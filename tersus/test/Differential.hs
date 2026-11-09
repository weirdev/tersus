-- The differential harness (REPLACING_HASKELL.md): an elaborator other than the Haskell one, answering the
-- requests the compiler makes over the corpus, compared request by request with `respond`. TestDifferential
-- runs it on in-process candidates; `stack run frontend-diff` runs it on an executable.
module Differential
    ( Unit (..)
    , Outcome (..)
    , Candidate
    , corpusUnits
    , suiteUnits
    , unitRequests
    , unitThrough
    , executableElaborator
    , compareResponses
    , throughText
    , executableCandidate
    , buildElaborator
    , runDifferential
    , tally
    ) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (IOException, SomeException, evaluate, finally, try)
import qualified Data.ByteString.Char8 as B
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import System.Exit (ExitCode (..))
import System.IO.Unsafe (unsafePerformIO)
import System.IO (hClose, hSetBinaryMode)
import System.Process (CreateProcess (..), StdStream (..), proc, waitForProcess, withCreateProcess)

import AstData (writeElaborated)
import Bootstrap (llvmOfOwned)
import Compile (lowerSourcePartsWith, lowerStatementsWith, parseWithEquality)
import ElaborateRequest
import InterfaceData (writeInterface)
import LibPackage (compileLibPackageWith, nativeStorageUnitsWith)
import MirHousekeeping (validationEntry)
import Native (buildExecutable)
import Pipeline (compileModulesBootstrap, ownedModuleProgram)
import qualified Modules as Mod
import qualified PackageCompile as Package
import PreludeSource (toolPackageFiles, validationPackageFiles)
import qualified TersusParser
import Utils
import ValidatorNative (raiseStack)

-- What the compiler elaborates: a program read from a file, a program a test checks as it is given (with a name:
-- no libraries in front of it, as Pipeline.validateStatements has it), a package (its modules in order), or the
-- compiler libraries
data Unit = SourceFile FilePath | SourceText String String | EmbeddedPackage FilePath | FilePackage FilePath | Libraries
    deriving (Show, Eq)

data Outcome
    = Agree
    | -- both refuse, at the same stage, in different words
      Wording String String
    | Disagree String
    | NotModelledBy String
    | CandidateFailed String
    deriving (Show, Eq)

type Candidate = Request -> IO (Result Response String)

corpusUnits :: IO [Unit]
corpusUnits = (++ map EmbeddedPackage toolPackages) <$> suiteUnits

-- The corpus without the compiler's own packages, whose Haskell elaboration alone takes most of the corpus's time
suiteUnits :: IO [Unit]
suiteUnits = do
    files <- concat <$> mapM tersusFiles ["examples", "examples/rejected"]
    pure (map SourceFile files ++ [FilePackage "examples/modules/app/main.tersus", Libraries])
  where
    tersusFiles dir = map ((dir ++ "/") ++) . filter (".tersus" `isSuffixOf`) . sort <$> listDirectory dir

toolPackages :: [FilePath]
toolPackages = ["lib/parser/parser.tersus", "lib/ast_reader/ast_reader.tersus", "lib/mir/emit/emit.tersus", "lib/mir/mir_verify/mir_verify.tersus", "lib/mir/mir_erase/mir_erase.tersus", validationEntry]

-- The requests the compiler makes compiling a unit, in the order it makes them, with `respond`'s answers. A unit
-- that does not parse makes none.
unitRequests :: Unit -> IO (Result [(Request, Response)] String)
unitRequests unit = do
    ref <- newIORef []
    outcome <- unitThrough False (recording ref) unit
    forced <- try (evaluate (either id (const "") (resultEither outcome)) >>= evaluate . length)
    requests <- reverse <$> readIORef ref
    pure $ case (forced :: Either SomeException Int, outcome) of
        (Left e, _) -> Error (show e)
        (_, Error e) | null requests -> Error e
        _ -> Ok requests
  where
    resultEither r = case r of
        Ok a -> Right a
        Error e -> Left e

-- The compiler's compilation of a unit as far as lowering, each module elaborated by the given elaborator, made anew each
-- time the action runs; deep, the length of what it lowered to, which forces all of it
unitThrough :: Bool -> Elaborator -> Unit -> IO (Result Int String)
unitThrough deep elaborator given = pure given >>= \unit -> case unit of
    SourceFile path -> program <$> readFile path
    SourceText _ source -> pure $ case parseWithEquality source of
        Left e -> Error ("does not parse: " ++ e)
        Right stmts -> measured (lowerStatementsWith elaborator stmts)
    EmbeddedPackage entry -> pure (package (if entry == validationEntry then validationPackageFiles else toolPackageFiles) entry)
    FilePackage entry -> do
        files <- Mod.snapshotFromFilesystem entry
        pure (package files entry)
    Libraries -> pure (measured (compileLibPackageWith elaborator) `bindResult` \a -> mapResult (+ a) (measured (nativeStorageUnitsWith elaborator)))
  where
    program source = case TersusParser.parseSourceParts True source of
        Error e -> Error ("does not parse: " ++ e)
        Ok parts -> measured (lowerSourcePartsWith elaborator True parts)
    package files entry = case Mod.loadFromEntry (Mod.resolverFromFiles files) entry of
        Left e -> Error e
        Right (Mod.PackageResult pkg) -> measured (Package.compileModulesWith elaborator pkg)
        Right _ -> Error (entry ++ " is not a package")
    measured r = mapResult (\lowered -> if deep then length (show lowered) else 0) r

-- `respond`, with each request and its answer kept (in reverse order). The compiler takes each response apart as
-- soon as it has it, so a request is kept when it is made.
{-# NOINLINE recording #-}
recording :: IORef [(Request, Response)] -> Elaborator
recording ref rq = unsafePerformIO $ do
    let response = respond rq
    modifyIORef' ref ((rq, response) :)
    pure response

compareResponses :: Response -> Response -> Outcome
compareResponses reference candidate = case (reference, candidate) of
    (_, NotModelled what) -> NotModelledBy what
    (Accepted e i, Accepted e' i')
        | e /= e' -> Disagree ("elaborations differ" ++ firstDifference (writeElaborated e) (writeElaborated e'))
        | i /= i' -> Disagree ("interfaces differ" ++ firstDifference (maybeText i) (maybeText i'))
        | otherwise -> Agree
    (Refused m, Refused m') -> if m == m' then Agree else Wording m m'
    (RefusedInterface m, RefusedInterface m') -> if m == m' then Agree else Wording m m'
    _ -> Disagree ("verdicts differ: " ++ verdict reference ++ " / " ++ verdict candidate)
  where
    maybeText = maybe (Ok "none") writeInterface
    verdict r = case r of
        Accepted _ _ -> "accepted"
        Refused m -> "refused: " ++ m
        RefusedInterface m -> "interface refused: " ++ m
        NotModelled m -> "not modelled: " ++ m
    firstDifference (Ok a) (Ok b) = case [(n, x, y) | (n, x, y) <- zip3 [1 :: Int ..] (lines a ++ repeat "") (lines b ++ repeat ""), x /= y] of
        (n, x, y) : _ -> " at record " ++ show n ++ ": " ++ take 120 x ++ " / " ++ take 120 y
        [] -> ""
    firstDifference _ _ = ""

-- The Haskell elaborator behind the text protocol: what a request and a response lose shows up as a disagreement
throughText :: Candidate
throughText rq = pure $
    writeRequest rq `bindResult` \text ->
        readRequest text `bindResult` \rq' ->
            if rq' /= rq
                then Error "the request does not read back as written"
                else writeResponse (respond rq') `bindResult` readResponse

-- The elaborator of lib/elaborate in the given package files, built unvalidated as the host builds its own tools
buildElaborator :: [(FilePath, String)] -> FilePath -> IO (Result () String)
buildElaborator files out = case Mod.loadFromEntry (Mod.resolverFromFiles files) "lib/elaborate/elaborate.tersus" of
    Left e -> pure (Error e)
    Right (Mod.PackageResult pkg) -> case compileModulesBootstrap pkg `bindResult` ownedModuleProgram of
        Error e -> pure (Error e)
        Ok owned -> llvmOfOwned owned >>= \ir -> case ir of
            Error e -> pure (Error e)
            Ok text -> buildExecutable out text
    Right _ -> pure (Error "lib/elaborate is not a package")

-- The elaborator executable as the compiler's elaborator: what it cannot answer is not modelled
{-# NOINLINE executableElaborator #-}
executableElaborator :: FilePath -> Elaborator
executableElaborator exe rq = unsafePerformIO $ do
    answer <- executableCandidate exe rq
    pure $ case answer of
        Ok response -> response
        Error e -> NotModelled e

-- An elaborator executable: the request on its standard input, the response on its standard output
executableCandidate :: FilePath -> Candidate
executableCandidate exe rq = case writeRequest rq of
    Error e -> pure (Error e)
    Ok text -> do
        -- (the elaborator recurses over the nesting of expressions, deeper than a default stack allows for a deep one;
        -- the data is ASCII, so it is passed as bytes rather than through the locale's decoding of a String)
        (code, out, err) <- withCreateProcess (proc "/bin/sh" ["-c", raiseStack, exe]){std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe} $
            \(Just hin) (Just hout) (Just herr) ph -> do
                mapM_ (`hSetBinaryMode` True) [hin, hout, herr]
                outVar <- newEmptyMVar
                errVar <- newEmptyMVar
                _ <- forkIO (B.hGetContents hout >>= putMVar outVar)
                _ <- forkIO (B.hGetContents herr >>= putMVar errVar)
                _ <- try (B.hPut hin (B.pack text) `finally` hClose hin) :: IO (Either IOException ())
                out <- takeMVar outVar
                err <- takeMVar errVar
                code <- waitForProcess ph
                pure (code, out, err)
        pure $ case code of
            ExitSuccess -> readResponseBytes (B.lines out)
            ExitFailure n -> Error ("exit " ++ show n ++ ": " ++ take 400 (B.unpack err))

-- Each request of each unit, with the module it elaborates and how the candidate's response compares
runDifferential :: Candidate -> [Unit] -> IO [(Unit, String, Outcome)]
runDifferential candidate units = concat <$> mapM one units
  where
    one unit = do
        requests <- unitRequests unit
        case requests of
            Error e -> pure [(unit, "", CandidateFailed ("the compiler made no requests: " ++ e)) | not (notParsed e)]
            Ok answered -> mapM (compareOne unit) answered
    notParsed e = take 15 e == "does not parse:"
    compareOne unit (rq, reference) = do
        answer <- candidate rq
        let outcome = case answer of
                Error e -> CandidateFailed e
                Ok response -> compareResponses reference response
        pure (unit, Mod.renderModuleId (rqModule rq), outcome)

-- Agreements, wording differences, disagreements, not modelled and candidate failures
tally :: [Outcome] -> (Int, Int, Int, Int, Int)
tally outcomes = (count isAgree, count isWording, count isDisagree, count isNotModelled, count isFailed)
  where
    count p = length (filter p outcomes)
    isAgree o = o == Agree
    isWording o = case o of Wording _ _ -> True; _ -> False
    isDisagree o = case o of Disagree _ -> True; _ -> False
    isNotModelled o = case o of NotModelledBy _ -> True; _ -> False
    isFailed o = case o of CandidateFailed _ -> True; _ -> False
