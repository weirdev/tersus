-- The differential harness (REPLACING_HASKELL.md): another elaborator answering the requests the compiler makes over
-- the corpus, compared request by request with the compiler's frontend (ElaboratorTool.sourceLoader, and
-- sourceElaborator for a program given as statements).
module Differential
    ( Unit (..)
    , Outcome (..)
    , Asked (..)
    , Answers
    , Candidate
    , Frontend (..)
    , compilerFrontend
    , bootstrapFrontend
    , askFrontend
    , answersOf
    , compareAnswers
    , corpusUnits
    , suiteUnits
    , toolPackages
    , unitRequests
    , unitThrough
    , compareResponses
    , throughText
    , executableCandidate
    , buildElaborator
    , runDifferential
    , tally
    ) where

import Control.Exception (SomeException, evaluate, try)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List (isPrefixOf, isSuffixOf, sort)
import System.Directory (listDirectory)
import System.IO.Unsafe (unsafePerformIO)

import AstData (writeElaborated)
import Bootstrap (llvmOfOwned)
import Compile (lowerSourceUsing, lowerStatementsWith, parseWithEqualityUsing)
import ElaborateRequest
import ElaboratorTool (Loader, bootstrapElaborator, bootstrapLoader, noVerdict, runElaborator, runLoader, sourceElaborator, sourceLoader)
import InterfaceData (writeInterface)
import LibPackage (compileLibPackageWith, libPackage)
import MirHousekeeping (validationEntry)
import Native (buildExecutable)
import Pipeline (compileModulesBootstrap, ownedModuleProgram)
import qualified Modules as Mod
import qualified PackageCompile as Package
import PreludeSource (elaboratePackageFiles, toolPackageFiles, validationPackageFiles)
import Utils

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

-- What the compiler asks: a module given as statements, or a load (a program, a package, the libraries)
data Asked = AskedModule Request | AskedLoad LoadRequest
    deriving (Show, Eq)

-- The elaborations an answer carries, each with the module it is of (a refused load is one refusal)
type Answers = [(String, Response)]

type Candidate = Asked -> IO (Result Answers String)

-- The elaborator the compiler asks, for both kinds of request
data Frontend = Frontend Elaborator Loader

compilerFrontend :: Frontend
compilerFrontend = Frontend sourceElaborator sourceLoader

bootstrapFrontend :: Frontend
bootstrapFrontend = Frontend bootstrapElaborator bootstrapLoader

askFrontend :: Frontend -> Asked -> Answers
askFrontend (Frontend elaborator _) (AskedModule rq) = [(Mod.renderModuleId (rqModule rq), elaborator rq)]
askFrontend (Frontend _ loader) (AskedLoad rq) = answersOf (loader rq)

answersOf :: LoadResponse -> Answers
answersOf response = case response of
    LoadedProgram r -> [("program", r)]
    LoadedModules ms -> [(Mod.renderModuleId m, r) | (m, _, r) <- ms]
    LoadedLibraries ls failure -> [(name, r) | LibraryAnswer name _ _ r <- ls] ++ [("libraries", Refused e) | Just e <- [failure]]
    NotLoaded e -> [("load", Refused e)]
    Unparsed e -> [("parse", Refused e)]
    other -> [("load", Unresolved ("not an elaboration: " ++ take 200 (show other)))]

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

-- The requests the compiler makes compiling a unit, in the order it makes them, with the given frontend's answers, none of
-- which may be a failure of the elaborator as a tool or a program it does not handle
unitRequests :: Frontend -> Unit -> IO (Result [(Asked, Answers)] String)
unitRequests frontend unit = do
    ref <- newIORef []
    outcome <- unitThrough False (recording frontend ref) unit
    forced <- try (evaluate (either id (const "") (resultEither outcome)) >>= evaluate . length)
    requests <- reverse <$> readIORef ref
    pure $ case (forced :: Either SomeException Int, outcome) of
        (Left e, _) -> Error (show e)
        (_, Error e) | null requests -> Error e
        _ -> case [r | (_, answers) <- requests, (_, r) <- answers, noAnswer r] of
            r : _ -> Error ("the reference elaborator gave no answer: " ++ show r)
            [] -> Ok requests
  where
    resultEither r = case r of
        Ok a -> Right a
        Error e -> Left e

-- The compiler's compilation of a unit as far as lowering, through the given frontend, made anew each time the action
-- runs; deep, the length of what it lowered to, which forces all of it
unitThrough :: Bool -> Frontend -> Unit -> IO (Result Int String)
unitThrough deep (Frontend elaborator loader) given = pure given >>= \unit -> case unit of
    SourceFile path -> program <$> readFile path
    SourceText _ source -> pure $ case parseWithEqualityUsing loader source of
        Left e -> Error ("does not parse: " ++ e)
        Right stmts -> measured (lowerStatementsWith elaborator stmts)
    EmbeddedPackage entry -> pure (package (embeddedFiles entry) entry)
    FilePackage entry -> do
        files <- Mod.snapshotFromFilesystem entry
        pure (package files entry)
    Libraries -> pure (measured (compileLibPackageWith loader))
  where
    program source = measured (lowerSourceUsing loader False True source)
    package files entry = measured (Package.compileModulesUsing loader libPackage (Mod.Snapshot (Mod.resolverFromFiles files) entry False))
    measured r = mapResult (\lowered -> if deep then length (show lowered) else 0) r
    embeddedFiles entry
        | entry == validationEntry = validationPackageFiles
        | "lib/elaborate/" `isPrefixOf` entry = elaboratePackageFiles
        | otherwise = toolPackageFiles

-- The frontend, with each request and its answers kept (in reverse order). The compiler takes each response apart as
-- soon as it has it, so a request is kept when it is made.
recording :: Frontend -> IORef [(Asked, Answers)] -> Frontend
recording frontend ref = Frontend (\rq -> snd (head (keep (AskedModule rq) (askFrontend frontend (AskedModule rq))))) loader
  where
    Frontend _ given = frontend
    loader rq = keepLoad rq (given rq)
    {-# NOINLINE keep #-}
    keep asked answers = unsafePerformIO (modifyIORef' ref ((asked, answers) :) >> pure answers)
    {-# NOINLINE keepLoad #-}
    keepLoad rq response = unsafePerformIO (modifyIORef' ref ((AskedLoad rq, answersOf response) :) >> pure response)

-- The answers of two frontends to one request, module by module
compareAnswers :: Answers -> Answers -> Outcome
compareAnswers reference candidate
    | map fst reference /= map fst candidate = case [o | (_, NotModelled what) <- candidate, let o = NotModelledBy what] of
        o : _ -> o
        [] -> Disagree ("the modules answered differ: " ++ unwords (map fst reference) ++ " / " ++ unwords (map fst candidate))
    | otherwise = case [o | ((_, a), (_, b)) <- zip reference candidate, let o = compareResponses a b, o /= Agree] of
        o : _ -> o
        [] -> Agree

compareResponses :: Response -> Response -> Outcome
compareResponses reference candidate = case (reference, candidate) of
    (_, NotModelled what) -> NotModelledBy what
    (Accepted e i ls, Accepted e' i' ls')
        | e /= e' -> Disagree ("elaborations differ" ++ firstDifference (writeElaborated e) (writeElaborated e'))
        | i /= i' -> Disagree ("interfaces differ" ++ firstDifference (maybeText i) (maybeText i'))
        | ls /= ls' -> Disagree ("selected libraries differ: " ++ unwords ls ++ " / " ++ unwords ls')
        | otherwise -> Agree
    (Refused m, Refused m') -> if m == m' then Agree else Wording m m'
    (RefusedInterface m, RefusedInterface m') -> if m == m' then Agree else Wording m m'
    (Unresolved m, Unresolved m') -> if m == m' then Agree else Wording m m'
    _ -> Disagree ("verdicts differ: " ++ verdict reference ++ " / " ++ verdict candidate)
  where
    maybeText = maybe (Ok "none") writeInterface
    verdict r = case r of
        Accepted _ _ _ -> "accepted"
        Refused m -> "refused: " ++ m
        Unresolved m -> "unresolved: " ++ m
        RefusedInterface m -> "interface refused: " ++ m
        NotModelled m -> "not modelled: " ++ m
    firstDifference (Ok a) (Ok b) = case [(n, x, y) | (n, x, y) <- zip3 [1 :: Int ..] (lines a ++ repeat "") (lines b ++ repeat ""), x /= y] of
        (n, x, y) : _ -> " at record " ++ show n ++ ": " ++ take 120 x ++ " / " ++ take 120 y
        [] -> ""
    firstDifference _ _ = ""

-- The compiler's frontend behind a second trip through the text protocol: what a request and a response lose shows up
-- as a disagreement (a load's response is read from text whenever it is asked)
throughText :: Candidate
throughText asked = pure $ case asked of
    AskedModule rq ->
        writeRequest rq `bindResult` \text ->
            readRequest text `bindResult` \rq' ->
                if rq' /= rq
                    then Error "the request does not read back as written"
                    else writeResponse (sourceElaborator rq') `bindResult` readResponse `bindResult` \response -> Ok [(Mod.renderModuleId (rqModule rq), response)]
    AskedLoad rq -> Ok (answersOf (sourceLoader rq))

-- The elaborator of lib/elaborate in the given package files, built unvalidated as the host builds its own tools
buildElaborator :: [(FilePath, String)] -> FilePath -> IO (Result () String)
buildElaborator files out = case Mod.loadFromEntry (Mod.resolverFromFiles files) "lib/elaborate/elaborate.tersus" of
    Left e -> pure (Error e)
    Right (Mod.PackageResult pkg) -> case compileModulesBootstrap (Mod.packageSnapshot pkg) `bindResult` ownedModuleProgram of
        Error e -> pure (Error e)
        Ok owned -> llvmOfOwned owned >>= \ir -> case ir of
            Error e -> pure (Error e)
            Ok text -> buildExecutable out text
    Right _ -> pure (Error "lib/elaborate is not a package")

-- An elaborator executable: the request on its standard input, the response on its standard output
executableCandidate :: FilePath -> Candidate
executableCandidate exe asked = case asked of
    AskedModule rq -> mapResult (\r -> [(Mod.renderModuleId (rqModule rq), r)]) <$> runElaborator exe rq
    AskedLoad rq -> mapResult answersOf <$> runLoader exe rq

-- Each request of each unit, with the module it elaborates and how the candidate's response compares
runDifferential :: Candidate -> [Unit] -> IO [(Unit, String, Outcome)]
runDifferential candidate units = concat <$> mapM one units
  where
    one unit = do
        requests <- unitRequests compilerFrontend unit
        case requests of
            Error e -> pure [(unit, "", CandidateFailed ("the compiler made no requests: " ++ e)) | not (notParsed e)]
            Ok answered -> mapM (compareOne unit) answered
    notParsed e = take 15 e == "does not parse:"
    compareOne unit (asked, reference) = do
        answer <- candidate asked
        let outcome = case answer of
                Error e -> CandidateFailed e
                Ok answers -> compareAnswers reference answers
        pure (unit, label asked, outcome)
    label asked = case asked of
        AskedModule rq -> Mod.renderModuleId (rqModule rq)
        AskedLoad rq -> show (lrKind rq)

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

noAnswer :: Response -> Bool
noAnswer response = case response of
    Refused message -> noVerdict message
    RefusedInterface message -> noVerdict message
    NotModelled _ -> True
    Unresolved _ -> False
    Accepted _ _ _ -> False
