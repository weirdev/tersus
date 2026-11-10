-- The compiler's elaborators: executables of the elaborator written in Tersus (lib/elaborate), each answering one
-- request (ElaborateRequest) on its standard input with the response on its standard output.
module ElaboratorTool
    ( runElaborator
    , nativeElaborator
    , frontendToolFailure
    , bootstrapElaborator
    , sourceElaborator
    , frontendSources
    , noVerdict
    ) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (IOException, evaluate, finally, try)
import qualified Data.ByteString.Char8 as B
import Data.List (isInfixOf, isPrefixOf)
import GHC.Clock (getMonotonicTime)
import System.Directory (createDirectoryIfMissing)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.IO (hClose, hPutStr, hSetBinaryMode, openTempFile)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (CreateProcess (..), StdStream (..), proc, waitForProcess, withCreateProcess)

import BuiltinTable (builtinTableText)
import ElaborateRequest
import {-# SOURCE #-} ElaboratorNative (frontendStage)
import Hash (fingerprint)
import MirLower (probeGenerics)
import Modules (ModuleId (..))
import Syntax (Elaborated (..), Statement (..))
import Native (raiseStack)
import PreludeSource (elaboratePackageFiles, frontendSeedSources)
import Seed (cachedFrontendSeed)
import Utils

runElaborator :: FilePath -> Request -> IO (Result Response String)
runElaborator exe rq = do
    reportDir <- lookupEnv "TERSUS_BOUNDS_ONLY_REPORT"
    case writeRequest rq of
        Error e -> pure (Error e)
        Ok text0 -> do
            let text = maybe text0 (const (markBoundsReport text0)) reportDir
            -- (the elaborator recurses over the nesting of expressions, deeper than a default stack allows for a deep one;
            -- the data is ASCII, so it is passed as bytes rather than through the locale's decoding of a String)
            start <- getMonotonicTime
            (code, out, err) <- withCreateProcess (proc "/bin/sh" ["-c", raiseStack, exe]){std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe} $
                \hin' hout' herr' ph -> case (hin', hout', herr') of
                    (Just hin, Just hout, Just herr) -> do
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
                    _ -> pure (ExitFailure 1, B.empty, B.pack "no pipes to the elaborator")
            let response = case code of
                    ExitSuccess -> readResponseBytes (B.lines out)
                    ExitFailure n -> Error ("exit " ++ show n ++ ": " ++ take 400 (B.unpack err))
            case reportDir of
                Nothing -> pure response
                Just dir -> do
                    elapsed <- subtract start <$> getMonotonicTime
                    boundsReport dir rq elapsed err response

-- Phase 0 spike (TERSUS_BOUNDS_ONLY_REPORT=<directory>): the elaborator checks each template the module defines against
-- its bounds and appends the generic bodies; their lowering is probed here, and both reports are written to the directory.
-- The response given back is the program without the appended bodies.
markBoundsReport :: String -> String
markBoundsReport = unlines . go . lines
  where
    go ("builtins" : rest) = "builtins boundsReport" : rest
    go (l : rest) = l : go rest
    go [] = []

boundsReport :: FilePath -> Request -> Double -> B.ByteString -> Result Response String -> IO (Result Response String)
boundsReport dir rq elapsed err response = do
    let findings = [B.unpack l | l <- B.lines err, B.pack "boundsReport | " `B.isPrefixOf` l]
        isMarker stmt = case stmt of
            ExternDef m -> m == "$stub" || "$generic " `isPrefixOf` m
            _ -> False
    (result, probed, probeSeconds) <- case response of
        Ok (Accepted (Elaborated stmts types) iface) | any isMarker stmts -> do
            let (mainStmts, tailStmts) = break isMarker stmts
                genericCount = sum [n | ExternDef m <- tailStmts, "$generic " `isPrefixOf` m, (w : _) <- [words (drop 9 m)], [(n, "")] <- [reads w]]
                (mainTypes, genericTypes) = splitAt (length types - genericCount) types
                lines' = probeGenerics (rqInterfaces rq) mainStmts tailStmts genericTypes
            probeStart <- getMonotonicTime
            _ <- evaluate (length (concat lines'))
            probeEnd <- getMonotonicTime
            pure (Ok (Accepted (Elaborated mainStmts mainTypes) iface), lines', probeEnd - probeStart)
        _ -> pure (response, [], 0)
    let ModuleId pkg modu = rqModule rq
        verdict = case response of
            Ok (Accepted _ _) -> "accepted"
            Ok (Refused e) -> "refused " ++ take 200 e
            Ok (RefusedInterface e) -> "interfaceRefused " ++ take 200 e
            Ok (NotModelled e) -> "unmodelled " ++ take 200 e
            Error e -> "error " ++ take 200 e
        header =
            [ "module " ++ pkg ++ maybe "" ("::" ++) modu ++ " | " ++ map (\c -> if c == '\n' then ' ' else c) verdict
            , "elaborateSeconds " ++ show elapsed
            , "probeSeconds " ++ show probeSeconds
            ]
    _ <- try (do
        createDirectoryIfMissing True dir
        (path, handle) <- openTempFile dir "report.txt"
        hPutStr handle (unlines (header ++ findings ++ probed))
        hClose handle
        pure path) :: IO (Either IOException FilePath)
    pure result

-- The executable as the compiler's elaborator. An answer it cannot give refuses the module, with a reason that says
-- the tool failed, rather than being taken for the program's fault or answered by another elaborator.
{-# NOINLINE nativeElaborator #-}
nativeElaborator :: FilePath -> Elaborator
nativeElaborator exe rq = unsafePerformIO (answered <$> runElaborator exe rq)

answered :: Result Response String -> Response
answered (Ok response) = response
answered (Error e) = Refused (toolFailurePrefix ++ e)

toolFailurePrefix :: String
toolFailurePrefix = "Elaborator tool failure: "

frontendToolFailure :: String -> Bool
frontendToolFailure = isInfixOf toolFailurePrefix

-- A refusal that says nothing about the program: the elaborator failed as a tool, or does not handle the program
noVerdict :: String -> Bool
noVerdict message = frontendToolFailure message || "does not handle this" `isInfixOf` message

-- The seed (F0) elaborates the compiler's own code: the host's programs, the compiler libraries and the List and Box
-- helper units, and the elaborator's later stages.
bootstrapElaborator :: Elaborator
bootstrapElaborator = withStage 0

-- The elaborator of the programs and modules the compiler is given: the seed while it was made from the elaborator's
-- sources as they are (testFrontendBootstrap requires that on master), otherwise the elaborator as it is now,
-- elaborated by the seed (stage 1, built once).
sourceElaborator :: Elaborator
sourceElaborator = withStage sourceStage

sourceStage :: Int
sourceStage = if frontendSources == Ok frontendSeedSources then 0 else 1

-- What the seed's behavior depends on besides its own IR: the elaborator's sources, the protocol, and the builtin
-- table every request carries
frontendSources :: Result String String
frontendSources = mapResult (\table -> fingerprint ([requestHeader, responseHeader, table] ++ concatMap (\(path, contents) -> [path, contents]) elaboratePackageFiles)) builtinTableText

-- (the stage is looked up in the cache for each request, as the cache directory can change within a process)
{-# NOINLINE withStage #-}
withStage :: Int -> Elaborator
withStage n rq = unsafePerformIO $ do
    exe <- if n <= 0 then cachedFrontendSeed else mapResult fst <$> frontendStage n
    case exe of
        Ok path -> runElaborator path rq >>= pure . answered
        Error e -> pure (Refused (toolFailurePrefix ++ e))
