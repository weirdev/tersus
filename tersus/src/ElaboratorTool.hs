-- The compiler's elaborators: executables of the elaborator written in Tersus (lib/elaborate), each answering one
-- request (ElaborateRequest) on its standard input with the response on its standard output.
module ElaboratorTool
    ( runElaborator
    , runElaboratorText
    , runElaboratorRaw
    , nativeElaborator
    , frontendToolFailure
    , bootstrapElaborator
    , sourceElaborator
    , sourceElaboratorExecutable
    , frontendSources
    , noVerdict
    , Loader
    , runLoader
    , nativeLoader
    , bootstrapLoader
    , sourceLoader
    ) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Exception (IOException, finally, try)
import qualified Data.ByteString.Char8 as B
import Data.List (isInfixOf)
import System.Exit (ExitCode (..))
import System.IO (hClose, hSetBinaryMode)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (CreateProcess (..), StdStream (..), proc, waitForProcess, withCreateProcess)

import BuiltinTable (builtinTableText)
import ElaborateRequest
import {-# SOURCE #-} ElaboratorNative (frontendStage, productionTools)
import Hash (fingerprint)
import Native (raiseStack)
import PreludeSource (elaboratePackageFiles, frontendSeedSources)
import qualified ParserSeed
import Seed (cachedFrontendSeed, cachedParserSeed)
import Utils

runElaborator :: FilePath -> Request -> IO (Result Response String)
runElaborator exe rq = case writeRequest rq of
    Error e -> pure (Error e)
    Ok text -> runElaboratorText exe text

runElaboratorText :: FilePath -> String -> IO (Result Response String)
runElaboratorText exe text = (`bindResult` readResponseBytes) <$> runElaboratorRaw exe text

-- The executable on the request, and the lines of its response
runElaboratorRaw :: FilePath -> String -> IO (Result [B.ByteString] String)
runElaboratorRaw exe text = do
    -- (the elaborator recurses over the nesting of expressions, deeper than a default stack allows for a deep one;
    -- the data is ASCII, so it is passed as bytes rather than through the locale's decoding of a String)
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
    pure $ case code of
        ExitSuccess -> Ok (B.lines out)
        ExitFailure n -> Error ("exit " ++ show n ++ ": " ++ take 400 (B.unpack err))

type Loader = LoadRequest -> LoadResponse

runLoader :: FilePath -> LoadRequest -> IO (Result LoadResponse String)
runLoader exe rq = case writeLoadRequest rq of
    Error e -> pure (Error e)
    Ok text -> (`bindResult` readLoadResponseBytes (lrKind rq)) <$> runElaboratorRaw exe text

-- A load the executable cannot answer refuses it, with a reason that says the tool failed
{-# NOINLINE nativeLoader #-}
nativeLoader :: FilePath -> Loader
nativeLoader exe rq = unsafePerformIO (loaded <$> runLoader exe rq)

loaded :: Result LoadResponse String -> LoadResponse
loaded (Ok response) = response
loaded (Error e) = NotLoaded (toolFailurePrefix ++ e)

bootstrapLoader :: Loader
bootstrapLoader = withStageLoader 0

-- (a program or package it loads is checked and validated next, with the tools made beforehand, side by side; a tool
-- that fails refuses the load in its own words)
{-# NOINLINE sourceLoader #-}
sourceLoader :: Loader
sourceLoader rq
    | lrKind rq `elem` [LoadProgram, LoadPackage] = unsafePerformIO $ do
        ready <- sourceTools
        pure $ case ready of
            Error e -> NotLoaded e
            Ok () -> withStageLoader sourceStage rq
    | otherwise = withStageLoader sourceStage rq

{-# NOINLINE sourceToolsReady #-}
sourceToolsReady :: MVar Bool
sourceToolsReady = unsafePerformIO (newMVar False)

-- (once per process, and not kept when it fails)
sourceTools :: IO (Result () String)
sourceTools = modifyMVar sourceToolsReady $ \ready ->
    if ready then pure (True, Ok ()) else do
        reader <- cachedParserSeed
        made <- case reader of
            Error e -> pure (Error (ParserSeed.failure e))
            Ok _ -> productionTools
        pure (succeeded made, made)
  where
    succeeded (Ok ()) = True
    succeeded (Error _) = False

{-# NOINLINE withStageLoader #-}
withStageLoader :: Int -> Loader
withStageLoader n rq = unsafePerformIO $ do
    -- (a request carries the builtin table, which P0 reads from lib/stdlib.tersus)
    reader <- cachedParserSeed
    case reader of
        Error e -> pure (NotLoaded (ParserSeed.failure e))
        Ok _ -> do
            exe <- stageExecutable n
            case exe of
                Ok path -> loaded <$> runLoader path rq
                Error e -> pure (NotLoaded (toolFailurePrefix ++ e))

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
  where

-- (the stage is looked up in the cache for each request, as the cache directory can change within a process)
{-# NOINLINE withStage #-}
withStage :: Int -> Elaborator
withStage n rq = unsafePerformIO $ do
    exe <- stageExecutable n
    case exe of
        Ok path -> runElaborator path rq >>= pure . answered
        Error e -> pure (Refused (toolFailurePrefix ++ e))

stageExecutable :: Int -> IO (Result FilePath String)
stageExecutable n = if n <= 0 then cachedFrontendSeed else mapResult fst <$> frontendStage n

sourceElaboratorExecutable :: IO (Result FilePath String)
sourceElaboratorExecutable = stageExecutable sourceStage
