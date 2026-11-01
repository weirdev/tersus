module Seed
    ( seedHash
    , seedSha256
    , seedUrl
    , emitterHash
    , stageZero
    , cachedSeed
    ) where

import Control.Exception (IOException, evaluate, try)
import Data.Char (isHexDigit)
import GHC.IO.Encoding (char8)
import System.Directory (doesFileExist, removeFile, renameFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (IOMode (..), hClose, hGetContents, hSetEncoding, openFile, openTempFile)
import System.Process (readProcessWithExitCode)

import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import Native (buildExecutable, cachedProgram, cacheDirectory)
import PreludeSource (emitterSource, listsSource, preludeSource, seedSha256, stringSource)
import Utils

-- The seed the emitter written in Tersus is bootstrapped from (see Bootstrap): its text is fetched, or read from where it is kept, and
-- checked against the digest the repository pins, and stage 0 is it built with clang. This is below both Bootstrap and MirHousekeeping,
-- which each build programs written in Tersus from it.

-- The release the seed is fetched from: one release per seed, tagged for the seed it holds, so a release is never reused for a different seed
seedUrl :: String
seedUrl = "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 seedSha256 ++ "/emitter.ll"

-- What stage 0 is made of: the seed and the runtime it is linked with
seedHash :: String
seedHash = fingerprint [seedSha256, runtimeSource]

-- What stage 1 is made of: stage 0, the emitter, and the library every program has
emitterHash :: String
emitterHash = fingerprint [seedHash, emitterSource, preludeSource, listsSource, stringSource]

-- Stage 0: the seed built, at the path
stageZero :: FilePath -> IO (Result () String)
stageZero output = do
    seed <- seedText
    case seed of
        Error e -> pure (Error e)
        Ok text -> buildExecutable output text

seedText :: IO (Result String String)
seedText = do
    override <- lookupEnv "TERSUS_SEED_FILE"
    case override of
        Just path -> verifiedText path
        Nothing -> do
            local <- firstExisting ["bootstrap" </> "emitter.ll", "tersus" </> "bootstrap" </> "emitter.ll"]
            case local of
                Just path -> verifiedText path
                Nothing -> cachedText
  where
    firstExisting [] = pure Nothing
    firstExisting (path : rest) = do
        present <- doesFileExist path
        if present then pure (Just path) else firstExisting rest
    cachedText = do
        cache <- cacheDirectory
        case cache of
            Error e -> pure (Error e)
            Ok dir -> do
                let path = dir </> ("seed-" ++ seedHash ++ ".ll")
                present <- doesFileExist path
                if present
                    then verifiedText path
                    else do
                        fetched <- downloadSeed dir path
                        case fetched of
                            Error e -> pure (Error e)
                            Ok () -> verifiedText path

downloadSeed :: FilePath -> FilePath -> IO (Result () String)
downloadSeed dir path = do
    (partial, handle) <- openTempFile dir "seed.ll.tmp"
    hClose handle
    outcome <- try (readProcessWithExitCode "curl" ["-fsSL", "-o", partial, seedUrl] "") :: IO (Either IOException (ExitCode, String, String))
    case outcome of
        Left e -> removeQuietly partial >> pure (Error ("Could not run curl to fetch the bootstrap seed from " ++ seedUrl ++ ": " ++ show e ++ ". Install curl, or set TERSUS_SEED_FILE to a seed file."))
        Right (ExitFailure _, _, err) -> removeQuietly partial >> pure (Error ("Could not fetch the bootstrap seed from " ++ seedUrl ++ ": " ++ err ++ "Set TERSUS_SEED_FILE to a seed file to work without a network."))
        Right (ExitSuccess, _, _) -> do
            verified <- verifyFile partial
            case verified of
                Error e -> removeQuietly partial >> pure (Error e)
                Ok () -> renameFile partial path >> pure (Ok ())

verifiedText :: FilePath -> IO (Result String String)
verifiedText path = do
    verified <- verifyFile path
    case verified of
        Error e -> pure (Error e)
        Ok () -> do
            read' <- try (readBytes path) :: IO (Either IOException String)
            pure $ case read' of
                Left e -> Error ("Could not read the bootstrap seed " ++ path ++ ": " ++ show e)
                Right text -> Ok text
  where
    readBytes p = do
        handle <- openFile p ReadMode
        hSetEncoding handle char8
        contents <- hGetContents handle
        _ <- evaluate (length contents)
        hClose handle
        pure contents

verifyFile :: FilePath -> IO (Result () String)
verifyFile path = do
    outcome <- try (readProcessWithExitCode "sha256sum" [path] "") :: IO (Either IOException (ExitCode, String, String))
    bySum <- case outcome of
        Right (ExitSuccess, out, _) -> pure (Just out)
        _ -> do
            fallback <- try (readProcessWithExitCode "shasum" ["-a", "256", path] "") :: IO (Either IOException (ExitCode, String, String))
            pure $ case fallback of
                Right (ExitSuccess, out, _) -> Just out
                _ -> Nothing
    pure $ case bySum of
        Nothing -> Error ("Could not run sha256sum or shasum to verify the bootstrap seed " ++ path ++ ".")
        Just out
            | takeWhile (/= ' ') out == seedSha256 && length seedSha256 == 64 && all isHexDigit seedSha256 -> Ok ()
            | otherwise -> Error ("The bootstrap seed " ++ path ++ " does not match bootstrap/emitter.sha256 (" ++ seedSha256 ++ "): got " ++ takeWhile (/= ' ') out ++ ". Refusing to build it.")

removeQuietly :: FilePath -> IO ()
removeQuietly path = do
    _ <- try (removeFile path) :: IO (Either IOException ())
    pure ()

-- Stage 0 in the cache, built if it is not there yet
cachedSeed :: IO (Result FilePath String)
cachedSeed = cachedProgram "seed" seedHash "the seed of the emitter written in Tersus" stageZero

