module Seed
    ( seedHash
    , seedSha256
    , seedUrl
    , compilerSnapshotHash
    , stageZero
    , cachedSeed
    , parserSeedHash
    , parserSeedSha256
    , parserSeedUrl
    , cachedParserSeed
    , frontendSeedHash
    , frontendSeedSha256
    , frontendSeedUrl
    , cachedFrontendSeed
    , frontendSeedFile
    ) where

import Control.Exception (Exception, IOException, SomeException, evaluate, throwIO, try)
import Data.Char (isHexDigit)
import GHC.IO.Encoding (char8)
import System.Directory (doesFileExist, removeFile, renameFile)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (IOMode (..), hClose, hGetContents, hSetEncoding, openFile)
import System.Process (proc)

import CacheLock (openTempFileCloexec)
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import Native (buildExecutable, cachedProgram, cachedProgramIfPresent, cacheDirectory, parallelBuilds, readProcessOutput)
import PreludeSource (compilerSourceHash, frontendSeedSha256, libPackageFiles, mirPackageFiles, seedSha256, parserSeedSha256, stdlibSource)
import Utils

seedUrl :: String
seedUrl = assetUrl "emitter" seedSha256

parserSeedUrl :: String
parserSeedUrl = assetUrl "parser" parserSeedSha256

frontendSeedUrl :: String
frontendSeedUrl = assetUrl "frontend" frontendSeedSha256

assetUrl :: String -> String -> String
assetUrl name digest = "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 digest ++ "/" ++ name ++ ".ll"

seedHash :: String
seedHash = fingerprint [seedSha256, runtimeSource]

parserSeedHash :: String
parserSeedHash = fingerprint [parserSeedSha256, runtimeSource]

frontendSeedHash :: String
frontendSeedHash = fingerprint [frontendSeedSha256, runtimeSource]

compilerSnapshotHash :: String
compilerSnapshotHash = fingerprint ([seedHash, parserSeedHash, frontendSeedHash] ++ concatMap (\(path, contents) -> [path, contents]) (mirPackageFiles ++ libPackageFiles) ++ [stdlibSource, compilerSourceHash])

stageZero :: FilePath -> IO (Result () String)
stageZero = buildSeed "emitter" seedSha256 seedHash "TERSUS_SEED_FILE"

buildSeed :: String -> String -> String -> String -> FilePath -> IO (Result () String)
buildSeed name digest hash override output = do
    seed <- seedText name digest hash override
    case seed of
        Error e -> pure (Error e)
        Ok text -> buildExecutable output text

seedText :: String -> String -> String -> String -> IO (Result String String)
seedText name digest hash variable = do
    file <- seedFile name digest hash variable
    case file of
        Error e -> pure (Error e)
        Ok path -> readSeedText name path

-- The seed's IR file, verified against its pin: the override, the checkout's copy, or the one fetched into the cache
seedFile :: String -> String -> String -> String -> IO (Result FilePath String)
seedFile name digest hash variable = do
    override <- lookupEnv variable
    case override of
        Just path -> verified path
        Nothing -> do
            local <- firstExisting ["bootstrap" </> name ++ ".ll", "tersus" </> "bootstrap" </> name ++ ".ll"]
            case local of
                Just path -> verified path
                Nothing -> cachedFile
  where
    verified path = mapResult (const path) <$> verifyFile name digest path
    firstExisting [] = pure Nothing
    firstExisting (path : rest) = do
        present <- doesFileExist path
        if present then pure (Just path) else firstExisting rest
    cachedFile = do
        cache <- cacheDirectory
        case cache of
            Error e -> pure (Error e)
            Ok dir -> do
                let path = dir </> ((if name == "emitter" then "seed-" else name ++ "-seed-") ++ hash ++ ".ll")
                present <- doesFileExist path
                if present
                    then verified path
                    else do
                        fetched <- downloadSeed name digest variable dir path
                        case fetched of
                            Error e -> pure (Error e)
                            Ok () -> verified path

downloadSeed :: String -> String -> String -> FilePath -> FilePath -> IO (Result () String)
downloadSeed name digest variable dir path = do
    (partial, handle) <- openTempFileCloexec dir (name ++ ".ll.tmp")
    hClose handle
    let url = assetUrl name digest
    outcome <- try (readProcessOutput (proc "curl" ["-fsSL", "-o", partial, url]) "") :: IO (Either IOException (ExitCode, String, String))
    case outcome of
        Left e -> removeQuietly partial >> pure (Error ("Could not run curl to fetch the " ++ name ++ " bootstrap seed from " ++ url ++ ": " ++ show e ++ ". Install curl, or set " ++ variable ++ " to a seed file."))
        Right (ExitFailure _, _, err) -> removeQuietly partial >> pure (Error ("Could not fetch the " ++ name ++ " bootstrap seed from " ++ url ++ ": " ++ err ++ "Set " ++ variable ++ " to a seed file to work without a network."))
        Right (ExitSuccess, _, _) -> do
            verified <- verifyFile name digest partial
            case verified of
                Error e -> removeQuietly partial >> pure (Error e)
                Ok () -> renameFile partial path >> pure (Ok ())

readSeedText :: String -> FilePath -> IO (Result String String)
readSeedText name path = do
    read' <- try (readBytes path) :: IO (Either IOException String)
    pure $ case read' of
        Left e -> Error ("Could not read the " ++ name ++ " bootstrap seed " ++ path ++ ": " ++ show e)
        Right text -> Ok text
  where
    readBytes p = do
        handle <- openFile p ReadMode
        hSetEncoding handle char8
        contents <- hGetContents handle
        _ <- evaluate (length contents)
        hClose handle
        pure contents

verifyFile :: String -> String -> FilePath -> IO (Result () String)
verifyFile name digest path = do
    outcome <- try (readProcessOutput (proc "sha256sum" [path]) "") :: IO (Either IOException (ExitCode, String, String))
    bySum <- case outcome of
        Right (ExitSuccess, out, _) -> pure (Just out)
        _ -> do
            fallback <- try (readProcessOutput (proc "shasum" ["-a", "256", path]) "") :: IO (Either IOException (ExitCode, String, String))
            pure $ case fallback of
                Right (ExitSuccess, out, _) -> Just out
                _ -> Nothing
    pure $ case bySum of
        Nothing -> Error ("Could not run sha256sum or shasum to verify the " ++ name ++ " bootstrap seed " ++ path ++ ".")
        Just out
            | takeWhile (/= ' ') out == digest && length digest == 64 && all isHexDigit digest -> Ok ()
            | otherwise -> Error ("The " ++ name ++ " bootstrap seed " ++ path ++ " does not match bootstrap/" ++ name ++ ".sha256 (" ++ digest ++ "): got " ++ takeWhile (/= ' ') out ++ ". Refusing to build it.")

removeQuietly :: FilePath -> IO ()
removeQuietly path = do
    _ <- try (removeFile path) :: IO (Either IOException ())
    pure ()

cachedSeed :: IO (Result FilePath String)
cachedSeed = cachedProgram "seed" seedHash "the seed of the emitter written in Tersus" stageZero

-- (the emitter and elaborator seeds need nothing else and are needed soon after the first parse, so they are built beside
-- the parser seed, before the parse runs rather than while it runs)
cachedParserSeed :: IO (Result FilePath String)
cachedParserSeed = do
    present <- cachedProgramIfPresent "parser-seed" parserSeedHash
    case present of
        Ok (Just exe) -> pure (Ok exe)
        _ -> do
            -- (a refused parser seed fails what asked for it, so the builds beside it are stopped, not waited for)
            built <- try (parallelBuilds [buildParserSeed >>= stopOnRefusal, besides cachedSeed, besides cachedFrontendSeed])
            pure $ case built of
                Left (SeedRefused e) -> Error e
                Right results -> head results
  where
    buildParserSeed = cachedProgram "parser-seed" parserSeedHash "the pinned native parser seed" (buildSeed "parser" parserSeedSha256 parserSeedHash "TERSUS_PARSER_SEED_FILE")
    stopOnRefusal result = case result of
        Error e -> throwIO (SeedRefused e)
        ok -> pure ok
    -- (what goes wrong with them is reported when they are asked for themselves)
    besides build = (try build :: IO (Either SomeException (Result FilePath String))) >> pure (Error "unused")

newtype SeedRefused = SeedRefused String
    deriving Show

instance Exception SeedRefused

-- F0: the elaborator written in Tersus, built from the pinned seed IR (bootstrap/frontend.sha256)
cachedFrontendSeed :: IO (Result FilePath String)
cachedFrontendSeed = cachedProgram "frontend-seed" frontendSeedHash "the pinned elaborator seed" (buildSeed "frontend" frontendSeedSha256 frontendSeedHash "TERSUS_FRONTEND_SEED_FILE")

-- The IR F0 is built from
frontendSeedFile :: IO (Result FilePath String)
frontendSeedFile = seedFile "frontend" frontendSeedSha256 frontendSeedHash "TERSUS_FRONTEND_SEED_FILE"
