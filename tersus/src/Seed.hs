module Seed
    ( seedHash
    , seedSha256
    , seedUrl
    , emitterHash
    , stageZero
    , cachedSeed
    , parserSeedHash
    , parserSeedSha256
    , parserSeedUrl
    , cachedParserSeed
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
import PreludeSource (compilerSourceHash, libPackageFiles, mirPackageFiles, seedSha256, parserSeedSha256, stdlibSource)
import Utils

seedUrl :: String
seedUrl = assetUrl "emitter" seedSha256

parserSeedUrl :: String
parserSeedUrl = assetUrl "parser" parserSeedSha256

assetUrl :: String -> String -> String
assetUrl name digest = "https://github.com/weirdev/tersus/releases/download/bootstrap-" ++ take 12 digest ++ "/" ++ name ++ ".ll"

seedHash :: String
seedHash = fingerprint [seedSha256, runtimeSource]

parserSeedHash :: String
parserSeedHash = fingerprint [parserSeedSha256, runtimeSource]

emitterHash :: String
emitterHash = fingerprint ([seedHash, parserSeedHash] ++ concatMap (\(path, contents) -> [path, contents]) (mirPackageFiles ++ libPackageFiles) ++ [stdlibSource, compilerSourceHash])

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
    override <- lookupEnv variable
    case override of
        Just path -> verifiedText name digest path
        Nothing -> do
            local <- firstExisting ["bootstrap" </> name ++ ".ll", "tersus" </> "bootstrap" </> name ++ ".ll"]
            case local of
                Just path -> verifiedText name digest path
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
                let path = dir </> ((if name == "emitter" then "seed-" else "parser-seed-") ++ hash ++ ".ll")
                present <- doesFileExist path
                if present
                    then verifiedText name digest path
                    else do
                        fetched <- downloadSeed name digest variable dir path
                        case fetched of
                            Error e -> pure (Error e)
                            Ok () -> verifiedText name digest path

downloadSeed :: String -> String -> String -> FilePath -> FilePath -> IO (Result () String)
downloadSeed name digest variable dir path = do
    (partial, handle) <- openTempFile dir (name ++ ".ll.tmp")
    hClose handle
    let url = assetUrl name digest
    outcome <- try (readProcessWithExitCode "curl" ["-fsSL", "-o", partial, url] "") :: IO (Either IOException (ExitCode, String, String))
    case outcome of
        Left e -> removeQuietly partial >> pure (Error ("Could not run curl to fetch the " ++ name ++ " bootstrap seed from " ++ url ++ ": " ++ show e ++ ". Install curl, or set " ++ variable ++ " to a seed file."))
        Right (ExitFailure _, _, err) -> removeQuietly partial >> pure (Error ("Could not fetch the " ++ name ++ " bootstrap seed from " ++ url ++ ": " ++ err ++ "Set " ++ variable ++ " to a seed file to work without a network."))
        Right (ExitSuccess, _, _) -> do
            verified <- verifyFile name digest partial
            case verified of
                Error e -> removeQuietly partial >> pure (Error e)
                Ok () -> renameFile partial path >> pure (Ok ())

verifiedText :: String -> String -> FilePath -> IO (Result String String)
verifiedText name digest path = do
    verified <- verifyFile name digest path
    case verified of
        Error e -> pure (Error e)
        Ok () -> do
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
    outcome <- try (readProcessWithExitCode "sha256sum" [path] "") :: IO (Either IOException (ExitCode, String, String))
    bySum <- case outcome of
        Right (ExitSuccess, out, _) -> pure (Just out)
        _ -> do
            fallback <- try (readProcessWithExitCode "shasum" ["-a", "256", path] "") :: IO (Either IOException (ExitCode, String, String))
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

cachedParserSeed :: IO (Result FilePath String)
cachedParserSeed = cachedProgram "parser-seed" parserSeedHash "the pinned native parser seed" (buildSeed "parser" parserSeedSha256 parserSeedHash "TERSUS_PARSER_SEED_FILE")
