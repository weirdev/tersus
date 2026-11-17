{-# LANGUAGE TemplateHaskell #-}
module EmitterProvenance (approvedEmitterBuild, emitterBuildDescription, emitterBuildInputs, constructionIdentity, matchesConstruction, workingSourcesMatch, checkEmitterOutputs) where

import Control.Exception (IOException, evaluate, try)
import Data.Char (isHexDigit, toLower)
import Data.List (nub, sort, isSuffixOf)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as B
import Data.Version (showVersion)
import Language.Haskell.TH.Syntax (addDependentFile, lift, namePackage, runIO)
import qualified System.Directory as Directory
import qualified System.Environment as Environment
import qualified System.Process as Process
import qualified System.Posix.IO as Posix
import qualified Text.Parsec as Parsec
import System.FilePath ((</>), takeDirectory, takeFileName)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Exit (ExitCode (..))
import Utils

approvedEmitterBuild :: Maybe String
approvedEmitterBuild = $(do
    identity <- runIO (Environment.lookupEnv "TERSUS_TEST_APPROVED_BUILD_IDENTITY")
    manifest <- runIO (Environment.lookupEnv "TERSUS_EMITTER_BUILD_MANIFEST")
    case (identity, manifest) of
        (Just digest, Just path) | length digest == 64 && all isHexDigit digest -> do
            observed <- runIO (try (Process.readProcessWithExitCode "sha256sum" [path] "") :: IO (Either IOException (ExitCode, String, String)))
            case observed of
                Right (ExitSuccess, output, _) | takeWhile (/= ' ') output == map toLower digest ->
                    addDependentFile path >> lift (Just (map toLower digest))
                _ -> lift (Nothing :: Maybe String)
        _ -> lift (Nothing :: Maybe String))

emitterBuildDescription :: [String]
emitterBuildDescription = [compilerName, showVersion compilerVersion, os, arch,
    $(lift (show (map namePackage ['id, 'Map.fromList, 'B.pack, 'Directory.getXdgDirectory,
        'Process.readProcessWithExitCode, 'Posix.openFd, 'Parsec.parse, 'lift])))]

emitterBuildInputs :: [String]
emitterBuildInputs = maybe [] (\build -> build : emitterBuildDescription) approvedEmitterBuild

constructionIdentity :: [String] -> IO (Result (Maybe String) String)
constructionIdentity inputs = case approvedEmitterBuild of
    Nothing -> pure (Ok Nothing)
    Just build -> do
        result <- try (Process.readProcessWithExitCode "sha256sum" []
            (show ("tersus-published-full-emitter 1", build, emitterBuildDescription, inputs))) :: IO (Either IOException (ExitCode, String, String))
        pure $ case result of
            Right (ExitSuccess, output, _) | let digest = takeWhile (/= ' ') output,
                length digest == 64 && all isHexDigit digest -> Ok (Just digest)
            _ -> Error "could not hash the full emitter construction"

matchesConstruction :: Result (Maybe String) String -> String -> Bool
matchesConstruction (Ok (Just actual)) expected = length expected == 64 && all isHexDigit expected && actual == expected
matchesConstruction _ _ = False

-- Installed binaries use their captured source. In a source checkout, the
-- current files and module listings must still match that captured input.
workingSourcesMatch :: [(FilePath, String)] -> IO Bool
workingSourcesMatch captured = do
    package <- sourceTreePresent "."
    repository <- sourceTreePresent "tersus"
    case (package, repository) of
        (False, False) -> pure True
        _ -> do
            let root = if package then "." else "tersus"
            observed <- try (compareSources root) :: IO (Either IOException Bool)
            pure (either (const False) id observed)
  where
    sourceTreePresent root = do
        anchors <- mapM (Directory.doesFileExist . (root </>))
            ["package.yaml", "tersus.cabal", "lib/mir/package.tersus", "lib/elaborate/package.tersus"]
        source <- Directory.doesDirectoryExist (root </> "src")
        pure (source || or anchors)
    files = Map.toAscList (Map.fromList captured)
    compareSources root = do
        same <- mapM (\(path, expected) -> do
            actual <- readFile (root </> path)
            _ <- evaluate (length actual)
            pure (actual == expected)) files
        listings <- mapM (sameListing root) (Map.toAscList (Map.fromListWith (++)
            [(takeDirectory path, [takeFileName path]) | (path, _) <- files,
                any (`isSuffixOf` path) [".hs", ".hsc", ".hs-boot", ".tersus"]]))
        pure (and same && and listings)
    sameListing root (directory, expected) = do
        actual <- Directory.listDirectory (root </> directory)
        let hasHaskell = any (\name -> any (`isSuffixOf` name) [".hs", ".hsc", ".hs-boot"]) expected
            relevant name = any (`isSuffixOf` name) (if hasHaskell then [".hs", ".hsc", ".hs-boot"] else [".tersus"])
        -- The root lib files are selected individually by the compiler library
        -- authority, not all executable examples beside them.
        pure (directory == "lib" || sort (filter relevant actual) == sort expected)

checkEmitterOutputs :: [FilePath] -> [FilePath] -> IO (Result () String)
checkEmitterOutputs inputs outputs = do
    paths <- try (do
        protected <- mapM Directory.canonicalizePath inputs
        destinations <- mapM Directory.canonicalizePath outputs
        pure (protected, destinations)) :: IO (Either IOException ([FilePath], [FilePath]))
    pure $ case paths of
        Left e -> Error ("could not resolve emitter output paths: " ++ show e)
        Right (protected, destinations)
            | length (nub destinations) /= length destinations -> Error "emitter output and construction association must be distinct"
            | any (`elem` protected) destinations -> Error "emitter output aliases a source, pin or seed input"
            | otherwise -> Ok ()
