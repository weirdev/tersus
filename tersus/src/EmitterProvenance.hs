{-# LANGUAGE TemplateHaskell #-}
module EmitterProvenance (ordinaryBuildProfile, emitterBuildDescription, emitterBuildInputs, constructionIdentity, constructionIdentityFor, matchesConstruction, workingSourcesMatch, checkEmitterOutputs) where

import BuildOptions (describeBuildOptions)
import Control.Exception (IOException, evaluate, try)
import Data.Char (isHexDigit)
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
import PreludeSource (emitterSourceFiles)
import System.FilePath ((</>), takeDirectory, takeFileName)
import System.Info (arch, compilerName, compilerVersion, os)
import System.Exit (ExitCode (..))
import Utils

-- The options this library was actually compiled with, as the build itself
-- gives them: the command line GHC was given while it compiled this module
-- (BuildOptions). In an ordinary Cabal or Stack build that is the whole
-- invocation of the configured package -- what the package asks for, what
-- configuring it resolved, and what the build command adds on top of both --
-- and the library is compiled once, so the compiler and every tool built
-- from it describe the same build. An invocation that is not an ordinary
-- build of a configured package, or one that reads from somewhere this
-- cannot describe, leaves no profile, no association is believed, and the
-- emitter is made from source.
--
-- This is an observation, not an approval: the digest of a published emitter
-- is accepted only when this description, the packages GHC selected and the
-- working source are again the ones the association was written for
-- (MirHousekeeping.emitterIdentity).
ordinaryBuildProfile :: Maybe [String]
ordinaryBuildProfile = $(do
    root <- runIO Directory.getCurrentDirectory
    compiled <- runIO (takeFileName <$> Environment.getExecutablePath)
    arguments <- runIO Environment.getArgs
    -- (the directories the compiler captures the source of, whose content and
    -- listing workingSourcesMatch compares again: what a search path of one
    -- of them is bound by)
    let captured = nub [takeDirectory path | (path, _) <- emitterSourceFiles,
            any (`isSuffixOf` path) [".hs", ".hsc", ".hs-boot"], takeDirectory path /= "."]
    described <- runIO (describeBuildOptions root captured compiled arguments)
    case described of
        Nothing -> lift (Nothing :: Maybe [String])
        Just (profile, bound) -> mapM_ addDependentFile bound >> lift (Just profile))

emitterBuildDescription :: [String]
emitterBuildDescription = [compilerName, showVersion compilerVersion, os, arch,
    $(lift (show (map namePackage ['id, 'Map.fromList, 'B.pack, 'Directory.getXdgDirectory,
        'Process.readProcessWithExitCode, 'Posix.openFd, 'Parsec.parse, 'lift])))]

emitterBuildInputs :: [String]
emitterBuildInputs = maybe [] (++ emitterBuildDescription) ordinaryBuildProfile

constructionIdentity :: [String] -> IO (Result (Maybe String) String)
constructionIdentity = constructionIdentityFor ordinaryBuildProfile

-- (what a profile other than this build's decides, for the tests: a build with
-- no configured profile at all knows no association and makes the emitter from
-- source, and one made differently reaches a different association)
constructionIdentityFor :: Maybe [String] -> [String] -> IO (Result (Maybe String) String)
constructionIdentityFor profile inputs = case profile of
    Nothing -> pure (Ok Nothing)
    Just build -> do
        result <- try (Process.readProcessWithExitCode "sha256sum" []
            (show ("tersus-published-full-emitter 2", build, emitterBuildDescription, inputs))) :: IO (Either IOException (ExitCode, String, String))
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
