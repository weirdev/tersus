module TestElaborate (testElaborateMutant) where

import Data.List (isInfixOf, isPrefixOf)
import Control.Exception (finally)
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory, removePathForcibly)
import System.FilePath ((</>))
import System.Posix.Process (getProcessID)

import qualified Compile
import Differential
import Hash (fingerprint)
import Native (cachedProgram)
import PreludeSource (elaboratePackageFiles)
import Seed (compilerSnapshotHash)
import TestHarness
import Utils

-- Run only when named (TestScheduling.optInGroups): it builds an elaborator of its own
testElaborateMutant :: Test
testElaborateMutant = TestList "testElaborateMutant"
    [ TestCase "an elaborator that unifies Int and Bool is caught" unificationMutant
    ]

-- Runs a test on the elaborator of the given package files and a scratch directory of its own, removed after. The
-- elaborator is built once for those files and this compiler, and kept in the cache.
withElaborator :: String -> [(FilePath, String)] -> (FilePath -> FilePath -> IO TestResult) -> IO TestResult
withElaborator name files use = do
    temp <- getTemporaryDirectory
    pid <- getProcessID
    let dir = temp </> ("tersus-" ++ name ++ "-" ++ show pid)
        key = fingerprint (compilerSnapshotHash : concatMap (\(path, text) -> [path, text]) files)
    createDirectoryIfMissing True dir
    flip finally (removePathForcibly dir) $ do
        built <- cachedProgram ("test-" ++ name) key ("the elaborator written in Tersus (" ++ name ++ ")") (buildElaborator files)
        case built of
            Error e -> pure (Just (name ++ " does not build: " ++ e))
            Ok exe -> use exe dir

-- A program the elaborator refuses because a condition is an Int
mismatch :: String
mismatch = "x = 1;\nif x { x = 2; };\nreturn x;\n"

-- Unification is the rule every type rests on: an elaborator whose unify lets Int and Bool stand for each other
-- accepts a program the compiler's elaborator refuses, and the differential says so
unificationMutant :: IO TestResult
unificationMutant = case mutate elaboratePackageFiles of
    Nothing -> pure (Just "the mutation does not apply to lib/elaborate/state.tersus")
    Just files -> withElaborator "elaborate-mutant" files $ \exe scratch -> do
        let program = scratch </> "mismatch.tersus"
        writeFile program mismatch
        results <- runDifferential (executableCandidate exe) [SourceFile program]
        pure $ case (Compile.lowerSource True mismatch, [o | (_, _, o) <- results]) of
            (Ok _, _) -> Just "the compiler's elaborator accepts the control program"
            (Error e, _) | not ("condition of if: expected Bool, got Int" `isInfixOf` e) -> Just ("the control program is refused for another reason: " ++ e)
            (_, [Disagree _]) -> Nothing
            (_, outcomes) -> Just ("the mutant was not caught: " ++ show outcomes)
  where
    rule = "    if kx != ky {"
    mutant = "    if kx != ky && kx + ky != 2 {"
    mutate files = case break ((== "lib/elaborate/state.tersus") . fst) files of
        (before, (path, text) : after) -> case replaceOnce text of
            Just text' -> Just (before ++ (path, text') : after)
            Nothing -> Nothing
        _ -> Nothing
    replaceOnce text = go "" text
      where
        go _ [] = Nothing
        go acc rest@(c : cs)
            | rule `isPrefixOf` rest = Just (reverse acc ++ mutant ++ drop (length rule) rest)
            | otherwise = go (c : acc) cs
