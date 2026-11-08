module TestElaborate (testElaborate) where

import Data.List (isInfixOf, isPrefixOf)
import Control.Exception (finally)
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory, removePathForcibly)
import System.FilePath (takeDirectory, (</>))
import System.Posix.Process (getProcessID)

import Differential
import PreludeSource (elaboratePackageFiles)
import TestData (typeCheckSources)
import TestHarness
import Utils

-- The elaborator written in Tersus (lib/elaborate) against the Haskell one: it agrees on every request it handles,
-- and answers "not modelled" for the rest (REPLACING_HASKELL.md)
testElaborate :: Test
testElaborate = TestList "testElaborate"
    [ TestCase "the elaborator agrees with the Haskell one over the corpus" corpusAgreement
    , TestCase "an elaborator that unifies Int and Bool is caught" unificationMutant
    ]

-- Runs a test on the elaborator of the given package files, built in a directory of its own that is removed after
withElaborator :: String -> [(FilePath, String)] -> (FilePath -> IO TestResult) -> IO TestResult
withElaborator name files use = do
    temp <- getTemporaryDirectory
    pid <- getProcessID
    let dir = temp </> ("tersus-" ++ name ++ "-" ++ show pid)
        exe = dir </> name
    createDirectoryIfMissing True dir
    flip finally (removePathForcibly dir) $ do
        built <- buildElaborator files exe
        case built of
            Error e -> pure (Just (name ++ " does not build: " ++ e))
            Ok () -> use exe

corpusAgreement :: IO TestResult
corpusAgreement = withElaborator "elaborate" elaboratePackageFiles $ \exe -> do
        files <- filter singleFile <$> corpusUnits
        let control = takeDirectory exe </> "mismatch.tersus"
            units = files ++ [SourceText name source | (name, source) <- typeCheckSources] ++ [SourceFile control]
        writeFile control mismatch
        results <- runDifferential (executableCandidate exe) units
        let (agree, wording, disagree, unmodelled, failed) = tally [o | (_, _, o) <- results]
        putStrLn ("elaborate: " ++ show (length units) ++ " units, " ++ show agree ++ " agree, " ++ show wording ++ " wording, " ++ show disagree ++ " disagree, " ++ show unmodelled ++ " not modelled, " ++ show failed ++ " failed")
        pure $ case [(unit, modu, o) | (unit, modu, o) <- results, not (accepted o)] of
            [] | [o | (SourceFile path, _, o) <- results, path == control] /= [Agree] -> Just "the program the mutant is tried on does not agree"
            [] | agree > 0 -> Nothing
            [] -> Just "no request agrees"
            (unit, modu, o) : _ -> Just (show unit ++ " " ++ modu ++ ": " ++ show o)
  where
    -- (the modules of packages and of the compiler libraries are elaborated module by module, which is not built yet)
    singleFile unit = case unit of
        SourceFile _ -> True
        _ -> False
    -- (what the elaborator answers "not modelled" for is only what is not built yet)
    accepted o = case o of
        Agree -> True
        NotModelledBy what -> any (`isInfixOf` what) ["reference", "trait", "impl", "bounds", "clone", "Clone", "Deref", "Eq", "modules"]
        _ -> False

-- A program the Haskell elaborator refuses because a condition is an Int
mismatch :: String
mismatch = "x = 1;\nif x { x = 2; };\nreturn x;\n"

-- Unification is the rule every type rests on: an elaborator whose unify lets Int and Bool stand for each other
-- accepts a program the Haskell one refuses, and the differential says so
unificationMutant :: IO TestResult
unificationMutant = case mutate elaboratePackageFiles of
    Nothing -> pure (Just "the mutation does not apply to lib/elaborate/state.tersus")
    Just files -> withElaborator "elaborate-mutant" files $ \exe -> do
        let program = takeDirectory exe </> "mismatch.tersus"
        writeFile program mismatch
        results <- runDifferential (executableCandidate exe) [SourceFile program]
        pure $ case [o | (_, _, o) <- results] of
            [Disagree _] -> Nothing
            outcomes -> Just ("the mutant was not caught: " ++ show outcomes)
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
