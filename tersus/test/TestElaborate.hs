module TestElaborate (testElaborate, testElaborateMutant) where

import Data.List (isPrefixOf)
import Control.Exception (finally)
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory, removePathForcibly)
import System.FilePath ((</>))
import System.Posix.Process (getProcessID)

import Differential
import Hash (fingerprint)
import Native (cachedProgram)
import PreludeSource (elaboratePackageFiles)
import Seed (compilerSnapshotHash)
import TestData (typeCheckSources)
import TestHarness
import Utils

-- The elaborator written in Tersus (lib/elaborate) against the Haskell one (REPLACING_HASKELL.md); the compiler's own
-- packages are left to `frontend-diff compare` (Differential.suiteUnits)
testElaborate :: Test
testElaborate = TestList "testElaborate"
    [ TestCase "the elaborator agrees with the Haskell one over the corpus" agreement
    ]

-- Run only when named (TestTersus.optInGroups): it builds an elaborator of its own
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

-- The elaborator agrees with the Haskell one, with no "not modelled" answer, over the corpus without the compiler's own
-- packages, the programs of testTypeCheck, and small packages whose module tries the edges of predeclaration and of its
-- interface
agreement :: IO TestResult
agreement = withElaborator "elaborate" elaboratePackageFiles $ \exe scratch -> do
        corpus <- suiteUnits
        edges <- mapM (edgePackage scratch) (zip [1 :: Int ..] edgeModules)
        let control = scratch </> "mismatch.tersus"
            units = corpus ++ [SourceText name source | (name, source) <- typeCheckSources] ++ edges ++ [SourceFile control]
        writeFile control mismatch
        results <- runDifferential (executableCandidate exe) units
        let (agree, wording, disagree, unmodelled, failed) = tally [o | (_, _, o) <- results]
        putStrLn ("elaborate: " ++ show (length units) ++ " units, " ++ show agree ++ " agree, " ++ show wording ++ " wording, " ++ show disagree ++ " disagree, " ++ show unmodelled ++ " not modelled, " ++ show failed ++ " failed")
        pure $ case [(unit, modu, o) | (unit, modu, o) <- results, o /= Agree] of
            [] | [o | (SourceFile path, _, o) <- results, path == control] /= [Agree] -> Just "the program the mutant is tried on does not agree"
            [] | agree > 0 -> Nothing
            [] -> Just "no request agrees"
            (unit, modu, o) : _ -> Just (show unit ++ " " ++ modu ++ ": " ++ show o)

edgePackage :: FilePath -> (Int, String) -> IO Unit
edgePackage scratch (i, source) = do
    let root = scratch </> ("edge" ++ show i)
    createDirectoryIfMissing True (root </> "app")
    createDirectoryIfMissing True (root </> "parts")
    writeFile (root </> "package.tersus") ""
    writeFile (root </> "parts" </> "parts.tersus") source
    writeFile (root </> "app" </> "main.tersus") ("import edge" ++ show i ++ "::parts;\nreturn 0;\n")
    pure (FilePackage (root </> "app" </> "main.tersus"))

-- A module that exports a function with bounds, one whose types hold each other by value, one with a struct and a
-- variant of one name, and one whose function names a type declared after it
edgeModules :: [String]
edgeModules =
    [ "trait Sz { fn sz(self: &Self) -> Int; };\nfn f<T: Sz>(x: &T) -> Int { return Sz::sz(x); };\n"
    , "struct A { b: B };\nstruct B { a: A };\n"
    , "struct A { x: Int };\nenum E { A { y: Int }, B { z: Int } };\n"
    , "fn f(p: P) -> Int { return p.v; };\nstruct P { v: Int };\n"
    ]

-- A program the Haskell elaborator refuses because a condition is an Int
mismatch :: String
mismatch = "x = 1;\nif x { x = 2; };\nreturn x;\n"

-- Unification is the rule every type rests on: an elaborator whose unify lets Int and Bool stand for each other
-- accepts a program the Haskell one refuses, and the differential says so
unificationMutant :: IO TestResult
unificationMutant = case mutate elaboratePackageFiles of
    Nothing -> pure (Just "the mutation does not apply to lib/elaborate/state.tersus")
    Just files -> withElaborator "elaborate-mutant" files $ \exe scratch -> do
        let program = scratch </> "mismatch.tersus"
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
