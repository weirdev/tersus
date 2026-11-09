module TestElaborate (testElaborate, testElaborateMutant) where

import Data.List (isInfixOf, isPrefixOf)
import Control.Exception (finally)
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory, removePathForcibly)
import System.FilePath (takeDirectory, (</>))
import System.Posix.Process (getProcessID)

import Differential
import ElaborateRequest (Response (..))
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
        scope <- scopeAgreement exe scratch
        pure $ scope <> case [(unit, modu, o) | (unit, modu, o) <- results, o /= Agree] of
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

scopeAgreement :: FilePath -> FilePath -> IO TestResult
scopeAgreement exe scratch = do
    failures <- mapM one (zip [1 :: Int ..] scopeCases)
    pure (foldr (<>) Nothing failures)
  where
    one (i, (label, source, api, extras, expected)) = do
        let root = scratch </> ("scope" ++ show i)
            entry = root </> "app/main.tersus"
            files = [("app/package.tersus", "noPrelude = true;"), ("app/main.tersus", source), ("vendor/package.tersus", "noPrelude = true;"), ("vendor/api/api.tersus", api)] ++ extras
        mapM_ (\(path, text) -> createDirectoryIfMissing True (takeDirectory (root </> path)) >> writeFile (root </> path) text) files
        reference <- unitRequests (FilePackage entry)
        results <- runDifferential (executableCandidate exe) [FilePackage entry]
        let outcomes = [outcome | (_, _, outcome) <- results]
            okay = not (null outcomes) && all supported outcomes
            supported outcome = case (expected, outcome) of
                (_, Agree) -> True
                ("refused", Wording _ _) -> True
                (reason, NotModelledBy what) -> reason == what
                _ -> False
            referenceVerdict = case reference of
                Ok answered -> case reverse answered of
                    (_, Refused _) : _ -> expected == "refused"
                    (_, Accepted _ _) : _ -> expected /= "refused"
                    _ -> False
                Error _ -> False
            exercised = referenceVerdict && (expected == "refused" || expected == "agree" || NotModelledBy expected `elem` outcomes)
        putStrLn ("defining scope " ++ label ++ ": " ++ show outcomes)
        pure (if okay && exercised then Nothing else Just (label ++ ": " ++ show outcomes))

scopeCases :: [(String, String, String, [(FilePath, String)], String)]
scopeCases =
    [ ("ordinary bounded export/import", "import vendor::api { value }; return value(1);", marker ++ "impl Mark for Int { }; fn value<T: Mark>(x: T) -> T { return x; };", [], "agree")
    , ("caller-only trait refusal", "import vendor::api { value }; trait Read { fn read(self: &Self) -> Int; }; impl Read for Int { fn read(self: &Self) -> Int { return 1; }; }; return value(1);", marker ++ "impl Mark for Int { }; fn value<T: Mark>(x: T) -> Int { return x.read(); };", [], "refused")
    , ("no-prelude provider cannot inherit caller Hash", "import vendor::api { Mark, value }; struct Local { }; impl Mark for Local { }; impl Hash for Local { fn hash(self: &Self) -> Int [{ }] [{ affirm return = 1; }] { return 1; }; }; p = Local { }; return value(p);", marker ++ "fn value<T: Mark>(x: &T) -> Int { return Hash::hash(x); };", [("app/package.tersus", "")], "refused")
    , ("caller-only function refusal", "import vendor::api { value }; fn secret(x: Int) -> Int { return x; }; return value(1);", marker ++ "impl Mark for Int { }; fn value<T: Mark>(x: T) -> Int { return secret(1); };", [], "refused")
    , ("caller-owned known trait implementation", "import vendor::api { Mark, value }; struct Local { n: Int }; impl Mark for Local { fn marked(self: &Self) -> Int { return self.n; }; }; p = Local { n: 42 }; return value(p);", "trait Mark { fn marked(self: &Self) -> Int; }; fn value<T: Mark>(x: &T) -> Int { return Mark::marked(x); };", [], "agree")
    , ("defining inherent method", "import vendor::api { B, Mark, value }; struct Local { }; impl Mark for Local { }; p = Local { }; b = B { v: 42 }; return value(p, b);", marker ++ "struct B { v: Int }; impl B { fn get(self: &Self) -> Int { return self.v; }; }; fn value<T: Mark>(x: T, b: &B) -> Int { return b.get(); };", [], "agree")
    , ("caller-only inherent refusal", "import vendor::api { Mark, value }; struct Local { }; impl Mark for Local { }; impl Local { fn get(self: &Self) -> Int { return 1; }; }; p = Local { }; return value(p);", marker ++ "fn value<T: Mark>(x: &T) -> Int { return x.get(); };", [], "refused")
    , ("bounded writes retain signature metadata", "import vendor::api { Pair, value }; p = Pair<Int> { x: 1, y: 2 }; value(&mut p, 42); return p.x;", marker ++ "impl Mark for Int { }; struct Pair<T> { x: T, y: T }; fn value<T: Mark>(p: &mut Pair<T>, x: T) -> Int writes(p.x) [{ }] [{ }] { (*p).x = x; return 0; };", [], "agree")
    , ("bounded caller implementation with required companion", callerRead "42", reading, [], "agree")
    , ("bad bounded caller contract retains its required companion", callerRead "-1", reading, [], "agree")
    , ("caller implementation private prerequisites", "import vendor::api { Mark, value }; trait Good { fn good(self: &Self) -> Int; }; impl Good for Int { fn good(self: &Self) -> Int { return 42; }; }; struct Wrap<T> { value: T }; impl<U: Good> Mark for Wrap<U> { fn marked(self: &Self) -> Int { return self.value.good(); }; }; p = Wrap<Int> { value: 1 }; return value(p);", "trait Mark { fn marked(self: &Self) -> Int; }; fn value<T: Mark>(x: &T) -> Int { return Mark::marked(x); };", [], "a caller implementation with private bound prerequisites")
    , ("private nested defining metadata", "import vendor::api { value }; return value(1);", "import vendor::helpers { pass }; " ++ marker ++ "impl Mark for Int { }; fn value<T: Mark>(x: T) -> T { return pass(x); };", [("vendor/helpers/helpers.tersus", "trait Good { }; impl Good for Int { }; struct Hidden<T> { value: T }; fn pass<T: Good>(x: T) -> T { p = Hidden { value: x }; return p.value; };")], "an imported template with private defining dependency metadata")
    , ("private captured helper precedence", "import vendor::api { value }; fn pass(x: Bool) -> Bool { return x; }; return value(42);", "import vendor::helpers { pass }; " ++ marker ++ "impl Mark for Int { }; fn value<T: Mark>(x: T) -> Int { return pass(42); };", [("vendor/helpers/helpers.tersus", "fn pass(x: Int) -> Int { return x; };")], "agree")
    , ("parameter-dependent bounded size", "import vendor::api { value }; return value(1, #[1, 2, 3]);", "trait Feed<E> { }; impl Feed<Array<Int, 3>> for Int { }; fn value<T: Feed<Array<Int, n>>, n>(x: T, a: &Array<Int, n>) -> Int { return n; };", [], "an imported template with parameter-dependent trait arguments")
    ]
  where
    marker = "trait Mark { }; "
    reading = marker ++ "trait Read { fn read(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; fn value<U: Read>(x: &U) -> Int { return Read::read(x); };"
    callerRead result = "import vendor::api { Mark, Read, value }; struct Leaf { }; impl Mark for Leaf { }; struct Wrap<T> { value: T }; impl<T: Mark> Read for Wrap<T> { fn read(self: &Self) -> Int { return " ++ result ++ "; }; }; p = Wrap<Leaf> { value: Leaf { } }; return value(p);"


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
