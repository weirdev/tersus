module TestLibModules (testLibModules) where

import Control.Exception (bracket, evaluate)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Compile
import qualified Modules
import qualified Parse
import PreludeSource (eqSource)
import qualified Mir as M
import MirValidate (validateProgram)
import PackageCompile (compileModulesValidated)
import Interface (ModuleInterface (..))
import LibPackage (libInterfaces, libOrder, libPackage)
import MirEval (fromMirValue, runProgram)
import Pipeline (compileSource)
import Syntax (Value (..))
import TestHarness (Test (..), forceTestResult, testAssertEq, testAssertTrue, testCase)
import Utils (Result (..), bindResult)

-- The compiler libraries (lib/eq.tersus and the rest) compiled as modules
-- of the synthetic lib package: the package loads, each library checks
-- against the interfaces of the libraries it imports, and the interfaces
-- carry what an importer needs under the libraries' bare names.
testLibModules :: Test
testLibModules =
    TestList
        "testLibModules"
        [ TestList
            "the lib package standalone"
            [ TestCase "bootstrap is independent of the production parser" $
                bracket (lookupEnv "TERSUS_PARSER") restoreParser $ \_ -> do
                    -- Run first in this cold group: an invalid backend must not
                    -- affect the libraries needed to build the native parser.
                    setEnv "TERSUS_PARSER" "unavailable-bootstrap-guard"
                    _ <- evaluate (forceTestResult compiles)
                    pure compiles
            , testCase "it compiles" compiles
            , testCase "modules compile dependencies first" orderIsDependencyFirst
            , testCase "eq declares Eq and its impls" (interface "eq" (\iface -> Map.member "Eq" (ifTraits iface) && implsIn iface [("Eq", "List"), ("Eq", "Array"), ("Eq", "Box")]))
            , testCase "clone declares Clone and its impls" (interface "clone" (\iface -> Map.member "Clone" (ifTraits iface) && implsIn iface [("Clone", "List"), ("Clone", "Array"), ("Clone", "Box")]))
            , testCase "prelude declares its traits" (interface "prelude" (\iface -> allIn (Map.keys (ifTraits iface)) ["Sequence", "Growable", "Copy", "Drop", "Deref", "Hash"]))
            , testCase "prelude has the word Hash impls" (interface "prelude" (\iface -> implsIn iface [("Hash", "Int"), ("Hash", "Byte"), ("Hash", "Bool")] && allIn (Map.keys (ifFunctions iface)) ["hashCombine", "<Int as Hash>::hash"]))
            , testCase "prelude does not re-export Clone" (interface "prelude" (\iface -> not (implsIn iface [("Clone", "List")]) && Map.notMember "cloneBoxedArray" (ifTemplates iface)))
            , testCase "string declares String and its impls" (interface "string" (\iface -> Map.member "String" (ifTypes iface) && implsIn iface [("Clone", "String"), ("Eq", "String"), ("Hash", "String"), ("Sequence", "String")]))
            , testCase "map declares HashMap" (interface "map" (\iface -> allIn (Map.keys (ifGenerics iface)) ["HashMap", "Entry"] && implsIn iface [("Clone", "HashMap")]))
            , testCase "set declares HashSet" (interface "set" (\iface -> Map.member "HashSet" (ifGenerics iface) && implsIn iface [("Clone", "HashSet")]))
            , testCase "set reaches map's findNth as a function" (interface "map" (\iface -> Map.member "findNth" (ifFunctions iface)))
            , testCase "bounded helpers travel as templates" (both (interface "eq" (\iface -> Map.member "eqBoxedArrays" (ifTemplates iface))) (both (interface "clone" (\iface -> Map.member "cloneBoxedArray" (ifTemplates iface))) (interface "map" (\iface -> allIn (Map.keys (ifTemplates iface)) ["findIn", "indexFor", "<HashMap>::contains"]))))
            , testCase "generic impl methods travel as templates" (both (interface "eq" (\iface -> Map.member "<List as Eq>::eq" (ifTemplates iface))) (interface "clone" (\iface -> Map.member "<List as Clone>::clone" (ifTemplates iface))))
            ]
        , TestList
            "the single-file path through lib modules"
            [ testCase "a HashMap with word keys hashes through the prelude interface" (compiledRuns "m = HashMap::new().insert(1, 100).insert(2, 200); return m.lookup(1, 0) + m.lookup(2, 0);" (VInt 300))
            , testCase "a HashMap with Bool and String keys" (compiledRuns "m = HashMap::new().insert(true, 5); s = HashMap::new().insert(\"a\", 3).insert(\"b\", 4); return m.lookup(true, 0) * 100 + s.lookup(\"a\", 0) * 10 + s.lookup(\"b\", 0);" (VInt 534))
            , testCase "a HashSet through the map module" (compiledRuns "s = HashSet::new().insert(1).insert(2); if s.contains(1) { if s.contains(3) { return 9; }; return s.size(); }; return 0;" (VInt 2))
            , testCase "a string made by the string module" (compiledRuns "return size(String::fromInt(1203).bytes);" (VInt 4))
            , testCase "Box of an array compares and clones through templates" (compiledRuns "a = Array::boxed(2, 7); b = Array::boxed(2, 7); c = clone(a); if a = b { if c = a { return size(c); }; }; return 0;" (VInt 2))
            , testCase "Copy is synthesized through the prelude interface" (compiledRuns "struct P { x: Int, y: Int }; impl Clone for P { }; impl Copy for P { }; fn getX(p: P) -> Int { return p.x; }; p = P { x: 3, y: 4 }; a = getX(p); b = getX(p); return a * 10 + b + p.y;" (VInt 37))
            , testCase "Drop is synthesized through the prelude interface" (compiledRuns (dropper ++ "v = V::new(3); w = V::new(4); return v.n + w.n;") (VInt 7))
            , testCase "an Eq of the program's own suppresses the eq module" (compiledRejected "trait Eq { }; if [1] = [1] { return 1; }; return 0;" "List<Int> is compared with =")
            , testCase "a String of the program's own takes its literals" (compiledRuns "struct String { bytes: List<Byte> }; s = \"hi\"; return size(s.bytes);" (VInt 2))
            , testCase "an Eq of the program's own with a string literal" (compiledRuns (ownEq ++ "s = \"hi\"; return size(s.bytes);") (VInt 2))
            , testCase "an Eq of the program's own compares strings" (compiledRuns (ownEq ++ "if \"a\" = \"a\" { if \"a\" != \"b\" { return 1; }; }; return 0;") (VInt 1))
            , testCase "an Eq of the program's own with a HashMap" (compiledRuns (ownEq ++ "m = HashMap::new().insert(\"a\", 3).insert(\"b\", 4); return m.lookup(\"a\", 0) * 10 + m.lookup(\"b\", 0);") (VInt 34))
            ]
        , TestList "Eq shadowing source fixtures"
            ([ testCase (path ++ " rejects " ++ label) (rejected (compile source) "replacement Eq")
             | (path, compile) <- [("single", checkedSource), ("package", checkedPackage)]
             , (label, trait) <-
                [ ("return type", "trait Eq { fn eq(self: &Self, other: &Self) -> Int; }; ")
                , ("contract", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm false; }]; }; ")
                , ("empty method set", "trait Eq { }; ")
                , ("extra method", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; fn extra(self: &Self) -> Int; }; ")
                , ("generic arity", "trait Eq<T> { fn eq(self: &Self, other: &Self) -> Bool; }; ")
                ]
             , let source = trait ++ "s = \"a\"; return size(s.bytes);"
             ] ++
             [ testCase (path ++ " accepts source " ++ owner ++ " impl") (runs (compile source) (VInt 2))
             | (path, compile) <- [("single", checkedSource), ("package", checkedPackage)]
             , owner <- ["List", "Array", "Box"]
             , let source = ownEq ++ eqImpl owner ++ "s = \"hi\"; return size(s.bytes);"
             ] ++
             [ testCase "compatible Eq keeps String equality" (runs (checkedSource (ownEq ++ "if \"a\" = \"a\" { return 1; }; return 0;")) (VInt 1))
             , testCase "suppressed eq helper is not exposed" (rejected (checkedSource (ownEq ++ "s = \"hi\"; a = Array::boxed(1, 1); return eqBoxedArrays(a, a);")) "eqBoxedArrays")
             , testCase "a replacement without cached Eq impls is unrestricted" (runs (checkedSource "trait Eq { }; return 7;") (VInt 7))
             , testCase "supplied single-file AST is lowered without reparsing" (runs (Compile.parseSourceParts True "return 9;" `bindResult` Compile.lowerSourceParts True) (VInt 9))
             , testCase "Copy source regression" (runs (checkedSource "struct P { x: Int, y: Int }; impl Clone for P { }; impl Copy for P { }; fn getX(p: P) -> Int { return p.x; }; p = P { x: 3, y: 4 }; a = getX(p); b = getX(p); return a * 10 + b + p.y;") (VInt 37))
             , testCase "Drop source validates and retains its implementation" $ case checkedSource (dropper ++ "v = V::new(3); w = V::new(4); return v.n + w.n;") of
                Error err -> Just err
                Ok program -> testAssertTrue (Map.member "<V as Drop>::drop" (M.progFunctions program))
             , testCase "injected package AST is compiled without reparsing" injectedPackage
             ])
        ]
  where
    checkedSource source = Compile.lowerSource True source `bindResult` \program ->
        validateProgram program `bindResult` \_ -> Ok program
    checkedPackage source = case Modules.loadFromEntry (Modules.resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", source)]) "app/main.tersus" of
        Left err -> Error err
        Right (Modules.PackageResult pkg) -> compileModulesValidated pkg
        Right _ -> Error "fixture did not load as a package"
    runs result expected = case result `bindResult` runProgram of
        Error err -> Just err
        Ok value -> testAssertEq (fmap fromMirValue value) (Just expected)
    rejected result expected = case result of
        Error err -> testAssertTrue (expected `isInfixOf` err)
        Ok _ -> Just ("expected rejection containing " ++ expected)
    eqImpl owner = unlines (takeThrough (== "};") (dropWhile (not . isInfixOf ("Eq for " ++ owner ++ "<")) (lines eqSource)))
    takeThrough _ [] = []
    takeThrough p (x : xs) = x : if p x then [] else takeThrough p xs
    injectedPackage =
        let parser decls source = either (Left . show) Right (Parse.parseFileWith decls (if source == "@supplied-ast@" then "return 11;" else source))
         in case Modules.loadFromEntryWith parser (Modules.resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", "@supplied-ast@")]) "app/main.tersus" of
                Right (Modules.PackageResult pkg) -> runs (compileModulesValidated pkg) (VInt 11)
                other -> Just ("injected fixture failed: " ++ show other)
    restoreParser Nothing = unsetEnv "TERSUS_PARSER"
    restoreParser (Just backend) = setEnv "TERSUS_PARSER" backend
    compiledRuns source expected = case compileSource source `bindResult` runProgram of
        Error err -> Just ("compiling and running failed: " ++ err)
        Ok result -> testAssertEq (fmap fromMirValue result) (Just expected)
    compiledRejected source expected = case compileSource source of
        Error err -> if expected `isInfixOf` err then Nothing else Just ("expected failure containing " ++ show expected ++ ", got: " ++ err)
        Ok _ -> Just "the program compiled, where a failure was expected"
    dropper = "struct V { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl V { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; }; impl Drop for V { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; };"
    ownEq = "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; }; "
    compiles = case libPackage of
        Error err -> Just err
        Ok _ -> Nothing
    orderIsDependencyFirst = case libPackage of
        Error err -> Just err
        Ok pkg -> testAssertEq (libOrder pkg) ["types", "eq", "clone", "prelude", "string", "map", "set"]
    allIn keys wanted = all (`elem` keys) wanted
    implsIn iface wanted = all (`Set.member` ifImpls iface) wanted
    both (Just err) _ = Just err
    both Nothing other = other
    interface name check = case libPackage of
        Error err -> Just err
        Ok pkg -> case Map.lookup name (libInterfaces pkg) of
            Nothing -> Just ("no interface for lib module " ++ name)
            Just iface -> testAssertTrue (check iface)
