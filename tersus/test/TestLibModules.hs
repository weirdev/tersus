module TestLibModules (testLibModules) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Interface (ModuleInterface (..))
import LibPackage (libInterfaces, libOrder, libPackage)
import MirEval (fromMirValue, runProgram)
import Pipeline (compileSource)
import Syntax (Value (..))
import TestHarness (Test (..), testAssertEq, testAssertTrue, testCase)
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
            [ testCase "it compiles" compiles
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
            ]
        ]
  where
    compiledRuns source expected = case compileSource source `bindResult` runProgram of
        Error err -> Just ("compiling and running failed: " ++ err)
        Ok result -> testAssertEq (fmap fromMirValue result) (Just expected)
    compiledRejected source expected = case compileSource source of
        Error err -> if expected `isInfixOf` err then Nothing else Just ("expected failure containing " ++ show expected ++ ", got: " ++ err)
        Ok _ -> Just "the program compiled, where a failure was expected"
    dropper = "struct V { addr: Addr<Int>, n: Int, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = n; affirm count(blk) = 0; affirm n >= 0; }]; impl V { fn new(n: Int) -> Self [{ affirm n >= 0; }] [{ }] { (a, b) = Addr::alloc(n); return Self { addr: a, n: n, blk: b }; }; }; impl Drop for V { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; };"
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
