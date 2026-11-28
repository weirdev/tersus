-- The installed std package and fixed listed prelude (plan Phase 4): canonical declaration identities, List and Box
-- drops in their owning module, explicit std imports, explicit/prelude equivalence, ordinary file-level ambiguity on
-- prelude collisions, inner lexical shadowing, standalone/stdin/package agreement, and noPrelude opt-out.
module TestStdGraph (testStdGraph) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map

import Compile (lowerStatements)
import Interface (ModuleInterface (..))
import LibPackage (LibPackage (..), libPackage)
import qualified Mir as M
import MirEval (renderMirValue, runProgram)
import Modules (LoadOptions (..), LoadResult (..), Resolver (..), defaultLoadOptions, packageSnapshot, resolverFromFiles)
import qualified Pipeline
import PreludeSource (libPackageFiles)
import TestHarness
import TestParserFragments (parseStatementBlock)
import Types (Arg (..), OwnershipFacts (..), OwnershipTransport (..), Type (..))
import Utils (Result (..), bindResult, mapResult)

testStdGraph :: Test
testStdGraph = TestList "testStdGraph"
    [ testCase "the installed std package compiles via LoadPackage, and List and Box drops are core's" coreFacts
    , testCase "a generic type's derived Clone reaches its instances in another module and the copies of a function with bounds" $
        case programOf (defaultLoadOptions, []) [("app/package.tersus", ""), ("app/util/util.tersus", "struct Bag<K> { xs: List<K> };\nimpl<K> Clone for Bag<K> { };\nstruct Plain<K> { xs: List<K> };"), ("app/main.tersus", "import app::util { Bag, Plain };\nfn twice<K: Clone>(b: &Bag<K>) -> Int { c = clone(b); return size(c.xs) * 2; };\nb = Bag { xs: [1, 2] };\np = Plain { xs: [3] };\nreturn twice(&b) + size(p.xs);")] of
            Left e -> Just ("the package did not compile: " ++ e)
            Right program ->
                let cloneOf owner = fmap (fmap fst . ownershipClone) (Map.lookup owner =<< M.progOwnership program)
                 in testAssertEq (cloneOf "app$util$util$Bag<Int>", cloneOf "app$util$util$Plain<Int>") (Just (Just "std$core$ownership$Clone"), Just Nothing)
    , testCase "a generic function's copy at a type only an unused function gives it keeps none of that copy's facts' functions" $
        case programOf (defaultLoadOptions, []) [("app/package.tersus", ""), ("app/main.tersus", "struct S { n: Int };\nimpl Clone for S { };\nfn keep<T>(x: T) -> List<T> { return push([], x); };\nfn unused() -> Int { k = keep(S { n: 1 }); return size(k); };\nk = keep(1);\nreturn size(k);")] of
            Left e -> Just ("the package did not compile: " ++ e)
            Right program -> testAssertEq [name | name <- Map.keys (M.progFunctions program), "clone[S]" `isInfixOf` name] []
    , testCase "a noPrelude package's own Eq is its build's Eq" $
        let files = [("app/package.tersus", "noPrelude = true;\nEq = main::Eq;"), ("app/main.tersus", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; }; struct P { a: Int }; impl Eq for P { }; p = P { a: 1 }; if p = p { return 1; }; return 0;")]
         in runs files "1" <> providerIs files "Eq" "Eq"
    , testCase "a noPrelude package's own Eq in another module is the build's Eq" $
        runs [("app/package.tersus", "noPrelude = true;\nEq = own::Eq;"), ("app/own/own.tersus", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; }; struct P { a: Int }; impl Eq for P { };"), ("app/main.tersus", "import app::own { P }; p = P { a: 1 }; if p = p { return 1; }; return 0;")] "1"
    , testCase "binding Eq without noPrelude collides with std's prelude Eq" $
        refused [("app/package.tersus", "Eq = main::Eq;"), ("app/main.tersus", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; }; return 0;")] "ambiguous in this file"
    , testCase "two visible providers of Eq are refused" $
        refused [("app/package.tersus", "noPrelude = true;\nEq = a::Eq;\nEq = b::Eq;"), ("app/a/a.tersus", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; };"), ("app/b/b.tersus", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; };"), ("app/main.tersus", "import app::a { Eq }; import app::b; return 0;")] "provider"
    , testCase "a package's own Clone provider clones its types" $
        runs (boundPackage "Clone = main::Clone;" "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; }; struct P { a: Int }; impl Clone for P { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] { return P { a: self.a + 0 }; }; }; p = P { a: 7 }; q = p.clone(); return q.a;") "7"
    , testCase "two providers of one role in one build are refused" $
        refused [("app/package.tersus", "noPrelude = true;\nClone = a::Clone;\nClone = b::Clone;"), ("app/a/a.tersus", "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };"), ("app/b/b.tersus", "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };"), ("app/main.tersus", "import app::a { Clone }; import app::b; return 0;")] "provider"
    , testCase "a noPrelude package imports std explicitly from the default installed std root" $
        runs (noPreludePackage "import std::core::types { List };\nimport std::core::clone;\nfn count(xs: &List<Int>) -> Int { return size(xs); };\nxs = [1, 2, 3];\nys = xs.clone();\nreturn count(&ys);") "3"
    , testCase "a noPrelude package imports std explicitly from a custom --std-root" $
        runsWith stdRoot (noPreludePackage "import std::core::types { List };\nimport std::core::clone;\nfn count(xs: &List<Int>) -> Int { return size(xs); };\nxs = [1, 2, 3];\nys = xs.clone();\nreturn count(&ys);") "3"
    , testCase "an aliased std import names the same declarations" $
        runsWith stdRoot (noPreludePackage "import std::core::types as t;\nimport std::core::clone;\nfn count(xs: &t::List<Int>) -> Int { return size(xs); };\nxs = [4, 5];\nys = xs.clone();\nreturn count(&ys);") "2"
    , testCase "explicit listed prelude imports with noPrelude match default prelude compilation" $
        let body = "s = \"ab\"; t = clone(s); c = \"c\"; u = t.concat(&c); m = HashMap::new(); m = m.insert(1, 2); h = HashSet::new(); h = h.insert(3); k = 1; xs = map([1, 2], fn(x: Int) -> Int => x + 1); return size(u.bytes) + m.size() + h.size() + m.lookup(&k, 0) + size(xs);"
            explicit = unlines
                [ "import std::core::types::List;"
                , "import std::core::types::Box;"
                , "import std::core::ownership::Clone;"
                , "import std::core::ownership::Copy;"
                , "import std::core::ownership::Drop;"
                , "import std::core::ownership::Deref;"
                , "import std::core::clone::map;"
                , "import std::eq::Eq;"
                , "import std::prelude::Sequence;"
                , "import std::prelude::Growable;"
                , "import std::prelude::Hash;"
                , "import std::prelude::hashCombine;"
                , "import std::string::String;"
                , "import std::string::Format;"
                , "import std::map::HashMap;"
                , "import std::set::HashSet;"
                , "import std::thread::Thread;"
                , body
                ]
         in runs [("app/package.tersus", ""), ("app/main.tersus", body)] "9"
                <> runs (noPreludePackage explicit) "9"
                <> case Pipeline.compileSource body `bindResult` runProgram of
                    Ok (Just v) -> testAssertEq (renderMirValue v) "9"
                    other -> Just ("standalone source did not run: " ++ show other)
    , testCase "std's interfaces name an imported List by its provider in struct fields" fieldIdentity
    , testCase "programs run with std's strings, maps and sets" $
        runs [("app/package.tersus", ""), ("app/main.tersus", "s = \"ab\"; t = clone(s); c = \"c\"; u = t.concat(&c); m = HashMap::new(); m = m.insert(1, 2); h = HashSet::new(); h = h.insert(3); k = 1; return size(u.bytes) + m.size() + h.size() + m.lookup(&k, 0);")] "7"
    , testCase "a module's own Clone impl, a struct built with list type arguments and a list in a variant beside std's" $
        runs [("app/package.tersus", ""), ("app/main.tersus", "struct T { a: Int };\nimpl Clone for T { };\nstruct W<E> { v: E };\nenum Shape { Ring { xs: List<Int> }, Dot { } };\nfn ringSize(s: Shape) -> Int { if s is Shape::Ring { r = s as Shape::Ring; return size(r.xs); }; return 0; };\nt = clone(T { a: 1 });\ns = \"ab\";\nu = clone(s);\nw = W<List<Int>> { v: [1, 2] };\nreturn size(u.bytes) + t.a + size(w.v) + ringSize(Shape::Ring { xs: [5] });\n")] "6"
    , testCase "a package binds a trait of any name to a role, and its List and Clone named alike are ordinary declarations" $
        runs (bindingPackage "Clone = own::Copyable;" "import app::own { Copyable };\nimport app::shapes { List };\nstruct P { a: Int };\nimpl Copyable for P { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] { return P { a: self.a + 0 }; }; };\np = P { a: 7 };\nq = clone(p);\nl = List { n: 2 };\nreturn q.a + l.n;") "9"
    , testCase "list syntax in a package that binds no List is refused" $
        refused (bindingPackage "Clone = own::Copyable;" "xs = [1, 2];\nreturn size(xs);") "List syntax requires its checked provider"
    , testCase "a package's same-named trait without a binding provides no role" $
        refused (bindingPackage "Clone = own::Copyable;" "import app::shapes { Clone };\nstruct P { a: Int };\nimpl Clone for P { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] { return P { a: self.a + 0 }; }; };\np = P { a: 7 };\nq = clone(p);\nreturn q.a;") "clone requires its checked Clone provider, and none is bound in this build"
    , testCase "a binding that names no declaration of its module, or one of the wrong kind, is refused" $
        refused (bindingPackage "Clone = own::Missing;" "import app::own { Copyable };\nreturn 0;") "the package binds Clone to own::Missing, which is no trait of the module"
            <> refused (bindingPackage "List = own::Copyable;" "import app::own { Copyable };\nreturn 0;") "the package binds List to own::Copyable, which is no type of the module"
    , testCase "a binding of no module of the package and an unknown role are refused by the marker" $
        refused (bindingPackage "Clone = absent::Clone;" "return 0;") "which is no module of the package"
            <> refused (bindingPackage "Hash = own::Copyable;" "return 0;") "package configuration:"
    , testCase "standalone source gets its providers and linked bodies from std" $
        case Pipeline.compileSource "xs = [1, 2, 3];\nys = clone(xs);\nreturn size(ys);" of
            Error e -> Just e
            Ok program ->
                testAssertEq (Map.lookup "List" (M.progProtocols program)) (Just "std$core$types$List")
                    <> testAssertTrue (any ("<std$core$types$List as std$core$ownership$Clone>::clone" `isInfixOf`) (Map.keys (M.progFunctions program)))
                    <> testAssertEq (mapResult (fmap renderMirValue) (runProgram program)) (Ok (Just "3"))
    , testCase "standalone source names std's List as std declares it, by reference too" $
        case Pipeline.compileSource "struct S { xs: List<Int> };\nfn grow(r: &mut List<Int>) -> Int { *r = push(clone(*r), 3); return 0; };\ns = S { xs: [1, 2] };\nys = [4];\nn = grow(&mut ys);\nreturn size(s.xs) + size(ys) + n;" of
            Error e -> Just e
            Ok program ->
                testAssertEq [fields | (name, M.StructDecl fields) <- Map.toList (M.progTypes program), name == "S"] [[("xs", TNamed "std$core$types$List" [ArgType TInt])]]
                    <> testAssertEq (mapResult (fmap renderMirValue) (runProgram program)) (Ok (Just "4"))
    , testCase "file-level collision with a listed prelude name is an ordinary ambiguity error in packages and standalone files" $
        refused [("app/package.tersus", ""), ("app/main.tersus", "struct List { n: Int }; return 0;")] "ambiguous in this file"
            <> refused [("app/package.tersus", ""), ("app/main.tersus", "fn fold(x: Int) -> Int { return x; }; return fold(1);")] "ambiguous in this file"
            <> testAssertErrorContains "ambiguous in this file" (Pipeline.compileSource "struct List { n: Int }; return 0;")
    , testCase "inner lexical shadowing of prelude function names stays allowed" $
        runs [("app/package.tersus", ""), ("app/main.tersus", "fn f(map: Int, fold: Int) -> Int { any = map + fold; return any; }; return f(20, 22);")] "42"
    , testCase "a broken --std-root without noPrelude = true fails with a module import cycle" $
        let brokenStd =
                ( defaultLoadOptions{installedStdRoot = Just "broken/std"}
                , [("broken/" ++ path, if path == "std/package.tersus" then "" else text) | (path, text) <- libPackageFiles]
                )
         in case programOf brokenStd [("app/package.tersus", ""), ("app/main.tersus", "return 0;")] of
                Left e | "module import cycle" `isInfixOf` e -> Nothing
                other -> Just ("expected module import cycle on broken std without noPrelude: " ++ take 300 (show other))
    , testCase "raw statements declaring their own List and Clone, with no libraries, provide no roles" $
        case parseStatementBlock "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };\nstruct List<T> { n: Int };\nxs = [1, 2];\nreturn size(xs);" of
            Left e -> Just e
            Right stmts -> case lowerStatements stmts of
                Error e | "List syntax requires its checked provider" `isInfixOf` e -> Nothing
                other -> Just ("not refused for want of a provider: " ++ take 300 (show other))
    , testCase "a package named std is not the compiler's: its unused function with bounds is validated where it is written" $
        let pkg name = [("app/package.tersus", "noPrelude = true;"), ("app/main.tersus", "import " ++ name ++ "::m { M };\nreturn 0;"), (name ++ "/package.tersus", "noPrelude = true;"), (name ++ "/m/m.tersus", "trait M { fn m(self: &Self) -> Int [{ }] [{ }]; };\nfn f<T: M>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return x.m(); };")]
         in refused (pkg "std") "Could not prove: return >= 0" <> refused (pkg "vendor") "Could not prove: return >= 0"
    , testCase "non-prelude std internal names such as listNew do not collide with user declarations" $
        runs [("app/package.tersus", ""), ("app/main.tersus", "fn listNew() -> Int { return 40; }; xs = [1, 2]; return listNew() + size(xs);")] "42"
    ]

coreFacts :: TestResult
coreFacts = case libPackage of
    Error e -> Just ("the installed std package did not load: " ++ e)
    Ok pkg ->
        let coreOwn = Map.lookup "core" (libOwnership pkg)
            row name = [f | Just (Just t) <- [coreOwn], Just f <- [Map.lookup name (transportOwnership t)]]
            dropIn name = case row name of
                [f] -> testAssertEq (fst <$> ownershipDrop f) (Just "std$core$ownership$Drop")
                    <> testAssertTrue (maybe False (("std$core$ownership$Drop" `isInfixOf`) . snd) (ownershipDrop f))
                other -> Just ("core has no single row for " ++ name ++ ": " ++ show other)
         in testAssertTrue ("core" `elem` libOrder pkg)
                <> dropIn "std$core$types$List"
                <> dropIn "std$core$types$Box"

fieldIdentity :: TestResult
fieldIdentity = case libPackage of
    Error e -> Just ("the installed std package did not load: " ++ e)
    Ok pkg ->
        let ctor lib name = [fields | Just iface <- [Map.lookup lib (libInterfaces pkg)], Just (_, fields) <- [Map.lookup name (ifCtors iface)]]
            generic lib name = [fields | Just iface <- [Map.lookup lib (libInterfaces pkg)], Just (_, fields) <- [Map.lookup name (ifGenerics iface)]]
            list t = TNamed "std$core$types$List" [ArgType t]
         in testAssertEq (ctor "string" "std$string$string$String") [[("bytes", list TByte)]]
                <> testAssertEq (map (lookup "buckets") (generic "map" "std$map$map$HashMap")) [Just (list (list (TNamed "std$map$map$Entry" [ArgType (TParam "K"), ArgType (TParam "V")])))]

type Files = [(FilePath, String)]

noPreludePackage :: String -> Files
noPreludePackage source = [("app/package.tersus", "noPrelude = true;"), ("app/main.tersus", source)]

boundPackage :: String -> String -> Files
boundPackage bindings source = [("app/package.tersus", "noPrelude = true;\n" ++ bindings), ("app/main.tersus", source)]

bindingPackage :: String -> String -> Files
bindingPackage bindings source =
    boundPackage bindings source
        ++ [ ("app/own/own.tersus", "trait Copyable { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };")
           , ("app/shapes/shapes.tersus", "struct List { n: Int };\ntrait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };")
           ]

-- The compiler's std sources as an explicit --std-root
stdRoot :: (LoadOptions, Files)
stdRoot = (defaultLoadOptions{installedStdRoot = Just "installed/std"}, [("installed/" ++ path, text) | (path, text) <- libPackageFiles])

programOf :: (LoadOptions, Files) -> Files -> Either String M.Program
programOf (options, extra) files = case Pipeline.loadFromEntry (resolverFromFiles (files ++ extra)){resolverOptions = options} "app/main.tersus" of
    Right (PackageResult pkg) -> case Pipeline.compileModulesToProgram (packageSnapshot pkg) of
        Error e -> Left e
        Ok program -> Right program
    Right _ -> Left "not a package"
    Left e -> Left e

runsWith :: (LoadOptions, Files) -> Files -> String -> TestResult
runsWith root files expected = case programOf root files of
    Left e -> Just ("the package did not compile: " ++ e)
    Right program -> case runProgram program of
        Error e -> Just ("the package did not run: " ++ e)
        Ok value -> testAssertEq (fmap renderMirValue value) (Just expected)

runs :: Files -> String -> TestResult
runs = runsWith (defaultLoadOptions, [])

refused :: Files -> String -> TestResult
refused files needle = case programOf (defaultLoadOptions, []) files of
    Left e -> if needle `isInfixOf` e then Nothing else Just ("refused without " ++ needle ++ ": " ++ take 400 e)
    Right _ -> Just ("expected a refusal containing " ++ needle)

providerIs :: Files -> String -> String -> TestResult
providerIs files role provider = case programOf (defaultLoadOptions, []) files of
    Left e -> Just e
    Right program -> testAssertEq (Map.lookup role (M.progProtocols program)) (Just provider)
