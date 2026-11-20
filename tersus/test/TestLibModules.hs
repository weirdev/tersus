module TestLibModules (testLibModules, testNativeStorageModules) where

import Control.Exception (bracket, evaluate)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Compile
import qualified Modules
import qualified ParserSeed as Parse
import qualified ParsedFile as Parse
import PreludeSource (ownershipSource, typesSource, eqSource, cloneSource, preludeSource, stringSource, mapSource, setSource, threadSource, listsSource, boxSource, nativeHelperName, stdName)
import qualified Mir as M
import ValidatorNative (validateCompiled, validateLibrary)
import Interface (ModuleInterface (..))
import Lowering (lowerAccepted)
import MirMoves (finishLowered)
import ElaborateRequest (Extraction (..), Request (..), Response (..))
import ElaboratorTool (sourceElaborator)
import LibPackage (LibPackage (..), libPackage, libModuleId, nativeStorageUnits, compileLibPackageWith, nativeStorageUnitsWith)
import PreludeSource (libPackageFiles)
import ElaborateRequest (LibraryAnswer (..), LoadKind (..), LoadRequest (..), LoadResponse (..))
import ElaboratorTool (bootstrapLoader, sourceLoader)
import Link (linkPrograms, pruneProgram)
import MirLists (lowerLists)
import Types (Arg (..), Type (..), Size (..))
import MirEval (fromMirValue, runProgram, MirValue (MInt))
import Pipeline (compileModulesValidated, compileSource, ownedSource, erasedModuleProgram, ownedModuleProgram)
import Syntax (Value (..))
import TestHarness (Test (..), forceTestResult, testAssertEq, testAssertTrue, testCase)
import TestStorageOracle (eraseStorageHelper)
import qualified PackageCompile as Package
import PreludeSource (toolPackageFiles)
import MirHousekeeping (expandRefWrites, insertOwnership)
import MirData (forNative, readProgram, writeProgram)
import MirHousekeeping (nativeStorage, storageProgram)
import Utils (Result (..), bindResult, flatResultMap, mapResult)

-- The compiler libraries (lib/std/eq/eq.tersus and the rest) compiled as modules
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
            , testCase "implicit snapshots are the source files without an importing adapter" $
                testAssertEq [lookup ("std/" ++ libraryPath name ++ ".tersus") libPackageFiles | (name, _) <- implicitSources]
                    [Just source | (_, source) <- implicitSources]
            , testCase "implicit source imports preserve the dependency graph" $ case mapM (Parse.parseImportPrefix . snd) implicitSources of
                Left e -> Just (show e)
                Right imports -> case libPackage of
                    Error e -> Just e
                    Ok pkg -> both
                        (testAssertEq (map (map (\imp -> (Parse.importPath imp, Parse.importAlias imp, Parse.importNames imp))) imports)
                            [[(["std"] ++ path, Nothing, Just names) | (path, names) <- deps] | (_, deps) <- implicitDependencies])
                        (testAssertEq (libImports pkg) (Map.fromList moduleDependencies))
            , testCase "modules compile dependencies first" orderIsDependencyFirst
            , TestList "interface declarations" [ testCase name result | (name, result) <- interfaceCases ]
            ]
        , TestList
            "the single-file path through lib modules"
            [ testCase "a HashMap with word keys hashes through the prelude interface" (compiledRuns "m = HashMap::new().insert(1, 100).insert(2, 200); return m.lookup(1, 0) + m.lookup(2, 0);" (VInt 300))
            , testCase "a HashMap with Bool and String keys" (compiledRuns "m = HashMap::new().insert(true, 5); s = HashMap::new().insert(\"a\", 3).insert(\"b\", 4); return m.lookup(true, 0) * 100 + s.lookup(\"a\", 0) * 10 + s.lookup(\"b\", 0);" (VInt 534))
            , testCase "a HashSet through the map module" (compiledRuns "s = HashSet::new().insert(1).insert(2); if s.contains(1) { if s.contains(3) { return 9; }; return s.size(); }; return 0;" (VInt 2))
            , testCase "a string made by the string module" (compiledRuns "return size(String::fromInt(1203).bytes);" (VInt 4))
            , testCase "Box of an array compares and clones through templates" (compiledRuns "a = Array::boxed(2, 7); b = Array::boxed(2, 7); c = clone(a); if a = b { if c = a { return size(c); }; }; return 0;" (VInt 2))
            , testCase "Copy is synthesized through the prelude interface" (runs (checkedSource "struct P { x: Int, y: Int }; impl Clone for P { }; impl Copy for P { }; fn getX(p: P) -> Int { return p.x; }; p = P { x: 3, y: 4 }; a = getX(p); b = getX(p); return a * 10 + b + p.y;") (VInt 37))
            , testCase "Drop is synthesized through the prelude interface" (compiledRuns (dropper ++ "v = V::new(3); w = V::new(4); return v.n + w.n;") (VInt 7))
            , -- (= is std's Eq, the role std's package binds: a trait of the program that is spelled Eq is another trait)
              testCase "an Eq of the program's own leaves = to std's Eq" (compiledRuns "trait Eq { }; if [1] = [1] { return 1; }; return 0;" (VInt 1))
            , testCase "a String of the program's own takes its literals" (compiledRuns "struct String { bytes: List<Byte> }; s = \"hi\"; return size(s.bytes);" (VInt 2))
            , testCase "an Eq of the program's own with a string literal" (compiledRuns (ownEq ++ "s = \"hi\"; return size(s.bytes);") (VInt 2))
            , testCase "an Eq of the program's own compares strings" (compiledRuns (ownEq ++ "if \"a\" = \"a\" { if \"a\" != \"b\" { return 1; }; }; return 0;") (VInt 1))
            , testCase "an Eq of the program's own with a HashMap" (compiledRuns (ownEq ++ "m = HashMap::new().insert(\"a\", 3).insert(\"b\", 4); return m.lookup(\"a\", 0) * 10 + m.lookup(\"b\", 0);") (VInt 34))
            ]
        , TestList "Eq shadowing source fixtures"
            ([ testCase (path ++ " keeps std's = beside an own Eq with another " ++ label) (runs (compile source) (VInt 1))
             | (path, compile) <- [("single", checkedSource), ("package", checkedPackage)]
             , (label, trait) <-
                [ ("return type", "trait Eq { fn eq(self: &Self, other: &Self) -> Int; }; ")
                , ("contract", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm false; }]; }; ")
                , ("empty method set", "trait Eq { }; ")
                , ("extra method", "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; fn extra(self: &Self) -> Int; }; ")
                , ("generic arity", "trait Eq<T> { fn eq(self: &Self, other: &Self) -> Bool; }; ")
                ]
             , let source = trait ++ "s = \"a\"; if s = \"a\" { return size(s.bytes); }; return 0;"
             ] ++
             -- (an impl of the program's own Eq does not make its bound the Eq role: = of a T still needs std's)
             [ testCase (path ++ " an own Eq's " ++ owner ++ " impl does not bound = by std's Eq") (rejected (compile source) "T is compared with =, which needs it to implement Eq")
             | (path, compile) <- [("single", checkedSource), ("package", checkedPackage)]
             , owner <- ["List", "Array", "Box"]
             , let source = ownEq ++ eqImpl owner ++ "s = \"hi\"; return size(s.bytes);"
             ] ++
             [ testCase "compatible Eq keeps String equality" (runs (checkedSource (ownEq ++ "if \"a\" = \"a\" { return 1; }; return 0;")) (VInt 1))
             , -- (std's eq module is the build's Eq, whatever a trait of the program is spelled)
               testCase "std's eq helper is std's beside an own Eq" (runs (checkedSource (ownEq ++ "s = \"hi\"; a = Array::boxed(1, 1); return eqBoxedArrays(a, a);")) (VBool True))
             , testCase "a replacement without cached Eq impls is unrestricted" (runs (checkedSource "trait Eq { }; return 7;") (VInt 7))
             , testCase "supplied single-file AST is lowered without reparsing" (runs (Compile.lowerSourceUsing (\request -> sourceLoader request{lrResolver = (lrResolver request){Modules.resolverFiles = Map.fromList [("<source>", "return 9;")]}}) libPackage False True "@supplied-ast@") (VInt 9))
             , testCase "Drop source validates and retains its implementation" $ case checkedSource (dropper ++ "v = V::new(3); w = V::new(4); return v.n + w.n;") of
                Error err -> Just err
                Ok program -> testAssertTrue (Map.member ("<V as " ++ dropTrait ++ ">::drop") (M.progFunctions program))
             , testCase "injected package AST is compiled without reparsing" injectedPackage
             , testCase "production helper linking retains runtime layouts" $ case ownedSource "xs = [1]; b = Box::new(1); return size(xs) + Box::unbox(b);" of
                Error e -> Just e
                Ok p -> runtimeStorageLayout p
             , testCase "package custom Box survives the production list-helper link" $ case checkedPackage "struct Box { x: Int }; b = Box { x: 3 }; xs = [1]; return b.x + size(xs);" `bindResult` erasedModuleProgram `bindResult` ownedModuleProgram of
                Error e -> Just e
                Ok p -> both (testAssertEq (Map.lookup "Box" (M.progTypes p)) (Just (M.StructDecl [("x", TInt)]))) (testAssertTrue (Map.notMember "boxNew" (M.progFunctions p)))
             , -- (the native helpers have std's canonical names, which no function of a package entry has)
               testCase "a package entry function spelled like a native helper is the entry's own" (runs (checkedPackage "fn listNew() -> Int { return 7; }; return listNew();") (VInt 7))
             ])
        ]
  where
    implicitSources = [("core/ownership", ownershipSource), ("core/types", typesSource), ("core/clone", cloneSource), ("eq", eqSource),
        ("prelude", preludeSource), ("string", stringSource), ("map", mapSource), ("set", setSource), ("thread", threadSource)]
    libraryPath name = if '/' `elem` name then name else name ++ "/" ++ name
    -- (each file imports by name what it uses of the modules of std before it)
    implicitDependencies =
        [ ("core/ownership", [])
        , ("core/types", [(["core", "ownership"], ["Drop"])])
        , ("core/clone", [(["core", "types"], ["List", "Box"]), (["core", "ownership"], ["Clone"])])
        , ("eq", [(["core", "types"], ["List", "Box"])])
        , ("prelude", [(["core", "types"], ["List", "Box"]), (["core", "ownership"], ["Clone"])])
        , ("string", [(["core", "types"], ["List"]), (["core", "ownership"], ["Clone"]), (["eq"], ["Eq"]), (["prelude"], ["Sequence", "Growable", "Hash", "hashCombine"])])
        , ("map", [(["core", "types"], ["List"]), (["core", "ownership"], ["Clone"]), (["eq"], ["Eq"]), (["prelude"], ["Hash"])])
        , ("set", [(["core", "types"], ["List"]), (["map"], ["HashMap", "findNth"]), (["core", "ownership"], ["Clone"]), (["eq"], ["Eq"]), (["prelude"], ["Hash"])])
        , ("thread", [])
        ]
    moduleDependencies = [("core", []), ("eq", ["core"]), ("prelude", ["core"]), ("string", ["core", "eq", "prelude"]), ("map", ["core", "eq", "prelude"]), ("set", ["core", "map", "eq", "prelude"]), ("thread", [])]
    checkedSource source = Compile.lowerSource True source `bindResult` \program ->
        validateCompiled program `bindResult` \_ -> Ok program
    checkedPackage source = case Modules.loadFromEntry (Modules.resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", source)]) "app/main.tersus" of
        Left err -> Error err
        Right (Modules.PackageResult pkg) -> compileModulesValidated (Modules.packageSnapshot pkg)
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
        let supplied = Modules.resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", "return 11;")]
            loader request = sourceLoader request{lrResolver = supplied}
         in case Modules.loadFromEntryWith loader (Modules.resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", "@supplied-ast@")]) "app/main.tersus" of
                Right (Modules.PackageResult pkg) -> runs (Package.compileModulesWith loader (Modules.packageSnapshot pkg) `bindResult` Package.lowerCompiledPackage) (VInt 11)
                other -> Just ("injected fixture failed: " ++ show other)
    interfaceCases =
        [ ("eq declares Eq and its impls", (interface "eq" (\iface -> Map.member eqTrait (ifTraits iface) && implsIn iface [(eqTrait, list), (eqTrait, "Array"), (eqTrait, box)])))
        , ("core declares the ownership traits and the Clone impls", (interface "core" (\iface -> allIn (Map.keys (ifTraits iface)) (map (stdName "core/ownership") ["Clone", "Copy", "Drop", "Deref"]) && implsIn iface [(cloneTrait, list), (cloneTrait, "Array"), (cloneTrait, box)])))
        , ("prelude declares its traits", (interface "prelude" (\iface -> allIn (Map.keys (ifTraits iface)) (map (stdName "prelude") ["Sequence", "Growable", "Hash"]))))
        , ("prelude has the word Hash impls", (interface "prelude" (\iface -> implsIn iface [(hashTrait, "Int"), (hashTrait, "Byte"), (hashTrait, "Bool")] && allIn (Map.keys (ifFunctions iface)) [stdName "prelude" "hashCombine", "<Int as " ++ hashTrait ++ ">::hash"])))
        , ("prelude does not re-export Clone", (interface "prelude" (\iface -> not (implsIn iface [(cloneTrait, list)]) && Map.notMember (stdName "core/clone" "cloneBoxedArray") (ifTemplates iface))))
        , ("string declares String and its impls", (interface "string" (\iface -> Map.member string (ifTypes iface) && implsIn iface [(cloneTrait, string), (eqTrait, string), (hashTrait, string), (stdName "prelude" "Sequence", string)])))
        , ("map declares HashMap", (interface "map" (\iface -> allIn (Map.keys (ifGenerics iface)) [stdName "map" "HashMap", stdName "map" "Entry"] && implsIn iface [(cloneTrait, stdName "map" "HashMap")])))
        , ("set declares HashSet", (interface "set" (\iface -> Map.member (stdName "set" "HashSet") (ifGenerics iface) && implsIn iface [(cloneTrait, stdName "set" "HashSet")])))
        , ("set reaches map's findNth as a function", (interface "map" (\iface -> Map.member (stdName "map" "findNth") (ifFunctions iface))))
        , ("bounded helpers travel as templates", (both (interface "eq" (\iface -> Map.member (stdName "eq" "eqBoxedArrays") (ifTemplates iface))) (both (interface "core" (\iface -> Map.member (stdName "core/clone" "cloneBoxedArray") (ifTemplates iface))) (interface "map" (\iface -> allIn (Map.keys (ifTemplates iface)) [stdName "map" "findIn", stdName "map" "indexFor", "<" ++ stdName "map" "HashMap" ++ ">::contains"])))))
        , ("generic impl methods travel as templates", (both (interface "eq" (\iface -> Map.member ("<" ++ list ++ " as " ++ eqTrait ++ ">::eq") (ifTemplates iface))) (interface "core" (\iface -> Map.member ("<" ++ list ++ " as " ++ cloneTrait ++ ">::clone") (ifTemplates iface)))))
        ]
    list = stdName "core/types" "List"
    box = stdName "core/types" "Box"
    string = stdName "string" "String"
    eqTrait = stdName "eq" "Eq"
    cloneTrait = stdName "core/ownership" "Clone"
    hashTrait = stdName "prelude" "Hash"
    dropTrait = stdName "core/ownership" "Drop"
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
        Ok pkg -> testAssertEq (libOrder pkg) ["core", "eq", "prelude", "string", "map", "set", "thread"]
    allIn keys wanted = all (`elem` keys) wanted
    implsIn iface wanted = all (`Set.member` ifImpls iface) wanted
    both (Just err) _ = Just err
    both Nothing other = other
    interface name check = case libPackage of
        Error err -> Just err
        Ok pkg -> case Map.lookup name (libInterfaces pkg) of
            Nothing -> Just ("no interface for lib module " ++ name)
            Just iface -> testAssertTrue (check iface)

testNativeStorageModules :: Test
testNativeStorageModules = TestList "testNativeStorageModules"
    [ testCase "snapshot uses the embedded helper texts without concatenating bodies" $
        testAssertEq (map (\path -> lookup path libPackageFiles) ["std/lists/lists.tersus", "std/box/box.tersus"]) [Just listsSource, Just boxSource]
    , testCase "native imports are the compiled dependency graph" $
        case bootstrapLoader Modules.libraryRequest of
            LoadedLibraries answers Nothing -> testAssertEq [(name, imports) | LibraryAnswer name imports _ _ <- answers, name `elem` ["lists", "box"]] [("lists", ["core"]), ("box", ["core"])]
            other -> Just ("the compiler libraries did not load: " ++ take 300 (show other))
    , testCase "user-library compilation excludes native modules" $ case libPackage of
        Ok pkg -> testAssertTrue (all (\name -> name `notElem` libOrder pkg && Map.notMember name (libPrograms pkg) && Map.notMember name (libImports pkg)) ["lists", "box"])
        Error e -> Just e
    , testCase "physical generic constructor owners are not user import types" $ case libPackage of
        Error e -> Just e
        Ok pkg -> let iface = libInterfaces pkg Map.! "core"
                   in testAssertTrue (all (`Map.notMember` ifTypes iface) [list ++ "<'T>", box ++ "<'T>"])
    , testCase "core owns the List and Box drops, and the helpers expose none" $ inspectPackage $ \pkg ->
        let core = libInterfaces pkg Map.! "core"
         in testAssertTrue (ifDrops core == Set.fromList [list, box] && all (\name -> Set.null (ifDrops (libInterfaces pkg Map.! name))) ["lists", "box"])
    , testCase "implicit selection never reaches helper interfaces or units" $
        case Compile.lowerSourceUsing bootstrapLoader libPackage False False "s = \"a\"; return size(s.bytes);" of
            Error err -> Just err
            Ok p -> testAssertEq (runProgram p) (Ok (Just (MInt 1)))
                <> testAssertTrue (all (`Map.notMember` M.progFunctions p) (map nativeHelperName ["listNew", "boxNew"]))
    , testCase "a native helper failure does not fail the regular catalog" $
        let loader rq = case bootstrapLoader rq of
                LoadedLibraries answers _ -> LoadedLibraries (takeWhile ((/= "lists") . laName) answers) (Just "deliberate native storage failure")
                other -> other
         in testAssertEq (mapResult libOrder (compileLibPackageWith loader)) (mapResult libOrder libPackage)
            <> testAssertEq (mapResult (const ()) (nativeStorageUnitsWith loader)) (Error "deliberate native storage failure")
    , testCase "the helpers implement no trait, and core's types have their Drop impls" $ inspectPackage $ \pkg ->
        both (testAssertEq [ifImpls (libInterfaces pkg Map.! name) | name <- ["lists", "box"]] [Set.empty, Set.empty])
            (testAssertTrue (all (`Set.member` ifImpls (libInterfaces pkg Map.! "core")) [(dropTrait, list), (dropTrait, box)]))
    , testCase "helper declarations use the authoritative type interfaces" $ inspectPackage $ \pkg ->
        let types = libPrograms pkg Map.! "core"
         in testAssertTrue (all (\name -> let p = libPrograms pkg Map.! name in M.progGenerics p == M.progGenerics types && M.progInvariants p == M.progInvariants types) ["lists", "box"])
    , testCase "linked helper contracts meet physical-container proofs" $ case validateLibrary storageProgram of
        Error e -> Just e
        Ok _ -> Nothing
    , testCase "erased List and Box instances retain exact fields and offsets" runtimeLayout
    , -- (native code is made of what the program reaches: std's core, which every program is given, is pruned first)
      testCase "native lowering is a no-op without storage and does not force helpers" $ case Compile.lowerSource True "return 7;" of
        Error e -> Just e
        Ok p -> case lowerLists (error "unused helper graph forced") (pruneProgram p) of
            Error e -> Just e
            Ok native -> testAssertEq native (pruneProgram p)
    , testCase "a list selects only list helpers" (selectedHelpers "return [1];" "lists" "box")
    , testCase "a scalar Box selects only Box helpers" (selectedHelpers "return Box::unbox(Box::new(3));" "box" "lists")
    -- (a Box of an array is a List in native code: the operation calls no scalar Box helper, whatever helper definitions the
    -- conservative selection links)
    , testCase "an array-backed Box is a list in native code" $ case lowerNative "return Box::unbox(Box::new(#[1, 2]));" of
        Error e -> Just e
        Ok p -> let calls = [callee | b <- Map.elems (M.fnBlocks (M.progMain p)), M.Call (M.Const (M.CFn callee)) _ _ _ <- [M.blockTerminator b]]
                    mainLocals = [M.localType d | d <- Map.elems (M.fnLocals (M.progMain p))]
                 in both (testAssertTrue (any (\t -> case t of TNamed n _ -> n == list; _ -> False) mainLocals))
                        (testAssertEq [c | c <- calls, ("std$box$box$") `isPrefixOf` c] [])
    , testCase "custom Box is preserved when only lists need storage" (shadowType "Box" "struct Box { x: Int }; b = Box { x: 3 }; xs = [1]; return b.x + size(xs);")
    , testCase "custom List is preserved when only Boxes need storage" (shadowType "List" "struct List { x: Int }; l = List { x: 3 }; b = Box::new(4); return l.x + Box::unbox(b);")
    , testCase "repeated identical helper units link once" $ inspectPackage $ \pkg ->
        let unit = (libModuleId "lists", libPrograms pkg Map.! "lists")
         in case (linkPrograms [coreUnit pkg, unit], linkPrograms [coreUnit pkg, unit, unit]) of
            (Ok a, Ok b) -> testAssertEq a b
            (Error e, _) -> Just e
            (_, Error e) -> Just e
    , testCase "inconsistent copies cannot share helper unit identity" $ inspectPackage $ \pkg ->
        let p = libPrograms pkg Map.! "lists"
            id0 = libModuleId "lists"
         in rejectedResult "inconsistent units" (linkPrograms [coreUnit pkg, (id0, p), (id0, p{M.progFunctions = Map.delete (nativeHelperName "listPush") (M.progFunctions p)})])
    , testCase "copying a helper body does not confer its provenance" $ inspectPackage $ \pkg ->
        let p = libPrograms pkg Map.! "lists"
            user = p{M.progFunctions = Map.restrictKeys (M.progFunctions p) (Set.singleton (nativeHelperName "listNew"))}
         in rejectedResult "listNew" (linkPrograms [coreUnit pkg, (libModuleId "lists", p), (Modules.ModuleId "app" Nothing, user)])
    , testCase "an imported List invariant still rejects unfilled live slots" (badImportedLayout "fn bad() -> List<Int> { (a, b) = Addr::alloc(0); return List<Int> { addr: a, len: 1, cap: 0, blk: b }; };")
    , testCase "an imported Box invariant still requires one filled slot" (badImportedLayout "fn bad() -> Box<Int> { (a, b) = Addr::alloc(0); return Box<Int> { addr: a, blk: b }; };")
    , testCase "helper declaration seeds and raw tool input share a native phase" $ case Compile.lowerSource True "fn probe<T>(xs: &Box<Array<T>>) -> Int { return size(xs); }; b = Array::boxed(2, 1); return probe(&b);" of
        Error e -> Just e
        Ok p -> case (erasedHelpers, libPackage) of
            (Error e, _) -> Just e
            (_, Error e) -> Just e
            -- (with core's unit, whose Clone the helpers' frames name, as native lowering links them)
            (Ok units, Ok pkg) -> case linkPrograms (units ++ [coreUnit pkg, (Modules.ModuleId "native" Nothing, p)]) of
                Ok _ -> Just "fixture no longer reproduces mixed ghost/native declarations"
                -- (the raw program's generic Box still has its ghost permission, which the helpers' erased one does not)
                Error e | not ((box ++ "<'T> is defined by both") `isInfixOf` e && ghostBox p) -> Just e
                -- (native lowering is given the program pruned to what it reaches, as nativeProgramUsing gives it)
                Error _ -> case lowerLists (Ok units) (pruneProgram p) of
                    Error e -> Just e
                    -- (where the generic Box is the helpers' erased one: a Box of an array is a list in native code)
                    Ok native -> testAssertEq (Map.lookup (box ++ "<'T>") (M.progTypes native)) (Just (M.StructDecl [("addr", TAddr (TParam "T"))]))
    , testCase "generic permission fields are erased before linking, not before validation" $ case libPackage of
        Error e -> Just e
        Ok pkg -> let p = libPrograms pkg Map.! "core"
                      erased = M.completeErasedInstances p
                   in testAssertTrue (Map.lookup box (M.progGenerics p) == Just (["T"], [("addr", TAddr (TParam "T")), ("blk", TBlock (TParam "T"))]) && Map.lookup box (M.progGenerics erased) == Just (["T"], [("addr", TAddr (TParam "T"))]) && M.completeInstances p == p && M.completeErasedInstances erased == erased)
    , testCase "parser owned MIR constructs before guest compilation" (bootstrapOwned "lib/parser/parser.tersus")
    , testCase "emitter owned MIR constructs before guest compilation" (bootstrapOwned "lib/mir/emit/emit.tersus")
    , testCase "imported lent signatures survive until checkMoves" $ importedLoan "xs = [1]; r = headOf(xs); n = size(xs); return *r + n;" False
    , testCase "imported from results still freeze their source" $ importedLoan "xs = [1]; r = headOf(xs); xs = [2]; return *r;" True
    ]
  where
    list = stdName "core/types" "List"
    box = stdName "core/types" "Box"
    dropTrait = stdName "core/ownership" "Drop"
    both (Just err) _ = Just err
    both Nothing other = other
    -- (the units of the helpers name core's List and Box, and the frames of core's Clone of a list, which core's unit has)
    coreUnit pkg = (libModuleId "core", libPrograms pkg Map.! "core")
    ghostBox p = case Map.lookup box (M.progGenerics p) of
        Just (_, fields) -> any (\(_, t) -> case t of TBlock _ -> True; _ -> False) fields
        Nothing -> False
    inspectPackage check = case nativeStorageUnits of
        Error e -> Just e
        Ok native -> case libPackage of
            Error e -> Just e
            Ok pkg -> check pkg
                { libInterfaces = foldr (\(Modules.ModuleId _ (Just name), iface, _) -> Map.insert name iface) (libInterfaces pkg) native
                , libPrograms = foldr (\(Modules.ModuleId _ (Just name), _, p) -> Map.insert name p) (libPrograms pkg) native
                }
    lowerNative source = erasedHelpers `bindResult` \units ->
        Compile.lowerSource False source `bindResult` (lowerLists (Ok units) . pruneProgram)
    erasedHelpers = nativeStorage `bindResult` \(units, _) ->
        flatResultMap (\(modu, p) -> mapResult ((,) modu) (eraseStorageHelper p)) units
    -- (the helpers of a module, by their canonical names)
    selectedHelpers source present absent = case lowerNative source of
        Error e -> Just e
        Ok p -> let of_ modu = [name | name <- Map.keys (M.progFunctions p), ("std$" ++ modu ++ "$" ++ modu ++ "$") `isPrefixOf` name]
                 in if not (null (of_ present)) && null (of_ absent) then Nothing else Just ("helpers: " ++ show (of_ "lists" ++ of_ "box"))
    shadowType name source = case lowerNative source of
        Error e -> Just e
        Ok p -> testAssertEq (Map.lookup name (M.progTypes p)) (Just (M.StructDecl [("x", TInt)]))
    runtimeLayout = case Compile.lowerSource True "xs = [1]; b = Box::new(1); return size(xs) + Box::unbox(b);" of
        Error e -> Just e
        Ok p -> runtimeStorageLayout (M.completeErasedInstances p)
    bootstrapOwned entry = case Modules.loadFromEntry (Modules.resolverFromFiles toolPackageFiles) entry of
        Left e -> Just e
        Right (Modules.PackageResult pkg) -> case Package.compileModules (Modules.packageSnapshot pkg) `bindResult` Package.lowerCompiledPackage of
            Error e -> Just e
            Ok raw -> case (erasedHelpers `bindResult` \units -> expandRefWrites (pruneProgram raw) `bindResult` lowerLists (Ok units)) `bindResult` insertOwnership of
                Error e -> Just e
                Ok owned -> case readProgram (writeProgram owned) of
                    Error e -> Just e
                    -- (the data has the storage record, and none of the other roles or the checked facts)
                    Ok restored -> testAssertEq restored (forNative owned){M.progProtocols = Map.filterWithKey (\role _ -> role `elem` ["List", "Box"]) (M.progProtocols owned), M.progOwnership = Nothing}
        Right _ -> Just "bootstrap fixture is not a package"
    -- (a package that imports core's List and Box by name, read with std from its root: the fixture builds them as their
    -- module does, which only a module that imports the structs by name can)
    badImportedLayout source = case fixturePackage [("app/package.tersus", "noPrelude = true;"), ("app/main.tersus", "import std::core::types { List, Box };\n" ++ source ++ "\nreturn 0;")] of
        Error e -> Just e
        Ok compiled -> rejectedResult "Could not prove" (entryUnit compiled `bindResult` validateLibrary)
    fixturePackage files = case Modules.loadFromEntry (Modules.resolverFromFiles (files ++ [("installed/" ++ path, text) | (path, text) <- libPackageFiles])){Modules.resolverOptions = Modules.defaultLoadOptions{Modules.installedStdRoot = Just "installed/std"}} "app/main.tersus" of
        Left e -> Error e
        Right (Modules.PackageResult pkg) -> Package.compileModules (Modules.packageSnapshot pkg)
        Right _ -> Error "the fixture is not a package"
    -- (the entry module's own unit, finished as the compiler finishes it: its moves and borrows checked)
    entryUnit compiled = case [Package.compiledLowered m | m <- Package.compiledModules compiled, Package.compiledModuleId m == Modules.ModuleId "app" Nothing] of
        [lowered] -> lowered `bindResult` finishLowered
        other -> Error ("the entry module was not lowered once: " ++ show (length other))
    importedLoan source shouldFail = case fixturePackage [("app/package.tersus", ""), ("app/lib/lib.tersus", "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); };"), ("app/main.tersus", "import app::lib { headOf };\n" ++ source)] `bindResult` entryUnit of
        Error e | shouldFail -> testAssertTrue ("borrowed" `isInfixOf` e)
        Error e -> Just e
        Ok _ | shouldFail -> Just "imported from result did not freeze its source"
        Ok p -> testAssertTrue (all (`Map.notMember` M.progFunctions p) ["headOf", "app$lib$lib$headOf"])
    rejectedResult expected result = case result of
        Error e -> if expected `isInfixOf` e then Nothing else Just e
        Ok _ -> Just ("expected rejection containing " ++ expected)

runtimeStorageLayout :: M.Program -> Maybe String
runtimeStorageLayout native = firstFailure
    [ testAssertEq (Map.lookup (list ++ "<Int>") (M.progTypes native)) (Just (M.StructDecl [("addr", TAddr TInt), ("len", TInt), ("cap", TInt)]))
    , testAssertEq (Map.lookup (box ++ "<Int>") (M.progTypes native)) (Just (M.StructDecl [("addr", TAddr TInt)]))
    , testAssertEq (M.fieldOffsets native (list ++ "<Int>")) [0, 8, 16]
    , testAssertEq (M.fieldOffsets native (box ++ "<Int>")) [0]
    , testAssertEq (M.layoutOf native (TNamed list [ArgType TInt]), M.layoutOf native (TNamed box [ArgType TInt])) ((24, 8), (8, 8))
    ]
  where
    list = stdName "core/types" "List"
    box = stdName "core/types" "Box"
    firstFailure results = case [e | Just e <- results] of
        e : _ -> Just e
        [] -> Nothing
