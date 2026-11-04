module TestLibModules (testLibModules, testNativeStorageModules) where

import Control.Exception (bracket, evaluate)
import System.Environment (lookupEnv, setEnv, unsetEnv)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import qualified Compile
import qualified Modules
import qualified Parse
import PreludeSource (eqSource, listsSource, boxSource)
import qualified Mir as M
import MirValidate (validateContainerLibrary, validateProgram)
import PackageCompile (compileModulesValidated)
import Interface (ModuleInterface (..), extractLibInterface, interfaceImportEnv, mergeInterfacesImportEnv, predeclareOwnEnv)
import MirLower (lowerModuleWith)
import TypeCheck (ImportEnv (..), Elaborated (..), elaborateWith)
import LibPackage (LibPackage (..), libPackage, libModuleId, libSelection, nativeStorageUnits)
import LibParsed (LibParsed (..), libParsed, nativeLibParsed, libPackageFiles)
import Link (linkPrograms)
import MirHousekeeping (validatedListLibrary)
import MirLists (lowerLists)
import Types (Arg (..), Type (..), Size (..))
import MirEval (fromMirValue, runProgram)
import Pipeline (compileSource, ownedSource, erasedModuleProgram, ownedModuleProgram)
import Syntax (Value (..))
import TestHarness (Test (..), forceTestResult, testAssertEq, testAssertTrue, testCase)
import TestStorageOracle (eraseStorageHelper)
import qualified PackageCompile as Package
import PreludeSource (toolPackageFiles)
import MirOwnership (expandRefWrites, insertOwnership)
import MirData (forNative, readProgram, writeProgram)
import MirHousekeeping (validatedStorage)
import Utils (Result (..), bindResult, flatResultMap, mapResult)

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
             , testCase "production helper linking retains runtime layouts" $ case ownedSource "xs = [1]; b = Box::new(1); return size(xs) + Box::unbox(b);" of
                Error e -> Just e
                Ok p -> runtimeStorageLayout p
             , testCase "package custom Box survives the production list-helper link" $ case checkedPackage "struct Box { x: Int }; b = Box { x: 3 }; xs = [1]; return b.x + size(xs);" `bindResult` erasedModuleProgram `bindResult` ownedModuleProgram of
                Error e -> Just e
                Ok p -> both (testAssertEq (Map.lookup "Box" (M.progTypes p)) (Just (M.StructDecl [("x", TInt)]))) (testAssertTrue (Map.notMember "boxNew" (M.progFunctions p)))
             , testCase "package entry helper names are reserved even without storage" (rejected (checkedPackage "fn listNew() -> Int { return 7; }; return 1;") "listNew is reserved")
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
        Ok pkg -> testAssertEq (libOrder pkg) ["types", "clone", "eq", "prelude", "string", "map", "set"]
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
        testAssertEq (map (\path -> lookup path libPackageFiles) ["tersuslib/lists/lists.tersus", "tersuslib/box/box.tersus"]) [Just listsSource, Just boxSource]
    , testCase "native imports are the compiled dependency graph" $ case nativeLibParsed of
        Left e -> Just e
        Right parsed -> testAssertEq (map (\name -> Map.lookup name (lpDependencies parsed)) ["lists", "box"]) [Just ["types", "prelude"], Just ["types", "prelude"]]
    , testCase "user-library parsing and compilation exclude native modules" $ case (libParsed, libPackage) of
        (Right parsed, Ok pkg) -> testAssertTrue (all (\name -> Map.notMember name (lpStatements parsed) && Map.notMember name (libPrograms pkg)) ["lists", "box"])
        (Left e, _) -> Just e
        (_, Error e) -> Just e
    , testCase "physical generic constructor owners are not user import types" $ case libPackage of
        Error e -> Just e
        Ok pkg -> let env = interfaceImportEnv (libInterfaces pkg Map.! "types")
                   in testAssertTrue (all (`Map.notMember` ieTypes env) ["List<'T>", "Box<'T>"])
    , testCase "implicit types expose no native Drop implementations" $ inspectPackage $ \pkg ->
        let iface = libInterfaces pkg Map.! "types"
         in testAssertTrue (Set.null (ifDrops iface) && Map.null (ifFunctions iface))
    , testCase "implicit selection never reaches helper interfaces or units" $ inspectPackage $ \pkg ->
        let (ifaces, units) = libSelection pkg ["types", "prelude", "string", "map", "set"]
         in testAssertTrue (all (\name -> libModuleId name `notElem` map ifModule ifaces ++ map fst units) ["lists", "box"])
    , testCase "each helper owns only its declared Drop implementation" $ inspectPackage $ \pkg ->
        testAssertEq [ifImpls (libInterfaces pkg Map.! name) | name <- ["lists", "box"]] [Set.singleton ("Drop", "List"), Set.singleton ("Drop", "Box")]
    , testCase "helper declarations use the authoritative type interfaces" $ inspectPackage $ \pkg ->
        let types = libPrograms pkg Map.! "types"
         in testAssertTrue (all (\name -> let p = libPrograms pkg Map.! name in M.progGenerics p == M.progGenerics types && M.progInvariants p == M.progInvariants types) ["lists", "box"])
    , testCase "linked helper contracts meet physical-container proofs" $ case validateContainerLibrary validatedListLibrary of
        Error e -> Just e
        Ok _ -> Nothing
    , testCase "erased List and Box instances retain exact fields and offsets" runtimeLayout
    , testCase "native lowering is a no-op without storage and does not force helpers" $ case Compile.lowerSource True "return 7;" of
        Error e -> Just e
        Ok p -> case lowerLists (error "unused helper graph forced") p of
            Error e -> Just e
            Ok native -> testAssertEq native p
    , testCase "a list selects only list helpers" (selectedHelpers "return [1];" "listNew" "boxNew")
    , testCase "a scalar Box selects only Box helpers" (selectedHelpers "return Box::unbox(Box::new(3));" "boxNew" "listNew")
    , testCase "an array-backed Box selects list helpers" (selectedHelpers "return Box::unbox(Box::new(#[1, 2]));" "listNew" "boxNew")
    , testCase "custom Box is preserved when only lists need storage" (shadowType "Box" "struct Box { x: Int }; b = Box { x: 3 }; xs = [1]; return b.x + size(xs);")
    , testCase "custom List is preserved when only Boxes need storage" (shadowType "List" "struct List { x: Int }; l = List { x: 3 }; b = Box::new(4); return l.x + Box::unbox(b);")
    , testCase "repeated identical helper units link once" $ inspectPackage $ \pkg ->
        let unit = (libModuleId "lists", libPrograms pkg Map.! "lists")
         in case (linkPrograms [unit], linkPrograms [unit, unit]) of
            (Ok a, Ok b) -> testAssertEq a b
            (Error e, _) -> Just e
            (_, Error e) -> Just e
    , testCase "inconsistent copies cannot share helper unit identity" $ inspectPackage $ \pkg ->
        let p = libPrograms pkg Map.! "lists"
            id0 = libModuleId "lists"
         in rejectedResult "inconsistent units" (linkPrograms [(id0, p), (id0, p{M.progFunctions = Map.delete "listPush" (M.progFunctions p)})])
    , testCase "copying a helper body does not confer its provenance" $ inspectPackage $ \pkg ->
        let p = libPrograms pkg Map.! "lists"
            user = p{M.progFunctions = Map.restrictKeys (M.progFunctions p) (Set.singleton "listNew")}
         in rejectedResult "listNew" (linkPrograms [(libModuleId "lists", p), (Modules.ModuleId "app" Nothing, user)])
    , testCase "an imported List invariant still rejects unfilled live slots" (badImportedLayout "fn bad() -> List<Int> { (a, b) = Addr::alloc(0); return List<Int> { addr: a, len: 1, cap: 0, blk: b }; };")
    , testCase "an imported Box invariant still requires one filled slot" (badImportedLayout "fn bad() -> Box<Int> { (a, b) = Addr::alloc(0); return Box<Int> { addr: a, blk: b }; };")
    , testCase "helper declaration seeds and raw tool input share a native phase" $ case Compile.lowerSource True "fn probe<T>(xs: &Box<Array<T>>) -> Int { return size(xs); }; return 0;" of
        Error e -> Just e
        Ok p -> case erasedHelpers of
            Error e -> Just e
            Ok units -> case linkPrograms (units ++ [(Modules.ModuleId "native" Nothing, p)]) of
                Ok _ -> Just "fixture no longer reproduces mixed ghost/native declarations"
                Error e | not ("type Box<Array<'T, ?>>" `isInfixOf` e) -> Just e
                Error _ -> case lowerLists (Ok units) p of
                    Error e -> Just e
                    Ok native -> testAssertEq (Map.lookup "Box<Array<'T, ?>>" (M.progTypes native)) (Just (M.StructDecl [("addr", TAddr (TArrayOf (TParam "T") SizeAny))]))
    , testCase "generic permission fields are erased before linking, not before validation" $ case libPackage of
        Error e -> Just e
        Ok pkg -> let p = libPrograms pkg Map.! "types"
                      erased = M.completeErasedInstances p
                   in testAssertTrue (Map.lookup "Box" (M.progGenerics p) == Just (["T"], [("addr", TAddr (TParam "T")), ("blk", TBlock (TParam "T"))]) && Map.lookup "Box" (M.progGenerics erased) == Just (["T"], [("addr", TAddr (TParam "T"))]) && M.completeInstances p == p && M.completeErasedInstances erased == erased)
    , testCase "parser owned MIR constructs before guest compilation" (bootstrapOwned "examples/parser/parser.tersus")
    , testCase "emitter owned MIR constructs before guest compilation" (bootstrapOwned "examples/mir/emit/emit.tersus")
    , testCase "imported lent signatures survive until checkMoves" $ importedLoan "xs = [1]; r = headOf(xs); n = size(xs); return *r + n;" False
    , testCase "imported from results still freeze their source" $ importedLoan "xs = [1]; r = headOf(xs); xs = [2]; return *r;" True
    ]
  where
    inspectPackage check = case nativeStorageUnits of
        Error e -> Just e
        Ok native -> case libPackage of
            Error e -> Just e
            Ok pkg -> check pkg
                { libInterfaces = foldr (\(Modules.ModuleId _ (Just name), iface, _) -> Map.insert name iface) (libInterfaces pkg) native
                , libPrograms = foldr (\(Modules.ModuleId _ (Just name), _, p) -> Map.insert name p) (libPrograms pkg) native
                }
    lowerNative source = erasedHelpers `bindResult` \units ->
        Compile.lowerSource False source `bindResult` lowerLists (Ok units)
    erasedHelpers = validatedStorage `bindResult` \(units, _) ->
        flatResultMap (\(modu, p) -> mapResult ((,) modu) (eraseStorageHelper p)) units
    selectedHelpers source present absent = case lowerNative source of
        Error e -> Just e
        Ok p -> testAssertTrue (Map.member present (M.progFunctions p) && Map.notMember absent (M.progFunctions p))
    shadowType name source = case lowerNative source of
        Error e -> Just e
        Ok p -> testAssertEq (Map.lookup name (M.progTypes p)) (Just (M.StructDecl [("x", TInt)]))
    runtimeLayout = case Compile.lowerSource True "xs = [1]; b = Box::new(1); return size(xs) + Box::unbox(b);" of
        Error e -> Just e
        Ok p -> runtimeStorageLayout (M.completeErasedInstances p)
    bootstrapOwned entry = case Modules.loadFromEntry (Modules.resolverFromFiles toolPackageFiles) entry of
        Left e -> Just e
        Right (Modules.PackageResult pkg) -> case Package.compileModules pkg `bindResult` Package.lowerCompiledPackage pkg of
            Error e -> Just e
            Ok raw -> case erasedHelpers `bindResult` \units -> lowerLists (Ok units) (expandRefWrites raw) of
                Error e -> Just e
                Ok native ->
                    let owned = insertOwnership native
                     in case readProgram (writeProgram owned) of
                        Error e -> Just e
                        Ok restored -> testAssertEq restored (forNative owned)
        Right _ -> Just "bootstrap fixture is not a package"
    badImportedLayout source = case fixtureModule source of
        Error e -> Just e
        Ok (_, p) -> rejectedResult "does not meet its invariant" (validateContainerLibrary p)
    fixtureModule source = libPackage `bindResult` \pkg ->
        let ifaces = [libInterfaces pkg Map.! name | name <- ["types", "prelude", "clone"]]
         in checkedModule ifaces source
    checkedModule ifaces source = case libParsed of
        Left e -> Error e
        Right parsed -> case Parse.parseFileWith (lpDecls parsed) source of
            Left e -> Error (show e)
            Right (Parse.ParsedFile _ stmts, _) ->
                let env = mergeInterfacesImportEnv ifaces
                 in elaborateWith (predeclareOwnEnv env) stmts `bindResult` \(elaborated@(Elaborated body _), state) ->
                    extractLibInterface (Modules.ModuleId "fixture" Nothing) stmts body state `bindResult` \iface ->
                        lowerModuleWith env ifaces elaborated `bindResult` \p -> Ok (iface, p)
    importedLoan source shouldFail = case fixtureModule "fn headOf(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); };" of
        Error e -> Just e
        Ok (iface, _) -> libCheck iface
      where
        libCheck iface = case libPackage of
            Error e -> Just e
            Ok pkg -> case checkedModule [libInterfaces pkg Map.! "types", iface] source of
                Error e | shouldFail -> testAssertTrue ("borrowed" `isInfixOf` e)
                Error e -> Just e
                Ok _ | shouldFail -> Just "imported from result did not freeze its source"
                Ok (_, p) -> testAssertTrue (Map.notMember "headOf" (M.progFunctions p))
    rejectedResult expected result = case result of
        Error e -> if expected `isInfixOf` e then Nothing else Just e
        Ok _ -> Just ("expected rejection containing " ++ expected)

runtimeStorageLayout :: M.Program -> Maybe String
runtimeStorageLayout native = firstFailure
    [ testAssertEq (Map.lookup "List<Int>" (M.progTypes native)) (Just (M.StructDecl [("addr", TAddr TInt), ("len", TInt), ("cap", TInt)]))
    , testAssertEq (Map.lookup "Box<Int>" (M.progTypes native)) (Just (M.StructDecl [("addr", TAddr TInt)]))
    , testAssertEq (M.fieldOffsets native "List<Int>") [0, 8, 16]
    , testAssertEq (M.fieldOffsets native "Box<Int>") [0]
    , testAssertEq (M.layoutOf native (TNamed "List" [ArgType TInt]), M.layoutOf native (TNamed "Box" [ArgType TInt])) ((24, 8), (8, 8))
    ]
  where
    firstFailure results = case [e | Just e <- results] of
        e : _ -> Just e
        [] -> Nothing
