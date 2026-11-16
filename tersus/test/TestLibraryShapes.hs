module TestLibraryShapes (testLibraryShapes) where

import Data.List (isInfixOf)
import qualified Data.ByteString.Char8 as B
import qualified Data.Map.Strict as Map

import Compile (sourceRequest)
import ElaborateRequest
import ElaboratorTool (sourceLoader)
import Modules (LoadOptions (..), Resolver (..), Snapshot (..), defaultLoadOptions, librarySources, loadRequest)
import PackageData (ModuleId (..), resolverFromFiles)
import Utils (Result (..))
import TestHarness
import Interface (ModuleInterface (..))
import Types (Arg (..), OwnershipFacts (..), OwnershipTransport (..), Type (..))

-- The compiler libraries in the shape of the ordinary std package (std::module and std::module::file imports, a module of
-- several files), which the elaborator reads beside the synthetic tersuslib shape the compiler gives it: declarations get
-- the canonical names of package std, a program is given its selected libraries as imports of the names it spells, and
-- the List and Box Drop impls are their owning module's
testLibraryShapes :: Test
testLibraryShapes = TestList "testLibraryShapes"
    [ TestCase "std-shape libraries compile under canonical names with owner Drop facts" stdLibraries
    , TestCase "a program is given std-shape libraries by the names it spells" stdProgram
    , TestCase "a program's own declaration still shadows a std-shape library name" stdShadowed
    , TestCase "the std package's sources write an imported List as the provider it is in struct fields" fullFields
    , TestCase "programs with strings, maps and sets are given the std package's libraries" fullPrograms
    , TestCase "a package module's own Clone impl leaves the std libraries' impls visible, and a struct built with list type arguments is its instance" fullPackageClone
    , TestCase "a std marker's bindings give the libraries their roles" markedLibraries
    , TestCase "a std marker that binds no Box gives core no Box provider, and Box syntax then has none" unboundBox
    , testCase "a package binds a trait of any name to a role, and its List and Clone named alike have no role" $
        case moduleProtocols (bindingPackage "noPrelude = true;\nClone = own::Copyable;\n" "import app::shapes { List, Clone };\nimport app::own { Copyable };\ns = List { n: 3 };\nreturn s.n;") of
            Left e -> Just e
            Right byModule -> testAssertEq (lookup "own" byModule) (Just (Map.fromList [("Clone", ["app$own$own$Copyable"])]))
                <> testAssertEq (fmap (Map.member "List") (lookup "shapes" byModule)) (Just False)
                <> testAssertEq (fmap (Map.member "Clone") (lookup "shapes" byModule)) (Just False)
    , testCase "list syntax in a package that binds no List is refused" $
        refusedWith "List syntax requires its checked provider" (bindingPackage "noPrelude = true;\nClone = own::Copyable;\n" "import app::shapes { List };\nxs = [1, 2];\nreturn size(xs);")
    , testCase "two bindings of one role, both imported, are refused" $
        refusedWith "conflicting Clone providers" (bindingPackage "noPrelude = true;\nClone = own::Copyable;\nClone = shapes::Clone;\n" "import app::shapes { List, Clone };\nimport app::own { Copyable };\nreturn 0;")
    , testCase "a binding that names no declaration of its module is refused" $
        refusedWith "the package binds Clone to own::Missing, which is no trait of the module" (bindingPackage "noPrelude = true;\nClone = own::Missing;\n" "import app::own { Copyable };\nreturn 0;")
    , testCase "a binding of no module of the package and an unknown role are refused by the marker" $
        refusedWith "which is no module of the package" (bindingPackage "noPrelude = true;\nClone = absent::Clone;\n" "return 0;")
            <> refusedWith "package configuration:" (bindingPackage "noPrelude = true;\nHash = own::Copyable;\n" "return 0;")
    , testCase "a binding of List to a trait is refused" $
        refusedWith "the package binds List to own::Copyable, which is no type of the module" (bindingPackage "noPrelude = true;\nList = own::Copyable;\n" "import app::own { Copyable };\nreturn 0;")
    , TestCase "a std root without a package marker is refused" $ do
        sources <- fullSources
        pure $ case sourceLoader (LoadRequestData LoadLibraries False (resolverFromFiles [("installed/std/core/types.tersus", "")]){resolverOptions = defaultLoadOptions{installedStdRoot = Just "installed/std"}} Nothing sources [] (Just Map.empty)) of
            LoadedLibraries [] (Just message) -> testAssertTrue ("package marker not found: installed/std/package.tersus" `isInfixOf` message)
            other -> Just ("the std libraries were not refused: " ++ take 400 (show other))
    , testCase "until the bindings replace them, a package whose marker binds no role keeps the role names (reader stage)" $
        case moduleProtocols (bindingPackage "noPrelude = true;\n" "import app::shapes { List, Clone };\ns = List { n: 3 };\nreturn s.n;") of
            Left e -> Just e
            Right byModule -> testAssertEq (fmap (Map.lookup "Clone") (lookup "shapes" byModule)) (Just (Just ["app$shapes$shapes$Clone"]))
    , testCase "a marker's bindings are part of the load request" $
        testAssertTrue (requestText (bindingPackage "noPrelude = true;\nClone = own::Copyable;\n" "return 0;") /= requestText (bindingPackage "noPrelude = true;\nClone = shapes::Clone;\n" "return 0;"))
    , testCase "libraries of both shapes in one request are refused" mixedShapes
    , testCase "tersuslib-shape libraries keep their bare names" $ case loadLibraries librarySources of
        LoadedLibraries answers Nothing -> testAssertTrue (all (accepted . laResponse) answers)
            <> testAssertTrue (any (\a -> laName a == "types" && not (any ("std$" `isInfixOf`) (mirLines (laResponse a)))) answers)
        other -> Just ("the libraries did not load: " ++ take 400 (show other))
    ]

stdSources :: [(String, Bool, String)]
stdSources =
    [ ("core/ownership", False, unlines
        [ "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };"
        , "trait Copy { };"
        , "trait Drop { fn drop(self: Self) -> Int [{ }] [{ }]; };"
        , "trait Deref<T> { fn deref(self: &Self) -> T [{ }] [{ }]; };"
        ])
    , ("core/types", False, unlines
        [ "import std::core::ownership { Drop };"
        , "struct List<T> { addr: Addr<T>, len: Int, cap: Int, ghost blk: Block<T>, } invariant [{"
        , "    affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = cap; affirm count(blk) = len;"
        , "    affirm len >= 0; affirm len <= cap;"
        , "    affirm forall j in 0..len: filled(blk, j) = true;"
        , "    affirm forall j in len..cap: filled(blk, j) = false;"
        , "}];"
        , "struct Box<T> { addr: Addr<T>, ghost blk: Block<T>, } invariant [{"
        , "    affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 1; affirm filled(blk, 0) = true;"
        , "}];"
        , "impl<T> Drop for List<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, Addr::dropRange(self.addr, 0, self.len, self.blk)); }; };"
        , "impl<T> Drop for Box<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, Addr::dropValue(self.addr, 0, self.blk)); }; };"
        ])
    , ("core/clone", False, unlines
        [ "import std::core::types { List };"
        , "import std::core::ownership { Clone };"
        , "impl<T: Clone> Clone for List<T> {"
        , "    fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }] {"
        , "        out = [];"
        , "        i = 0;"
        , "        while i < size(self) [{ affirm i >= 0; affirm i <= size(self); affirm size(out) = i; affirm forall j in 0..i: get(out, j) = get(self, j); }] shrinks size(self) - i {"
        , "            out = push(out, get(self, i).clone());"
        , "            i = i + 1;"
        , "        };"
        , "        return out;"
        , "    };"
        , "};"
        ])
    , ("eq", False, unlines
        [ "import std::core::types { List };"
        , "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; };"
        , "impl<T: Eq> Eq for List<T> {"
        , "    fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }] {"
        , "        if size(self) != size(other) { return false; };"
        , "        i = 0;"
        , "        while i < size(self) [{ affirm i >= 0; affirm i <= size(self); affirm forall j in 0..i: get(self, j) = get(other, j); }] shrinks size(self) - i {"
        , "            if get(self, i) != get(other, i) { return false; };"
        , "            i = i + 1;"
        , "        };"
        , "        return true;"
        , "    };"
        , "};"
        ])
    ]

loadLibraries :: [(String, Bool, String)] -> LoadResponse
loadLibraries sources = sourceLoader (LoadRequestData LoadLibraries False (resolverFromFiles []) Nothing sources [] (Just Map.empty))

accepted :: Response -> Bool
accepted response = case response of
    Accepted (Just _) _ (MirLowered _) -> True
    _ -> False

mirLines :: Response -> [String]
mirLines response = case response of
    Accepted _ _ (MirLowered ls) -> map B.unpack ls
    _ -> []

-- The libraries as the catalog of a program request, or why they did not load
stdCatalog :: Either String ([LibraryAnswer], [Library])
stdCatalog = case loadLibraries stdSources of
    LoadedLibraries answers Nothing
        | all (accepted . laResponse) answers -> Right (answers, [Library name imports iface | LibraryAnswer name imports _ r@(Accepted (Just iface) _ _) <- answers, accepted r])
        | otherwise -> Left ("a std-shape library was refused: " ++ take 600 (show [(laName a, laResponse a) | a <- answers, not (accepted (laResponse a))]))
    other -> Left ("the std-shape libraries did not load: " ++ take 600 (show other))

listRow :: String
listRow = "std$core$types$List"

stdLibraries :: IO TestResult
stdLibraries = pure $ case stdCatalog of
    Left e -> Just e
    Right (answers, _) ->
        let core = [r | LibraryAnswer "core" _ _ r <- answers]
            facts = [f | r <- core, Just t <- [acceptedOwnership r], Just f <- [Map.lookup listRow (transportOwnership t)]]
         in testAssertEq (map laName answers) ["core", "eq"]
            <> testAssertTrue (any (any (("\"" ++ listRow ++ "\"") `isInfixOf`) . mirLines) core)
            <> case facts of
                [f] -> testAssertEq (fst <$> ownershipDrop f) (Just "std$core$ownership$Drop")
                    <> testAssertTrue (maybe False (("std$core$ownership$Drop" `isInfixOf`) . snd) (ownershipDrop f))
                    <> testAssertEq (fst <$> ownershipClone f) (Just "std$core$ownership$Clone")
                _ -> Just ("the checked facts of core give no single row for " ++ listRow ++ ": " ++ show facts)

stdProgramResponse :: String -> Either String Response
stdProgramResponse source = case stdCatalog of
    Left e -> Left e
    Right (_, catalog) ->
        let request = (sourceRequest LoadProgram False False catalog source){lrSources = stdSources, lrProtocols = Just Map.empty}
         in case sourceLoader request of
                LoadedProgram response -> Right response
                other -> Left ("the program did not load: " ++ take 600 (show other))

stdProgram :: IO TestResult
stdProgram = pure $ case stdProgramResponse "xs = [1, 2]; ys = clone(xs); if xs = ys { return size(ys); }; return 0;" of
    Left e -> Just e
    Right response@(Accepted _ selected _) ->
        testAssertEq selected ["core", "eq"]
            <> testAssertTrue (any (("\"" ++ listRow ++ "\"") `isInfixOf`) (mirLines response))
            <> testAssertTrue (any ("std$core$ownership$Clone" `isInfixOf`) (mirLines response))
            <> testAssertTrue (any ("std$eq$eq$Eq" `isInfixOf`) (mirLines response))
    Right other -> Just ("the program was not accepted: " ++ take 600 (show other))

stdShadowed :: IO TestResult
stdShadowed = pure $ case stdProgramResponse "trait Eq { fn eq(self: &Self, other: &Self) -> Bool [{ }] [{ affirm return = (self = other); }]; }; struct P { a: Int }; impl Eq for P { }; p = P { a: 1 }; if p = p { return 1; }; return 0;" of
    Left e -> Just e
    Right response@(Accepted _ selected _) ->
        testAssertTrue ("eq" `notElem` selected)
            <> testAssertTrue (not (any ("std$eq$eq$Eq" `isInfixOf`) (mirLines response)))
    Right other -> Just ("the program was not accepted: " ++ take 600 (show other))

mixedShapes :: TestResult
mixedShapes = case loadLibraries (take 1 librarySources ++ drop 1 stdSources) of
    LoadedLibraries [] (Just message) -> testAssertTrue ("not in the shape of the libraries before it" `isInfixOf` message)
    other -> Just ("mixed shapes were not refused: " ++ take 400 (show other))

-- The sources of the std package (test/fixtures/std, the package's files as the compiler libraries), in the libraries' order
fullSources :: IO [(String, Bool, String)]
fullSources = mapM (\(name, native) -> (\text -> (name, native, text)) <$> readFile (pathOf name)) order
  where
    order = [("core/ownership", False), ("core/types", False), ("core/clone", False), ("eq", False), ("prelude", False), ("string", False), ("map", False), ("set", False), ("lists", True), ("box", True)]
    pathOf name = "test/fixtures/std/" ++ (if '/' `elem` name then name else name ++ "/" ++ name) ++ ".tersus"

fullCatalog :: [(String, Bool, String)] -> Either String [LibraryAnswer]
fullCatalog sources = case loadLibraries sources of
    LoadedLibraries answers Nothing
        | all (accepted . laResponse) answers -> Right answers
        | otherwise -> Left ("a std library was refused: " ++ take 600 (show [(laName a, laResponse a) | a <- answers, not (accepted (laResponse a))]))
    other -> Left ("the std libraries did not load: " ++ take 600 (show other))

fullFields :: IO TestResult
fullFields = do
    sources <- fullSources
    pure $ case fullCatalog sources of
        Left e -> Just e
        Right answers ->
            let ctor lib name = [fields | LibraryAnswer l _ _ (Accepted (Just iface) _ _) <- answers, l == lib, Just (_, fields) <- [Map.lookup name (ifCtors iface)]]
                list t = TNamed listRow [ArgType t]
             in testAssertEq (ctor "string" "std$string$string$String") [[("bytes", list TByte)]]
                    <> testAssertEq (map (lookup "buckets") (ctor "map" "std$map$map$HashMap<'K, 'V>")) [Just (list (list (TNamed "std$map$map$Entry" [ArgType (TParam "K"), ArgType (TParam "V")])))]

fullPrograms :: IO TestResult
fullPrograms = do
    sources <- fullSources
    pure $ case fullCatalog sources of
        Left e -> Just e
        Right answers ->
            let catalog = [Library name imports iface | LibraryAnswer name imports _ (Accepted (Just iface) _ _) <- answers]
                load source = sourceLoader ((sourceRequest LoadProgram False False catalog source){lrSources = sources, lrProtocols = Just Map.empty})
                given source expected = case load source of
                    LoadedProgram (Accepted _ selected (MirLowered _)) -> testAssertTrue (all (`elem` selected) expected)
                    other -> Just ("the program was not accepted: " ++ take 600 (show other))
             in given "s = \"ab\"; t = clone(s); c = \"c\"; u = t.concat(&c); return size(u.bytes);" ["string"]
                    <> given "m = HashMap::new(); m = m.insert(1, 2); s = HashSet::new(); s = s.insert(3); k = 1; return m.size() + s.size() + m.lookup(&k, 0);" ["map", "set"]

fullPackageClone :: IO TestResult
fullPackageClone = do
    sources <- fullSources
    pure $ case fullCatalog sources of
        Left e -> Just e
        Right answers ->
            let catalog = [Library name imports iface | LibraryAnswer name imports _ (Accepted (Just iface) _ _) <- answers]
                files = [("app/package.tersus", ""), ("app/main.tersus", "struct T { a: Int };\nimpl Clone for T { };\nstruct W<E> { v: E };\nenum Shape { Ring { xs: List<Int> }, Dot { } };\nfn ringSize(s: Shape) -> Int { if s is Shape::Ring { r = s as Shape::Ring; return size(r.xs); }; return 0; };\nt = clone(T { a: 1 });\ns = \"ab\";\nu = clone(s);\nw = W<List<Int>> { v: [1, 2] };\nreturn size(u.bytes) + t.a + size(w.v);\n")]
                request = (loadRequest LoadPackage (Snapshot (resolverFromFiles files) "app/main.tersus" False)){lrSources = sources, lrLibraries = catalog, lrProtocols = Just Map.empty}
             in case sourceLoader request of
                    LoadedModules modules -> testAssertTrue (not (null modules) && and [case r of Accepted _ _ (MirLowered _) -> True; _ -> False | (_, _, r) <- modules])
                        <> testAssertEq [take 200 (show r) | (_, _, r) <- modules, case r of Accepted _ _ (MirLowered _) -> False; _ -> True] []
                        <> testAssertEq [fields | (_, _, Accepted (Just iface) _ _) <- modules, Just (_, fields) <- [Map.lookup "Shape::Ring" (ifCtors iface)]] [[("xs", TNamed listRow [ArgType TInt])]]
                    other -> Just ("the package did not load: " ++ take 600 (show other))

-- The std package's marker, binding each role to its declaration in core and eq
stdMarker :: String
stdMarker = "noPrelude = true;\nList = core::types::List;\nBox = core::types::Box;\nClone = core::ownership::Clone;\nCopy = core::ownership::Copy;\nDrop = core::ownership::Drop;\nDeref = core::ownership::Deref;\nEq = eq::Eq;\n"

loadMarked :: String -> [(String, Bool, String)] -> LoadResponse
loadMarked marker sources = sourceLoader (LoadRequestData LoadLibraries False (resolverFromFiles [("installed/std/package.tersus", marker)]){resolverOptions = defaultLoadOptions{installedStdRoot = Just "installed/std"}} Nothing sources [] (Just Map.empty))

markedLibraries :: IO TestResult
markedLibraries = do
    sources <- fullSources
    pure $ case (loadMarked stdMarker sources, fullCatalog sources) of
        (LoadedLibraries answers Nothing, Right legacy) ->
            let protocols as = [(laName a, fmap transportProtocols (acceptedOwnership (laResponse a))) | a <- as]
             in testAssertTrue (all (accepted . laResponse) answers)
                    <> testAssertEq (lookup "core" (protocols answers)) (Just (Just (Map.fromList [(role, [provider]) | (role, provider) <- [("Box", "std$core$types$Box"), ("Clone", "std$core$ownership$Clone"), ("Copy", "std$core$ownership$Copy"), ("Deref", "std$core$ownership$Deref"), ("Drop", "std$core$ownership$Drop"), ("List", "std$core$types$List")]])))
                    <> testAssertEq (protocols answers) (protocols legacy)
        (other, _) -> Just ("the marked std libraries did not load: " ++ take 600 (show other))

unboundBox :: IO TestResult
unboundBox = do
    sources <- fullSources
    let marker = unlines [l | l <- lines stdMarker, take 3 l /= "Box"]
    pure $ case loadMarked marker sources of
        LoadedLibraries answers _ ->
            let core = [r | LibraryAnswer "core" _ _ r <- answers]
             in testAssertTrue (any (\r -> case r of Refused m -> "Box syntax requires its checked provider" `isInfixOf` m; _ -> False) core)
        other -> Just ("the std libraries did not answer: " ++ take 600 (show other))

-- A noPrelude package app with the marker, a module own with a trait Copyable, a module shapes with a struct List and a
-- trait Clone, and main
bindingPackage :: String -> String -> LoadRequest
bindingPackage marker source = (loadRequest LoadPackage (Snapshot (resolverFromFiles files) "app/main.tersus" False)){lrProtocols = Just Map.empty}
  where
    files =
        [ ("app/package.tersus", marker)
        , ("app/own/own.tersus", "trait Copyable { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };")
        , ("app/shapes/shapes.tersus", "struct List { n: Int };\ntrait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; };")
        , ("app/main.tersus", source)
        ]

moduleProtocols :: LoadRequest -> Either String [(String, Map.Map String [String])]
moduleProtocols request = case sourceLoader request of
    LoadedModules modules
        | all (\(_, _, r) -> accepted' r) modules -> Right [(maybe "" id (moduleName m), maybe Map.empty transportProtocols (acceptedOwnership r)) | (m, _, r) <- modules]
        | otherwise -> Left ("a module was refused: " ++ take 600 (show [r | (_, _, r) <- modules, not (accepted' r)]))
    other -> Left ("the package did not load: " ++ take 600 (show other))
  where
    accepted' r = case r of
        Accepted _ _ (MirLowered _) -> True
        _ -> False

refusedWith :: String -> LoadRequest -> TestResult
refusedWith needle request = case sourceLoader request of
    LoadedModules modules -> testAssertTrue (any (\(_, _, r) -> refusal r) modules)
    NotLoaded m -> testAssertTrue (needle `isInfixOf` m)
    other -> Just ("expected a refusal containing " ++ needle ++ ": " ++ take 600 (show other))
  where
    refusal r = case r of
        Refused m -> needle `isInfixOf` m
        Unresolved m -> needle `isInfixOf` m
        _ -> False

requestText :: LoadRequest -> String
requestText request = case writeLoadRequest request of
    Ok text -> text
    Error e -> e
