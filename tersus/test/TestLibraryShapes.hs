module TestLibraryShapes (testLibraryShapes) where

import Data.List (isInfixOf)
import qualified Data.ByteString.Char8 as B
import qualified Data.Map.Strict as Map

import Compile (sourceRequest)
import ElaborateRequest
import ElaboratorTool (sourceLoader)
import Modules (librarySources)
import PackageData (resolverFromFiles)
import TestHarness
import Types (OwnershipFacts (..), OwnershipTransport (..))

-- The compiler libraries in the shape of the ordinary std package (std::module and std::module::file imports, a module of
-- several files), which the elaborator reads beside the synthetic tersuslib shape the compiler gives it: declarations get
-- the canonical names of package std, a program is given its selected libraries as imports of the names it spells, and
-- the List and Box Drop impls are their owning module's
testLibraryShapes :: Test
testLibraryShapes = TestList "testLibraryShapes"
    [ TestCase "std-shape libraries compile under canonical names with owner Drop facts" stdLibraries
    , TestCase "a program is given std-shape libraries by the names it spells" stdProgram
    , TestCase "a program's own declaration still shadows a std-shape library name" stdShadowed
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
