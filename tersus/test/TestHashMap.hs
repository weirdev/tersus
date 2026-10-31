module TestHashMap (testHashMap) where

import Data.List (isInfixOf)

import MirEval (fromMirValue)
import Pipeline (parseSource, runStatements, validateStatements)
import TersusTypes
import TestHarness
import Utils

-- HashMap: a map from keys to values in lib/map.tersus, its operations, and what its contracts do and do not say.
-- The programs are read as the command line reads them (the map library is put in front by the pipeline, and the
-- programs are validated as they run), so a lookup is asserted with lookup and a fallback: that an inserted key is
-- found is true when a map runs, and these tests say so, but fetch after an insert asks a caller to prove it and
-- cannot be written here (see lib/map.tersus). fetch is tested where its precondition is a function's own.
testHashMap :: Test
testHashMap =
    let runs source expected = case parseSource source of
            Error e -> Just ("Parse failed: " ++ e)
            Ok stmts -> case runStatements stmts of
                Ok result -> testAssertEq (fmap fromMirValue result) (Just (VInt expected))
                Error e -> Just ("Evaluation failed with error: " ++ e)
        valid source = case parseSource source of
            Error e -> Just ("Parse failed: " ++ e)
            Ok stmts -> case validateStatements stmts of
                Ok _ -> Nothing
                Error e -> Just ("Validation failed with error: " ++ e)
        rejected source expected = case parseSource source of
            Error e -> if expected `isInfixOf` e then Nothing else Just ("Expected failure containing: " ++ show expected ++ "\nGot: " ++ e)
            Ok stmts -> testAssertErrorContains expected (validateStatements stmts)
     in TestList
            "testHashMap"
            [ TestList
                "insert and lookup"
                [ testCase "an empty map" (runs "m = HashMap::new(); return m.size() * 10 + m.lookup(1, 7);" 7)
                , testCase "inserted and read back" (runs "m = HashMap::new().insert(1, 100).insert(2, 200); return m.lookup(1, 0) + m.lookup(2, 0);" 300)
                , testCase "a missing key is the fallback" (runs "m = HashMap::new().insert(1, 100); return m.lookup(9, 7);" 7)
                , testCase "insert at a key replaces it" (runs "m = HashMap::new().insert(1, 100).insert(1, 111); return m.lookup(1, 0) * 10 + m.size();" 1111)
                , testCase "contains" (runs "m = HashMap::new().insert(1, 100); a = m.contains(1); b = m.contains(2); if a { if b { return 3; }; return 1; }; return 0;" 1)
                , testCase "negative keys" (runs "m = HashMap::new().insert(0 - 5, 50).insert(-2147483647, 60); return m.lookup(0 - 5, 0) + m.lookup(-2147483647, 0);" 110)
                ]
            , TestList
                "remove"
                [ testCase "removed and not found" (runs "m = HashMap::new().insert(1, 100).insert(2, 200).remove(1); return m.lookup(1, 7) * 100 + m.lookup(2, 0) + m.size();" 901)
                , testCase "remove a missing key" (runs "m = HashMap::new().insert(1, 100).remove(9); return m.lookup(1, 0) * 10 + m.size();" 1001)
                , testCase "remove and insert again" (runs "m = HashMap::new().insert(1, 100).remove(1).insert(1, 300); return m.lookup(1, 0) + m.size();" 301)
                ]
            , TestList
                "keys and values"
                [ testCase "string keys" (runs "m = HashMap::new().insert(\"one\", 1).insert(\"two\", 2).insert(\"one\", 11); return m.lookup(\"one\", 0) * 100 + m.lookup(\"two\", 0) * 10 + m.size();" 1122)
                , testCase "struct keys with their own Hash" (runs "struct Point { x: Int, y: Int }; impl Clone for Point { }; impl Eq for Point { }; impl Hash for Point { fn hash(self: &Self) -> Int [{ }] [{ affirm return >= 0; affirm return < 2147483647; }] { return hashCombine(hashCombine(3, self.x), self.y); }; }; m = HashMap::new().insert(Point { x: 1, y: 2 }, 12).insert(Point { x: 3, y: 4 }, 34); return m.lookup(Point { x: 1, y: 2 }, 0) * 100 + m.lookup(Point { x: 3, y: 4 }, 0);" 1234)
                , testCase "values that own lists" (runs "m = HashMap::new().insert(1, push(push([], 10), 20)).insert(2, push([], 30)); a = m.lookup(1, []); b = m.lookup(2, []); return size(a) * 100 + size(b) * 10 + get(b, 0);" 240)
                , testCase "a map in a map" (runs "inner = HashMap::new().insert(1, 5); m = HashMap::new().insert(9, inner); return m.lookup(9, HashMap::new()).lookup(1, 0);" 5)
                ]
            , TestList
                "growth"
                [ testCase "past the spread, everything is found" (runs "m = HashMap::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { m = m.insert(i, i * 2); i = i + 1; }; s = 0; j = 0; while j < 40 [{ affirm j >= 0; affirm j <= 40; }] shrinks 40 - j { s = s + m.lookup(j, 0 - 1); j = j + 1; }; return m.size() * 10000 + s;" 401560)
                , testCase "removed after the spread" (runs "m = HashMap::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { m = m.insert(i, i); i = i + 1; }; m = m.remove(0).remove(39).remove(20); return m.size() * 100 + m.lookup(0, 7) * 10 + m.lookup(20, 8);" 3778)
                ]
            , TestList
                "contracts"
                [ testCase "fetch where the key is a precondition" (valid "fn getIt(m: &HashMap<Int, Int>, k: &Int) -> Int [{ affirm findIn(get(m.buckets, Hash::hash(k) % size(m.buckets)), k) >= 0; }] [{ }] { return m.fetch(k); }; return 0;")
                , testCase "a key type without Hash is refused" (rejected "struct Plain { x: Int }; impl Clone for Plain { }; m = HashMap::new().insert(Plain { x: 1 }, 2); return m.size();" "needs K to implement Hash")
                , testCase "the count after insert is bounded" (valid "fn addOne(m: HashMap<Int, Int>, k: Int, v: Int) -> Int [{ }] [{ affirm return >= size(m); affirm return <= size(m) + 1; }] { return m.insert(k, v).size(); }; return 0;")
                ]
            ]
