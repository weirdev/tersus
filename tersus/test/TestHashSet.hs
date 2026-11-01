module TestHashSet (testHashSet) where

import MirEval (fromMirValue)
import Pipeline (parseSource, runStatements, validateStatements)
import Types
import Syntax
import Solver
import TestHarness
import Utils

-- HashSet: a set of keys in lib/set.tersus, made of a HashMap to Bool. The programs are read as the command
-- line reads them (the set and map libraries are put in front by the pipeline, and the programs are validated
-- as they run), so membership is asserted by running it: that an inserted key is found is true when a set runs,
-- and these tests say so, but no contract of the library lets a caller prove it (see lib/set.tersus).
testHashSet :: Test
testHashSet =
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
     in TestList
            "testHashSet"
            [ TestList
                "insert and contains"
                [ testCase "an empty set" (runs "s = HashSet::new(); if s.contains(1) { return 1; }; return s.size();" 0)
                , testCase "inserted and found" (runs "s = HashSet::new().insert(1).insert(2); a = s.contains(1); b = s.contains(3); if a { if b { return 3; }; return 1; }; return 0;" 1)
                , testCase "inserting again adds nothing" (runs "s = HashSet::new().insert(1).insert(1); return s.size();" 1)
                , testCase "negative keys" (runs "s = HashSet::new().insert(0 - 5).insert(-2147483647); a = s.contains(0 - 5); b = s.contains(-2147483647); if a { if b { return 11; }; return 1; }; return 0;" 11)
                , testCase "string keys" (runs "s = HashSet::new().insert(\"one\").insert(\"two\").insert(\"one\"); a = s.contains(\"two\"); if a { return s.size() * 10 + 1; }; return 0;" 21)
                , testCase "the count after insert is bounded" (valid "fn addOne(s: HashSet<Int>, k: Int) -> Int [{ }] [{ affirm return >= size(s); affirm return <= size(s) + 1; }] { return s.insert(k).size(); }; return 0;")
                ]
            , TestList
                "remove"
                [ testCase "removed and not found" (runs "s = HashSet::new().insert(1).insert(2).remove(1); r = s.size() * 100; if s.contains(1) { r = r + 10; }; if s.contains(2) { r = r + 1; }; return r;" 101)
                , testCase "remove a missing key" (runs "s = HashSet::new().insert(1).remove(9); r = s.size() * 10; if s.contains(1) { r = r + 1; }; return r;" 11)
                , testCase "remove and insert again" (runs "s = HashSet::new().insert(1).remove(1).insert(1); r = s.size() * 10; if s.contains(1) { r = r + 1; }; return r;" 11)
                ]
            , TestList
                "elements"
                [ testCase "every key, in some order" (runs "s = HashSet::new().insert(1).insert(2).insert(1); t = 0; for k in s.elements() { t = t + k * 10; }; return t + size(s.elements()) * 100 + s.size();" 232)
                , testCase "past the spread, everything is found" (runs "s = HashSet::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { s = s.insert(i); i = i + 1; }; t = 0; for k in s.elements() { t = t + k; }; return s.size() * 10000 + t;" 400780)
                , testCase "removed after the spread" (runs "s = HashSet::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { s = s.insert(i); i = i + 1; }; s = s.remove(0).remove(39); r = s.size() * 100; if s.contains(0) { r = r + 10; }; if s.contains(20) { r = r + 1; }; return r;" 3801)
                ]
            ]
