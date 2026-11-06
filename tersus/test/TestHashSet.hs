module TestHashSet (testHashSet) where

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
    TestList
            "testHashSet"
            [ TestList
                "insert and contains"
                [ testCase "an empty set" (pipelineRuns "s = HashSet::new(); if s.contains(1) { return 1; }; return s.size();" (VInt 0))
                , testCase "inserted and found" (pipelineRuns "s = HashSet::new().insert(1).insert(2); a = s.contains(1); b = s.contains(3); if a { if b { return 3; }; return 1; }; return 0;" (VInt 1))
                , testCase "inserting again adds nothing" (pipelineRuns "s = HashSet::new().insert(1).insert(1); return s.size();" (VInt 1))
                , testCase "negative keys" (pipelineRuns "s = HashSet::new().insert(0 - 5).insert(-2147483647); a = s.contains(0 - 5); b = s.contains(-2147483647); if a { if b { return 11; }; return 1; }; return 0;" (VInt 11))
                , testCase "string keys" (pipelineRuns "s = HashSet::new().insert(\"one\").insert(\"two\").insert(\"one\"); a = s.contains(\"two\"); if a { return s.size() * 10 + 1; }; return 0;" (VInt 21))
                , testCase "the count after insert is bounded" (pipelineValid "fn addOne(s: HashSet<Int>, k: Int) -> Int [{ }] [{ affirm return >= size(s); affirm return <= size(s) + 1; }] { return s.insert(k).size(); }; return 0;")
                ]
            , TestList
                "remove"
                [ testCase "removed and not found" (pipelineRuns "s = HashSet::new().insert(1).insert(2).remove(1); r = s.size() * 100; if s.contains(1) { r = r + 10; }; if s.contains(2) { r = r + 1; }; return r;" (VInt 101))
                , testCase "remove a missing key" (pipelineRuns "s = HashSet::new().insert(1).remove(9); r = s.size() * 10; if s.contains(1) { r = r + 1; }; return r;" (VInt 11))
                , testCase "remove and insert again" (pipelineRuns "s = HashSet::new().insert(1).remove(1).insert(1); r = s.size() * 10; if s.contains(1) { r = r + 1; }; return r;" (VInt 11))
                ]
            , TestList
                "elements"
                [ testCase "every key, in some order" (pipelineRuns "s = HashSet::new().insert(1).insert(2).insert(1); t = 0; for k in s.elements() { t = t + k * 10; }; return t + size(s.elements()) * 100 + s.size();" (VInt 232))
                , testCase "removed after the spread" (pipelineRuns "s = HashSet::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { s = s.insert(i); i = i + 1; }; s = s.remove(0).remove(39); r = s.size() * 100; if s.contains(0) { r = r + 10; }; if s.contains(20) { r = r + 1; }; return r;" (VInt 3801))
                ]
            , TestList
                "elements by reference"
                [ testCase "every key by reference, in some order" (pipelineRuns "s = HashSet::new().insert(1).insert(2).insert(1); t = 0; n = 0; total = s.size(); while n < total [{ affirm n >= 0; affirm n <= total; }] shrinks total - n { k = s.elementRef(n); t = t + *k * 10; n = n + 1; }; return t + total * 100 + s.size();" (VInt 232))
                , testCase "elementRef where the key is a precondition" (pipelineValid "fn useIt(s: &HashSet<Int>) -> Int [{ affirm size(s.map.buckets) >= 1; affirm findNth(s.map.buckets, 1).1 >= 0; }] [{ }] { k = s.elementRef(1); return *k; }; return 0;")
                , testCase "the set cannot be moved while an elementRef is live" (pipelineRejected "fn bad(s: HashSet<Int>) -> Int [{ affirm size(s.map.buckets) >= 1; affirm findNth(s.map.buckets, 0).1 >= 0; }] [{ }] { k = s.elementRef(0); s = s.insert(9); return *k; }; return 0;" "cannot be moved while that borrow is live")
                ]
            ]
