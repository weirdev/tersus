module TestHashMap (testHashMap) where

import Types
import Syntax
import Solver
import TestHarness
import Utils

-- HashMap: a map from keys to values in lib/map.tersus, its operations, and what its contracts do and do not say.
-- The programs are read as the command line reads them (the map library is put in front by the pipeline, and the
-- programs are validated as they run), so a lookup is asserted with lookup and a fallback: that an inserted key is
-- found is true when a map runs, and these tests say so, but fetch after an insert asks a caller to prove it and
-- cannot be written here (see lib/map.tersus). fetch is tested where its precondition is a function's own.
testHashMap :: Test
testHashMap =
    TestList
            "testHashMap"
            [ TestList
                "insert and lookup"
                [ testCase "an empty map" (pipelineRuns "m = HashMap::new(); return m.size() * 10 + m.lookup(1, 7);" (VInt 7))
                , testCase "inserted and read back" (pipelineRuns "m = HashMap::new().insert(1, 100).insert(2, 200); return m.lookup(1, 0) + m.lookup(2, 0);" (VInt 300))
                , testCase "a missing key is the fallback" (pipelineRuns "m = HashMap::new().insert(1, 100); return m.lookup(9, 7);" (VInt 7))
                , testCase "insert at a key replaces it" (pipelineRuns "m = HashMap::new().insert(1, 100).insert(1, 111); return m.lookup(1, 0) * 10 + m.size();" (VInt 1111))
                , testCase "contains" (pipelineRuns "m = HashMap::new().insert(1, 100); a = m.contains(1); b = m.contains(2); if a { if b { return 3; }; return 1; }; return 0;" (VInt 1))
                , testCase "negative keys" (pipelineRuns "m = HashMap::new().insert(0 - 5, 50).insert(-2147483647, 60); return m.lookup(0 - 5, 0) + m.lookup(-2147483647, 0);" (VInt 110))
                ]
            , TestList
                "remove"
                [ testCase "removed and not found" (pipelineRuns "m = HashMap::new().insert(1, 100).insert(2, 200).remove(1); return m.lookup(1, 7) * 100 + m.lookup(2, 0) + m.size();" (VInt 901))
                , testCase "remove a missing key" (pipelineRuns "m = HashMap::new().insert(1, 100).remove(9); return m.lookup(1, 0) * 10 + m.size();" (VInt 1001))
                , testCase "remove and insert again" (pipelineRuns "m = HashMap::new().insert(1, 100).remove(1).insert(1, 300); return m.lookup(1, 0) + m.size();" (VInt 301))
                ]
            , TestList
                "keys and values"
                [ testCase "string keys" (pipelineRuns "m = HashMap::new().insert(\"one\", 1).insert(\"two\", 2).insert(\"one\", 11); return m.lookup(\"one\", 0) * 100 + m.lookup(\"two\", 0) * 10 + m.size();" (VInt 1122))
                , testCase "struct keys with their own Hash" (pipelineRuns "struct Point { x: Int, y: Int }; impl Clone for Point { }; impl Eq for Point { }; impl Hash for Point { fn hash(self: &Self) -> Int [{ }] [{ affirm return >= 0; affirm return < 2147483647; }] { return hashCombine(hashCombine(3, self.x), self.y); }; }; m = HashMap::new().insert(Point { x: 1, y: 2 }, 12).insert(Point { x: 3, y: 4 }, 34); return m.lookup(Point { x: 1, y: 2 }, 0) * 100 + m.lookup(Point { x: 3, y: 4 }, 0);" (VInt 1234))
                , testCase "values that own lists" (pipelineRuns "m = HashMap::new().insert(1, push(push([], 10), 20)).insert(2, push([], 30)); a = m.lookup(1, []); b = m.lookup(2, []); return size(a) * 100 + size(b) * 10 + get(b, 0);" (VInt 240))
                , testCase "a map in a map" (pipelineRuns "inner = HashMap::new().insert(1, 5); m = HashMap::new().insert(9, inner); return m.lookup(9, HashMap::new()).lookup(1, 0);" (VInt 5))
                ]
            , TestList
                "entries"
                [ testCase "every entry, in some order" (pipelineRuns "m = HashMap::new().insert(1, 10).insert(2, 20).insert(1, 11); s = 0; for e in m.entries() { s = s + e.key * 1000 + e.value; }; return s + size(m.entries()) * 100000 + m.size();" (VInt 203033))
                , testCase "entries past the spread" (pipelineRuns "m = HashMap::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { m = m.insert(i, i); i = i + 1; }; s = 0; for e in m.entries() { s = s + e.key + e.value; }; return s;" (VInt 1560))
                ]
            , TestList
                "entries by reference"
                [ testCase "every entry by reference, in some order" (pipelineRuns "m = HashMap::new().insert(1, 10).insert(2, 20).insert(1, 11); s = 0; n = 0; total = m.size(); while n < total [{ affirm n >= 0; affirm n <= total; }] shrinks total - n { e = m.entryRef(n); s = s + (*e).key * 1000 + (*e).value; n = n + 1; }; return s + total * 100000 + m.size();" (VInt 203033))
                , testCase "entries by reference past the spread" (pipelineRuns "m = HashMap::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { m = m.insert(i, i); i = i + 1; }; s = 0; n = 0; total = m.size(); while n < total [{ affirm n >= 0; affirm n <= total; }] shrinks total - n { e = m.entryRef(n); s = s + (*e).key + (*e).value; n = n + 1; }; return s;" (VInt 1560))
                , testCase "entryRef where the entry is a precondition" (pipelineValid "fn useIt(m: &HashMap<Int, Int>) -> Int [{ affirm findNth(m.buckets, 1).1 >= 0; }] [{ }] { e = m.entryRef(1); return (*e).key * 1000 + (*e).value; }; return 0;")
                , testCase "the map cannot be moved while an entryRef is live" (pipelineRejected "fn bad(m: HashMap<Int, Int>) -> Int [{ affirm findNth(m.buckets, 0).1 >= 0; }] [{ }] { e = m.entryRef(0); m = m.insert(9, 9); return (*e).key; }; return 0;" "cannot be moved while that borrow is live")
                ]
            , TestList
                "growth"
                [ testCase "past the spread, everything is found" (pipelineRuns "m = HashMap::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { m = m.insert(i, i * 2); i = i + 1; }; s = 0; j = 0; while j < 40 [{ affirm j >= 0; affirm j <= 40; }] shrinks 40 - j { s = s + m.lookup(j, 0 - 1); j = j + 1; }; return m.size() * 10000 + s;" (VInt 401560))
                , testCase "removed after the spread" (pipelineRuns "m = HashMap::new(); i = 0; while i < 40 [{ affirm i >= 0; affirm i <= 40; }] shrinks 40 - i { m = m.insert(i, i); i = i + 1; }; m = m.remove(0).remove(39).remove(20); return m.size() * 100 + m.lookup(0, 7) * 10 + m.lookup(20, 8);" (VInt 3778))
                ]
            , TestList
                "contracts"
                [ testCase "fetch where the key is a precondition" (pipelineValid "fn getIt(m: &HashMap<Int, Int>, k: &Int) -> Int [{ affirm findIn(get(m.buckets, Hash::hash(k) % size(m.buckets)), k) >= 0; }] [{ }] { return m.fetch(k); }; return 0;")
                , testCase "a key type without Hash is refused" (pipelineRejected "struct Plain { x: Int }; impl Clone for Plain { }; m = HashMap::new().insert(Plain { x: 1 }, 2); return m.size();" "needs K to implement Hash")
                , testCase "the count after insert is bounded" (pipelineValid "fn addOne(m: HashMap<Int, Int>, k: Int, v: Int) -> Int [{ }] [{ affirm return >= size(m); affirm return <= size(m) + 1; }] { return m.insert(k, v).size(); }; return 0;")
                ]
            ]
