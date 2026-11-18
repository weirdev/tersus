module TestThreads (testThreads) where

import Syntax
import TestHarness
import TestNative (sameAsMir)

-- Threads: lib/std/thread/thread.tersus, a closure started on a thread and joined for its result. The programs are read as the
-- command line reads them (the thread library is put in front of a program that mentions Thread). A thread shares
-- nothing with the program that starts it, so `eval` runs it where it is started, and native code gives the same.
testThreads :: Test
testThreads =
    TestList
        "testThreads"
        [ TestList
            "spawn and join"
            [ testCase "a closure's result is joined" (pipelineRuns "t = Thread::spawn(fn() -> Int => 41 + 1); return t.join();" (VInt 42))
            , testCase "a move closure takes a list" (pipelineRuns "xs = [1, 2, 3]; t = Thread::spawn(move fn() -> Int => size(xs)); return t.join();" (VInt 3))
            , testCase "a list moves out of a thread" (pipelineRuns "xs = [1, 2]; t = Thread::spawn(move fn() -> List<Int> { ys = xs; return push(ys, 3); }); zs = t.join(); return size(zs);" (VInt 3))
            , testCase "two threads, joined in the other order" (pipelineRuns "a = Thread::spawn(fn() -> Int => 1); b = Thread::spawn(fn() -> Int => 2); y = b.join(); x = a.join(); return x * 10 + y;" (VInt 12))
            , testCase "a thread starts a thread" (pipelineRuns innerThread (VInt 6))
            , testCase "a thread is joined by the function it is given to" (pipelineRuns "fn finish(t: Thread<Int>) -> Int { return t.join() * 2; }; t = Thread::spawn(fn() -> Int => 21); return finish(t);" (VInt 42))
            , testCase "a named function with no parameters is a closure" (pipelineRuns "fn seven() -> Int { return 7; }; t = Thread::spawn(seven); return t.join();" (VInt 7))
            , testCase "a closure calls a function of the program" (pipelineRuns "fn work(n: Int) -> Int { return n * 2; }; k = 21; t = Thread::spawn(move fn() -> Int => work(k)); return t.join();" (VInt 42))
            , testCase "a sum split across four threads" (pipelineRuns fourWaySum (VInt 499500))
            , testCase "recursion splits a sum across threads" (pipelineRuns recursiveSum (VInt 4950))
            , testCase "a program that declares its own Thread does not get the library" (pipelineRuns "struct Thread { n: Int }; t = Thread { n: 4 }; return t.n;" (VInt 4))
            ]
        , TestList
            "validation"
            [ testCase "a program with threads validates" (pipelineValid fourWaySum)
            , testCase "a capture's clause carries a fact into the thread" (pipelineValid "fn work(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { return n * 2; }; k = 21; t = Thread::spawn(move fn() -> Int [{ affirm k >= 0; }] [{ }] => work(k)); return t.join();")
            , testCase "a closure's call is checked against the function's contract" (pipelineRejected "fn positive(n: Int) -> Int [{ affirm n > 0; }] [{ }] { return n; }; t = Thread::spawn(fn() -> Int => positive(0)); return t.join();" "Could not prove: n > 0")
            , testCase "join promises only what the bound does" (pipelineRejected "t = Thread::spawn(fn() -> Int => 42); r = t.join(); affirm r = 42; return r;" "Could not prove: r = 42")
            , testCase "a result's invariant holds after the join" (pipelineValid "struct Pos { n: Int } invariant [{ affirm n > 0; }]; t = Thread::spawn(fn() -> Pos => Pos { n: 3 }); p = t.join(); affirm p.n > 0; return p.n;")
            , testCase "a thread that is not joined is refused" (pipelineRejected "t = Thread::spawn(fn() -> Int => 1); return 0;" "linear type")
            , testCase "a thread is joined once" (pipelineRejected "t = Thread::spawn(fn() -> Int => 1); a = t.join(); b = t.join(); return a + b;" "t was moved")
            , testCase "a closure that borrows is refused" (pipelineRejected "xs = [1, 2]; t = Thread::spawn(fn() -> Int => size(xs)); return t.join();" "Thread::spawn is given a closure that borrows xs: a thread cannot hold a reference")
            , testCase "a closure that starts the function it is in again has to be ~" (pipelineRejected "fn fan(n: Int) -> Int [{ }] [{ }] ~ { if n <= 0 { return 0; }; t = Thread::spawn(move fn() -> Int => fan(n - 1)); return t.join() + 1; }; return fan(2);" "may diverge")
            , testCase "a ~ closure starts the function it is in again" (pipelineValid recursiveSum)
            ]
        , TestList
            "native"
            [ sameNatively "a closure's result is joined" "t = Thread::spawn(fn() -> Int => 41 + 1); return t.join();"
            , sameNatively "a list moves in and out of a thread" "xs = [1, 2]; t = Thread::spawn(move fn() -> List<Int> { ys = xs; return push(ys, 3); }); zs = t.join(); return size(zs);"
            , sameNatively "a string result" "s = \"thread\"; t = Thread::spawn(move fn() -> String { own = s; return own.concat(\"s\"); }); r = t.join(); return size(r.bytes);"
            , sameNatively "a thread starts a thread" innerThread
            , sameNatively "a sum split across four threads" fourWaySum
            , sameNatively "recursion splits a sum across threads" recursiveSum
            ]
        ]
  where
    innerThread = "fn inner() -> Int { t = Thread::spawn(fn() -> Int => 5); return t.join() + 1; }; t = Thread::spawn(fn() -> Int => inner()); return t.join();"
    recursiveSum =
        "fn sumRange(lo: Int, hi: Int, depth: Int) -> Int [{ }] [{ }] ~ {\n\
        \    if depth <= 0 {\n\
        \        s = 0; i = lo;\n\
        \        while i < hi [{ affirm i >= lo; }] shrinks hi - i { s = s + i; i = i + 1; };\n\
        \        return s;\n\
        \    };\n\
        \    mid = lo + (hi - lo) / 2;\n\
        \    left = Thread::spawn(move fn() -> Int ~ => sumRange(lo, mid, depth - 1));\n\
        \    right = sumRange(mid, hi, depth - 1);\n\
        \    return left.join() + right;\n\
        \};\n\
        \return sumRange(0, 100, 3);"
    fourWaySum =
        "fn sumRange(lo: Int, hi: Int) -> Int [{ }] [{ }] {\n\
        \    s = 0; i = lo;\n\
        \    while i < hi [{ affirm i >= lo; }] shrinks hi - i { s = s + i; i = i + 1; };\n\
        \    return s;\n\
        \};\n\
        \a = Thread::spawn(fn() -> Int => sumRange(0, 250));\n\
        \b = Thread::spawn(fn() -> Int => sumRange(250, 500));\n\
        \c = Thread::spawn(fn() -> Int => sumRange(500, 750));\n\
        \d = sumRange(750, 1000);\n\
        \return a.join() + b.join() + c.join() + d;"

-- The program does natively what it does in `eval` (testNative's check; without clang the case passes)
sameNatively :: String -> String -> Test
sameNatively name source = TestCase name (sameAsMir name source)
