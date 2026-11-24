module TestThreads (testThreads) where

import Control.Exception (finally)
import Data.List (isInfixOf)
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory, removeFile)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (hClose)

import Bootstrap (tersusLlvm)
import CacheLock (openTempFileCloexec)
import Native (buildExecutableFast)
import Syntax
import TestHarness
import TestNative (clangAvailable, runExecutableBytes, sameAsMir)
import Utils (Result (..))

-- Threads: lib/thread.tersus, a closure started on a thread and joined for its result. The programs are read as the
-- command line reads them (the thread library is put in front of a program that mentions Thread or ScopedThread). A
-- thread shares nothing that another one writes, so `eval` runs it where it is started, and native code, which runs it
-- on a thread of its own (MirThreads), gives the same; its runs check the heap (TERSUS_CHECK).
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
            , sameNatively "sixty-three threads" (recursiveSumOf 6)
            , sameNatively "a thread starts a thread that starts a thread" "fn third() -> Int { t = Thread::spawn(fn() -> Int => 3); return t.join() + 1; }; fn second() -> Int { t = Thread::spawn(fn() -> Int => third()); return t.join() * 10; }; t = Thread::spawn(fn() -> Int => second()); return t.join();"
            , sameNatively "a thread is joined by the function it is given to" "fn finish(t: Thread<Int>) -> Int { return t.join() * 2; }; t = Thread::spawn(fn() -> Int => 21); return finish(t);"
            , sameNatively "a struct that owns lists moves in and out" "struct Pair { a: List<Int>, b: List<Int> }; p = Pair { a: [1, 2], b: [3] }; t = Thread::spawn(move fn() -> Pair { q = p; return Pair { a: push(q.a, 4), b: q.b }; }); r = t.join(); return size(r.a) * 10 + size(r.b);"
            , sameNatively "threads that allocate, and values freed by a thread that did not make them" allocating
            , sameNatively "an Int that overflows in a thread" "fn big(n: Int) -> Int [{ }] [{ }] { return n * n * n * n * n; }; t = Thread::spawn(fn() -> Int => big(100000)); return t.join();"
            , defaultHeap "threads that allocate, with the runtime's own heap" allocating "600\n"
            , defaultHeap "sixty-three threads, with the runtime's own heap" (recursiveSumOf 6) "4950\n"
            , sameNatively "a thread writes" "t = Thread::spawn(fn() -> Byte => writeByte(72)); a = t.join(); b = writeByte(10); return toInt(a) + toInt(b);"
            ]
        , TestList
            "scoped threads"
            [ testCase "a scoped thread borrows a list" (pipelineRuns borrowedSum (VInt 4950))
            , testCase "a scoped thread validates" (pipelineValid borrowedSum)
            , testCase "a scoped thread is joined in the function that starts it" (pipelineRuns "fn count(xs: &List<Int>) -> Int { f = fn() -> Int => size(xs); h = ScopedThread::spawn(&f); return h.join(); }; xs = [1, 2, 3]; return count(&xs);" (VInt 3))
            , testCase "what a scoped thread borrows is not written while it runs" (pipelineRejected "xs = [1, 2]; f = fn() -> Int => size(xs); h = ScopedThread::spawn(&f); xs = push(xs, 3); return h.join();" "xs cannot be assigned while it is borrowed by h")
            , testCase "what a scoped thread borrows is not moved while it runs" (pipelineRejected "fn give(xs: List<Int>) -> Int { return size(xs); }; xs = [1, 2]; f = fn() -> Int => size(xs); h = ScopedThread::spawn(&f); n = give(xs); return h.join() + n;" "xs is borrowed by h, so it cannot be moved while that borrow is live")
            , testCase "a scoped thread does not outlive the closure it borrows" (pipelineRejected "fn start<F: Fn() -> Int>(f: F) -> ScopedThread<Int, F> [{ }] [{ }] { return ScopedThread::spawn(&f); }; return 0;" "start returns a reference, but no parameter of it is a reference for the result to be from")
            , testCase "a scoped thread that is not joined is refused" (pipelineRejected "f = fn() -> Int => 1; h = ScopedThread::spawn(&f); return 0;" "linear type")
            , testCase "a closure that borrows for updating is refused" (pipelineRejected "xs = [1, 2]; r = &mut xs; f = fn() -> Int => size(r); h = ScopedThread::spawn(&f); return h.join();" "ScopedThread::spawn is lent a closure that borrows r for updating: a scoped thread only reads what it borrows")
            , testCase "a result that holds a reference is refused" (pipelineRejected "xs = [1, 2]; f = fn() -> &List<Int> => &xs; h = ScopedThread::spawn(&f); y = h.join(); return size(y);" "ScopedThread::spawn gives a &List<Int>, which can hold a reference, and a thread's result cannot")
            , sameNatively "a scoped thread borrows a list" borrowedSum
            , sameNatively "a scoped thread's closure owns what it reads" "ys = [1, 2, 3]; f = move fn() -> Int { s = 0; i = 0; while i < 100000 [{ affirm i >= 0; }] shrinks 100000 - i { s = s + size(ys); i = i + 1; }; return s; }; h = ScopedThread::spawn(&f); return h.join();"
            , sameNatively "scoped threads and threads together" "xs = [1, 2, 3]; f = fn() -> Int => size(xs); h = ScopedThread::spawn(&f); t = Thread::spawn(fn() -> Int => 10); return h.join() + t.join();"
            , sameNatively "a scoped thread starts a scoped thread" "fn count(xs: &List<Int>) -> Int { f = fn() -> Int => size(xs); h = ScopedThread::spawn(&f); return h.join(); }; xs = [1, 2, 3]; g = fn() -> Int => count(&xs) * 10; h = ScopedThread::spawn(&g); return h.join();"
            , sameNatively "scoped threads that allocate" "xs = [5, 6, 7]; f = fn() -> List<Int> { out = []; i = 0; while i < 2000 [{ affirm i >= 0; }] shrinks 2000 - i { out = push(out, size(xs) + i); i = i + 1; }; return out; }; a = ScopedThread::spawn(&f); b = ScopedThread::spawn(&f); l = a.join(); m = b.join(); return size(l) + size(m);"
            , nativeSpawnIr "library scoped spawns use the runtime" True borrowedSum
            , nativeSpawnIr "a source-defined lookalike does not start a native thread" False scopedLookalike
            , TestCase "the program cannot return a live thread" (nativeRefused "return Thread::spawn(fn() -> Int => 7);" "join it before returning")
            , TestCase "the program cannot return a live thread inside a tuple" (nativeRefused "return (1, Thread::spawn(fn() -> Int => 7));" "join it before returning")
            ]
        ]
  where
    innerThread = "fn inner() -> Int { t = Thread::spawn(fn() -> Int => 5); return t.join() + 1; }; t = Thread::spawn(fn() -> Int => inner()); return t.join();"
    recursiveSum = recursiveSumOf 3
    recursiveSumOf :: Int -> String
    recursiveSumOf levels =
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
        \return sumRange(0, 100, " ++ show levels ++ ");"
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
    -- (each thread makes lists and frees some of them; the main thread frees the lists the threads give)
    allocating =
        "fn build(k: Int) -> List<List<Int>> [{ }] [{ }] {\n\
        \    rows = []; i = 0;\n\
        \    while i < 300 [{ affirm i >= 0; }] shrinks 300 - i {\n\
        \        row = []; j = 0;\n\
        \        while j < 20 [{ affirm j >= 0; }] shrinks 20 - j { row = push(row, i * j + k); j = j + 1; };\n\
        \        if i % 2 = 0 { rows = push(rows, row); };\n\
        \        i = i + 1;\n\
        \    };\n\
        \    return rows;\n\
        \};\n\
        \a = Thread::spawn(fn() -> List<List<Int>> => build(1));\n\
        \b = Thread::spawn(fn() -> List<List<Int>> => build(2));\n\
        \c = Thread::spawn(fn() -> List<List<Int>> => build(3));\n\
        \d = build(4);\n\
        \x = a.join(); y = b.join(); z = c.join();\n\
        \return size(x) + size(y) + size(z) + size(d);"
    borrowedSum =
        "fn part(xs: &List<Int>, lo: Int, hi: Int) -> Int [{ affirm lo >= 0; }] [{ }] {\n\
        \    s = 0; i = lo;\n\
        \    while i < hi [{ affirm i >= 0; }] shrinks hi - i { if i < size(xs) { s = s + get(xs, i); }; i = i + 1; };\n\
        \    return s;\n\
        \};\n\
        \xs = []; i = 0;\n\
        \while i < 100 [{ affirm i >= 0; }] shrinks 100 - i { xs = push(xs, i); i = i + 1; };\n\
        \f = fn() -> Int => part(&xs, 0, 50);\n\
        \g = fn() -> Int => part(&xs, 50, 100);\n\
        \a = ScopedThread::spawn(&f);\n\
        \b = ScopedThread::spawn(&g);\n\
        \return a.join() + b.join();"

-- The program does natively what it does in `eval` (testNative's check; without clang the case passes)
sameNatively :: String -> String -> Test
sameNatively name source = TestCase name (sameAsMir name source)

nativeRefused :: String -> String -> IO TestResult
nativeRefused source expected = testAssertErrorContains expected <$> tersusLlvm source

nativeSpawnIr :: String -> Bool -> String -> Test
nativeSpawnIr name expected source = TestCase name $ do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            ir <- tersusLlvm source
            pure $ case ir of
                Error e -> Just e
                Ok text -> testAssertEq ("call i64 @\"tersus_thread_spawn\"" `isInfixOf` text) expected

scopedLookalike :: String
scopedLookalike = unlines
    [ "struct ScopedThread<T, F> { value: T, f: &F };"
    , "impl<T, F: Fn() -> T> ScopedThread<T, F> {"
    , "    fn spawn(g: &F) -> Self from g [{ }] [{ }] { return Self { value: g(), f: &g }; };"
    , "    fn join(self: Self) -> T [{ }] [{ }] { return self.value; };"
    , "};"
    , "f = fn() -> Int => 7;"
    , "h = ScopedThread::spawn(&f);"
    , "return h.join();"
    ]

defaultHeap :: String -> String -> String -> Test
defaultHeap name source expected = TestCase name $ do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            ir <- tersusLlvm source
            case ir of
                Error e -> pure (Just e)
                Ok text -> do
                    tmp <- getTemporaryDirectory
                    let dir = tmp </> "tersus-native-test"
                    createDirectoryIfMissing True dir
                    (exe, handle) <- openTempFileCloexec dir "threads_default_heap."
                    hClose handle
                    (do
                        built <- buildExecutableFast [] exe text
                        case built of
                            Error e -> pure (Just e)
                            Ok () -> testAssertEq (ExitSuccess, expected, "") <$> runExecutableBytes exe [] "")
                        `finally` removeFile exe
