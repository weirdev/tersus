module TestNative
    ( testNative
    , nativeExamples
    , validatedPrograms
    , unvalidatedPrograms
    ) where

import Control.Exception (IOException, try)
import Data.Char (isAscii)
import Data.List (isInfixOf)
import System.Directory (createDirectoryIfMissing, doesFileExist, getTemporaryDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Cli
import qualified Mir as M
import MirEval (renderMirValue, runProgram)
import MirLower (lowerProgram)
import LlvmEmit (emitProgram)
import Native (buildExecutable, buildExecutableWith)
import Parse (parseStatementBlock)
import Pipeline
import TestHarness
import Utils

-- Native code: the LLVM IR of a program, and the executable clang builds from it. The executable has to do what the
-- executor of the MIR does, so each program here is built, run, and compared with `tersus run`: the same output, the same
-- error and the same exit status. The builds need clang, and pass without it.

testNative :: Test
testNative =
    TestList
        "testNative"
        [ testNativeIr
        , TestList "examples" [testNativeProgram path | path <- nativeExamples]
        , TestList "arithmetic" [TestCase name (sameAsMir name source) | (name, source) <- arithmeticPrograms]
        , TestList "lists" [TestCase name (sameAsMir name source) | (name, source) <- listPrograms]
        , TestList "data" [TestCase name (sameAsMir name source) | (name, source) <- dataPrograms]
        , TestList "function values" [TestCase name (sameAsUnvalidated name source) | (name, source) <- functionPrograms]
        , TestList "control flow" [TestCase name (sameAsMir name source) | (name, source) <- controlPrograms]
        , TestList "build" [testBuildKeepsFiles]
        , TestList "memory" memoryTests
        , TestList "stops" [TestCase name (sameAsMir name source) | (name, source) <- stopPrograms]
        ]

-- Every example that validates
nativeExamples :: [FilePath]
nativeExamples =
    [ "examples/" ++ name ++ ".tersus"
    | name <-
        [ "arithmetic", "basics", "booleans", "branching", "build_list", "contracts", "early_return", "element_facts"
        , "enums", "for_loops", "forall_facts", "frame_facts", "functions", "generic_lists", "helper_functions", "linear"
        , "linked_list", "loop_return", "loops", "packet_parser", "parallel_sum", "proofs", "recursion", "rewrites", "rules"
        , "safe_access", "structs", "termination", "types", "update_list"
        ]
    ]

testNativeProgram :: FilePath -> Test
testNativeProgram path = TestCase path (readFile path >>= sameAsMir path)

testNativeIr :: Test
testNativeIr =
    TestList
        "ir"
        [ TestCase "overflow-checked add" . pure $
            withIr "return 1 + 2;" (\ir -> testAssertTrue ("@llvm.sadd.with.overflow.i64" `isInfixOf` ir && "@tersus_overflow" `isInfixOf` ir))
        , TestCase "comparison" . pure $
            withIr "x = 3; return x < 4;" (\ir -> testAssertTrue ("icmp slt i64" `isInfixOf` ir && "@\"type.Bool\"" `isInfixOf` ir))
        , TestCase "function" . pure $
            withIr "fn f(a: Int) -> Int { return a; }; return f(1);" (\ir -> testAssertTrue ("define internal i64 @\"fn.f\"(i64 %p.1)" `isInfixOf` ir && "call i64 @\"fn.f\"" `isInfixOf` ir))
        , TestCase "no return" . pure $
            withIr "x = 1;" (\ir -> testAssertTrue ("define internal void @tersus_main()" `isInfixOf` ir))
        , TestCase "ghost statements are dropped" . pure $
            withIr "x = 1; affirm x = 1; return x;" (\ir -> testAssertTrue (not ("affirm" `isInfixOf` ir)))
        , TestCase "a list is a runtime list with a descriptor" . pure $
            withIr "x = push([1], 2); return x;" (\ir -> testAssertTrue ("call ptr @tersus_list_push" `isInfixOf` ir && "@\"type.List<Int>\" = private constant" `isInfixOf` ir))
        , TestCase "a struct is a runtime object with a descriptor" . pure $
            withIr "struct P { x: Int }; p = P { x: 1 }; return p;" (\ir -> testAssertTrue ("call ptr @tersus_data_new(i64 0, i64 1)" `isInfixOf` ir && "@\"data.P\" = private constant" `isInfixOf` ir))
        , TestCase "an enum value has the tag of its variant" . pure $
            withIr "enum S { A, B { w: Int } }; x = S::B { w: 2 }; return x is S::B;" (\ir -> testAssertTrue ("call ptr @tersus_data_new(i64 1, i64 1)" `isInfixOf` ir && "icmp eq i64" `isInfixOf` ir))
        , TestCase "names with non-ASCII letters are written as their UTF-8 bytes" . pure $
            withIr "struct P { \x00e9: Int }; return P { \x00e9: 1 };" (\ir -> testAssertTrue (all isAscii ir && "[3 x i8] c\"\\C3\\A9\\00\"" `isInfixOf` ir))
        , TestCase "a letter of four bytes" . pure $
            withIr "struct \x1D538 { \x1D539: Int }; return \x1D538 { \x1D539: 1 };" (\ir -> testAssertTrue (all isAscii ir && "[5 x i8] c\"\\F0\\9D\\94\\B8\\00\"" `isInfixOf` ir))
        , TestCase "a function with a non-ASCII name" . pure $
            withIr "fn d\x00e9(n: Int) -> Int { return n + 1; }; return d\x00e9(1);" (\ir -> testAssertTrue (all isAscii ir && "@\"fn.d\\C3\\A9\"" `isInfixOf` ir))
        , TestCase "a program with non-ASCII names builds" $ buildsOnly "struct P { \x00e9: Int }; enum \x00d1 { \x00c4 { \x00f6: Int }, \x00dc }; fn d\x00e9(n: Int) -> Int { return n + 1; }; return \x00d1::\x00c4 { \x00f6: d\x00e9(1) };"
        , TestCase "a function value is the address of the function" . pure $
            case lowerSource "fn inc(n: Int) -> Int { return n + 1; }; f = inc; return f(1);" of
                Left e -> Just e
                Right program -> case emitProgram program of
                    Error e -> Just e
                    Ok ir -> testAssertTrue ("store ptr @\"fn.inc\"" `isInfixOf` ir && "call i64 %" `isInfixOf` ir)
        , TestCase "a program that does not validate is not lowered" . pure $
            testAssertErrorContains "Validation failed" (llvmSource "x = 5; affirm x < 4;")
        , TestCase "command line" . pure $
            testAssertEq
                (map parseCommandLine [["llvm", "a.tersus"], ["build", "a.tersus", "-o", "a"], ["build", "a.tersus"], ["owned", "a.tersus"]])
                [Just (Llvm, "a.tersus"), Just (Build "a", "a.tersus"), Nothing, Just (Owned, "a.tersus")]
        ]
  where
    withIr source check = case llvmSource source of
        Error e -> Just e
        Ok ir -> check ir

arithmeticPrograms :: [(String, String)]
arithmeticPrograms =
    [("expression", "return 1 + 2 * 3 - 4;"), ("negative literals", "x = -4; return 3 - x;")]
        ++ [ ("division " ++ show a ++ " by " ++ show b, divisionProgram a b)
           | (a, b) <- [(7, 2), (-7, 2), (7, -2), (-7, -2), (6, 3), (-6, 3), (6, -3), (0, 5), (0, -5), (1, -1)]
           ]
  where
    divisionProgram :: Int -> Int -> String
    divisionProgram a b = "a = " ++ show a ++ "; b = " ++ show b ++ "; q = a / b; r = a % b; return q * 100 + r;"

dataPrograms :: [(String, String)]
dataPrograms =
    [ ("struct", "struct P { x: Int, y: Bool }; return P { x: 1, y: true };")
    , ("struct field", "struct P { x: Int, y: Bool }; p = P { x: 7, y: false }; return p.x;")
    , ("struct with a list", "struct P { x: Int, y: List<Int> }; p = P { x: 1, y: [2, 3] }; return p;")
    , ("struct update", "struct P { x: Int, y: Int }; p = P { x: 1, y: 2 }; q = P { y: 5, ..p }; return q;")
    , ("enum variants", "enum S { A { r: Int }, B { w: Int, h: List<Int> }, C }; return S::B { w: 2, h: [3] };")
    , ("fieldless variant", "enum S { A { r: Int }, C }; return S::C;")
    , ("variant tests", "enum S { A { r: Int }, C }; x = S::C; return x is S::C;")
    , ("variant test that fails", "enum S { A { r: Int }, C }; x = S::C; return x is S::A;")
    , ("field of a variant", "enum S { A { r: Int }, C }; x = S::A { r: 4 }; return (x as S::A).r;")
    , ("match", "enum S { A { r: Int }, B { w: Int, h: Int }, C }; fn f(s: S) -> Int { return match s { S::A { r: r } => r, S::B { w: w, h: h } => w * h, S::C => 0 }; }; return f(S::B { w: 3, h: 4 }) + f(S::A { r: 5 }) + f(S::C);")
    , ("data in a list", "enum S { A { r: Int }, C }; l = push([], S::A { r: 1 }); l = push(l, S::C); return l;")
    , ("list in data in a list", "struct P { x: List<Int> }; l = push([], P { x: [1] }); l = push(l, P { x: [] }); return l;")
    , ("recursive enum", "enum T { Leaf, Node { l: T, v: Int, r: T } }; return T::Node { l: T::Leaf, v: 1, r: T::Node { l: T::Leaf, v: 2, r: T::Leaf } };")
    , ("recursive function", "enum T { Leaf, Node { l: T, v: Int, r: T } }; fn sum(t: T) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; }; return sum(T::Node { l: T::Node { l: T::Leaf, v: 3, r: T::Leaf }, v: 1, r: T::Node { l: T::Leaf, v: 2, r: T::Leaf } });")
    , ("equal structs", "struct P { x: Int, y: List<Int> }; p = P { x: 1, y: [2, 3] }; q = P { y: [2, 3], x: 1 }; return p = q;")
    , ("different structs", "struct P { x: Int, y: List<Int> }; p = P { x: 1, y: [2, 3] }; q = P { x: 1, y: [2] }; return p = q;")
    , ("unequal structs", "struct P { x: Int }; return P { x: 1 } != P { x: 2 };")
    , ("equal variants", "enum S { A { r: Int }, C }; a = S::A { r: 1 }; return a = S::A { r: 1 };")
    , ("variants with other fields", "enum S { A { r: Int }, C }; a = S::A { r: 1 }; return a = S::A { r: 2 };")
    , ("different variants", "enum S { A { r: Int }, C }; a = S::A { r: 1 }; return a = S::C;")
    , ("fieldless variants", "enum S { A { r: Int }, C }; return S::C = S::C;")
    , ("equal trees", "enum T { Leaf, Node { l: T, v: Int, r: T } }; a = T::Node { l: T::Leaf, v: 1, r: T::Leaf }; return a = T::Node { l: T::Leaf, v: 1, r: T::Leaf };")
    , ("lists of structs equal", "struct P { x: Int }; l = push([], P { x: 1 }); return l = push([], P { x: 1 });")
    , ("data parameter and result", "struct P { x: Int, y: Int }; fn swap(p: P) -> P { return P { x: p.y, y: p.x }; }; return swap(P { x: 1, y: 2 });")
    , ("data built in a loop", "struct P { x: Int }; l = []; i = 0; while i < 50 [{ affirm i >= 0; }] shrinks 50 - i { l = push(l, P { x: i }); i = i + 1; }; return size(l);")
    , ("a variant returned in a branch only", "enum S { A { r: Int }, C }; x = S::C; if x is S::A { return x; };")
    ]

-- Function values. The validator cannot yet follow a call of a function that is a value, so these are lowered without
-- validation (as the MIR tests are) and compared with the executor of the MIR.
functionPrograms :: [(String, String)]
functionPrograms =
    [ ("a function as a result", "fn inc(n: Int) -> Int { return n + 1; }; return inc;")
    , ("call of a local", "fn inc(n: Int) -> Int { return n + 1; }; f = inc; return f(5);")
    , ("a parameter", "fn inc(n: Int) -> Int { return n + 1; }; fn apply(g: fn(Int) -> Int, n: Int) -> Int { return g(g(n)); }; return apply(inc, 1);")
    , ("a function that takes two", "fn add(a: Int, b: Int) -> Int { return a + b; }; fn fold(g: fn(Int, Int) -> Int) -> Int { return g(g(1, 2), 3); }; return fold(add);")
    , ("a boolean result", "fn big(n: Int) -> Bool { return n > 10; }; f = big; return f(11);")
    , ("a function that takes a list", "fn total(l: List<Int>) -> Int { return size(l); }; f = total; return f([1, 2, 3]);")
    , ("in a list", "fn inc(n: Int) -> Int { return n + 1; }; fs = push([], inc); fs = push(fs, inc); f = get(fs, 1); return f(2);")
    , ("a list of functions printed", "fn inc(n: Int) -> Int { return n + 1; }; return push([], inc);")
    , ("in a struct", "struct B { f: fn(Int) -> Int }; fn inc(n: Int) -> Int { return n + 1; }; b = B { f: inc }; g = b.f; return g(41);")
    , ("a builtin", "f = size; return f([1, 2, 3]);")
    , ("a builtin on lists", "f = first; return f([7, 2, 3]);")
    , ("chosen by a branch", "fn inc(n: Int) -> Int { return n + 1; }; fn dec(n: Int) -> Int { return n - 1; }; f = inc; if 2 > 1 { f = dec; }; return f(10);")
    , ("a recursive function through a value", "fn count(n: Int) -> Int shrinks n { if n <= 0 { return 0; }; return 1 + count(n - 1); }; f = count; return f(5);")
    ]

listPrograms :: [(String, String)]
listPrograms =
    [ ("literal", "return [1, 2, 3];")
    , ("empty", "return [];")
    , ("booleans", "return [true, false];")
    , ("nested", "return [[1, 2], [], [3]];")
    , ("negative", "return [-1, 2];")
    , ("size", "x = [4, 5, 6]; return size(x);")
    , ("get, first and last", "x = [4, 5, 6]; return get(x, 1) * 100 + first(x) * 10 + last(x);")
    , ("push", "x = push(push([1], 2), 3); return x;")
    , ("push does not change its argument", "x = [1]; y = push(x, 2); return x;")
    , ("set", "x = [1, 2, 3]; y = set(x, 1, 9); return y;")
    , ("set does not change its argument", "x = [1, 2, 3]; y = set(x, 1, 9); return x;")
    , ("push to an empty list of lists", "x = [1, 2]; rows = push([], x); rows = push(rows, [3]); return rows;")
    , ("set a list in a list", "rows = [[1], [2]]; rows = set(rows, 0, [7, 8]); return rows;")
    , ("get a list from a list", "rows = [[1], [2, 3]]; return get(rows, 1);")
    , ("booleans in a list", "x = push([true], false); return get(x, 1) = false;")
    , ("last of booleans", "x = [false, true]; return last(x);")
    , ("equality", "x = [1, 2]; return x = [1, 2];")
    , ("inequality", "x = [1, 2]; return x != [1, 3];")
    , ("equality of different lengths", "x = [1, 2]; return x = [1, 2, 3];")
    , ("equality of empty lists", "x = push([1], 2); y = [3]; return [] = [];")
    , ("equality of nested lists", "x = [[1], [2]]; return x = [[1], [2]];")
    , ("inequality of nested lists", "x = [[1], [2]]; return x = [[1], [3]];")
    , ("list function", "fn grow(l: List<Int>) -> List<Int> { return push(l, size(l)); }; return grow(grow([]));")
    , ("list parameter", "fn total(l: List<Int>) -> Int { s = 0; i = 0; while i < size(l) [{ affirm i >= 0; affirm i <= size(l); }] shrinks size(l) - i { s = s + get(l, i); i = i + 1; }; return s; }; return total([1, 2, 3, 4]);")
    , ("build in a loop", "l = []; i = 0; while i < 300 [{ affirm i >= 0; }] shrinks 300 - i { l = push(l, i * i); i = i + 1; }; return l;")
    , ("nested empty lists are equal", "return [[]] = [[]];")
    , ("size of a nested empty list", "return size([[]]);")
    , ("a nested empty list against a local", "x = [[true]]; return [[]] = x;")
    , ("a local against a nested empty list", "x = [[true]]; return x != [[]];")
    , ("deeper empty lists", "return [[[]]] = [[[]]];")
    , ("an empty list among others", "return [[], [1], []];")
    , ("a parameter assigned a part", "fn f(row: List<Int>, rows: List<List<Int>>) -> Int [{ affirm size(rows) > 0; }] [{ }] { row = get(rows, 0); return size(row); }; return f([1], [[2, 3]]);")
    , ("a parameter assigned a part that is kept", "fn f(row: List<Int>, rows: List<List<Int>>) -> List<Int> [{ affirm size(rows) > 0; }] [{ }] { row = get(rows, 0); return row; }; return f([1], [[2, 3]]);")
    , ("a parameter assigned a field", "struct P { xs: List<Int> }; fn f(xs: List<Int>, p: P) -> Int { xs = p.xs; return size(xs); }; return f([1], P { xs: [2, 3] });")
    , ("a list that is not returned", "x = [1, 2];")
    , ("returned in a branch only", "x = [1]; if size(x) > 5 { return x; };")
    ]

controlPrograms :: [(String, String)]
controlPrograms =
    [ ("comparisons", "a = 3; b = 5; return a < b;")
    , ("equality of booleans", "a = 3 < 5; b = 4 < 2; return a = b;")
    , ("inequality", "a = 3; return a != 3;")
    , ("branch", "a = 3; if a > 2 { a = a * 10; } else { a = 0; }; return a;")
    , ("while loop", "i = 0; s = 0; while i < 10 shrinks 10 - i { s = s + i; i = i + 1; }; return s;")
    , ("no return", "x = 1 + 2;")
    , ("a return that is not reached", "if false { return 1; };")
    , ("a return in a branch that is not taken", "x = 3; if x > 5 { return 1; };")
    , ("a return in a branch that is taken", "x = 3; if x < 5 { return 1; };")
    , ("a return in a loop that is not reached", "x = 3; while x < 3 shrinks 3 - x { return 1; };")
    , ("a boolean return in a branch that is not taken", "x = 3; if x > 5 { return true; };")
    , ("recursion", "fn fact(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n = 0 { return 1; }; return n * fact(n - 1); }; return fact(10);")
    , ("boolean result", "fn even(n: Int) -> Bool { return n % 2 = 0; }; return even(10);")
    , ("boolean parameter", "fn pick(c: Bool, a: Int, b: Int) -> Int { if c { return a; }; return b; }; return pick(1 < 2, 10, 20);")
    ]

-- Every program of these tests that validates, and every one that is lowered without being validated
validatedPrograms :: [(String, String)]
validatedPrograms = arithmeticPrograms ++ controlPrograms ++ listPrograms ++ dataPrograms ++ stopPrograms

unvalidatedPrograms :: [(String, String)]
unvalidatedPrograms = functionPrograms

-- Programs that stop on an overflow, with the message and status of `tersus run`
stopPrograms :: [(String, String)]
stopPrograms =
    [ ("add", "return 9223372036854775807 + 1;")
    , ("sub", "x = -9223372036854775807 - 1; return x - 1;")
    , ("mul", "x = 4611686018427387904; return x * 2;")
    , ("smallest divided by -1", "x = -9223372036854775807 - 1; y = -1; return x / y;")
    , ("smallest mod -1", "x = -9223372036854775807 - 1; y = -1; return x % y;")
    , ("largest still fits", "return 9223372036854775806 + 1;")
    ]

-- Building to `<output>` must not touch an `<output>.build` that is already there
testBuildKeepsFiles :: Test
testBuildKeepsFiles = TestCase "an existing output.build directory is kept" $ do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            tmp <- getTemporaryDirectory
            let dir = tmp </> "tersus-native-keep"
                exe = dir </> "app"
                precious = exe ++ ".build" </> "precious.txt"
            createDirectoryIfMissing True (exe ++ ".build")
            writeFile precious "keep me"
            built <- case llvmSource "return 1;" of
                Error e -> pure (Error e)
                Ok ir -> buildExecutable exe ir
            kept <- doesFileExist precious
            pure $ case built of
                Error e -> Just e
                Ok () -> testAssertTrue kept

-- Builds the program and runs it, and runs it on the MIR: both have to print the same, and fail the same
sameAsMir :: String -> String -> IO TestResult
sameAsMir name source = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else case compileSource source of
            Error e -> pure (Just ("Does not compile: " ++ e))
            Ok _ -> case llvmSource source of
                Error e -> pure (Just e)
                Ok ir -> do
                    buildAndRun (map safeChar name) name ir (expected (runSource Run source))
  where
    expected (Ok output) = (ExitSuccess, if null output then "" else output ++ "\n", "")
    expected (Error e) = (ExitFailure 1, "", e ++ "\n")

-- A list built by pushing, and changed by setting, is built in place: it needs memory in proportion to its length and not to its
-- length squared (a million pushes copied each time would need terabytes), and a limit on the memory of the program shows it
memoryTests :: [Test]
memoryTests =
    [ TestCase "a million pushes" (underLimit "l = []; i = 0; while i < 1000000 [{ affirm i >= 0; }] shrinks 1000000 - i { l = push(l, i); i = i + 1; }; return size(l);" "1000000\n")
    , TestCase "pushes and sets" (underLimit "l = []; i = 0; while i < 300000 [{ affirm i >= 0; }] shrinks 300000 - i { l = push(l, i); i = i + 1; }; k = 0; while k < 300000 [{ affirm k >= 0; }] shrinks 300000 - k { l = set(l, k, get(l, k) + 1); k = k + 1; }; return get(l, 299999);" "300000\n")
    , TestCase "lists of lists" (underLimit "rows = []; i = 0; while i < 20000 [{ affirm i >= 0; }] shrinks 20000 - i { row = push(push([], i), i); rows = push(rows, row); i = i + 1; }; return size(rows);" "20000\n")
    , TestCase "values made and dropped in a loop" (underLimit "struct P { x: Int, ys: List<Int> }; s = 0; i = 0; while i < 2000000 [{ affirm i >= 0; }] shrinks 2000000 - i { p = P { x: i, ys: push(push([], i), 1) }; s = s + p.x; i = i + 1; }; return s;" "1999999000000\n")
    ]
  where
    underLimit source expected = do
        available <- clangAvailable
        if not available
            then pure Nothing
            else case llvmSource source of
                Error e -> pure (Just e)
                Ok ir -> do
                    tmp <- getTemporaryDirectory
                    let dir = tmp </> "tersus-native-test"
                        exe = dir </> "memory_limit"
                    createDirectoryIfMissing True dir
                    built <- buildExecutable exe ir
                    case built of
                        Error e -> pure (Just e)
                        Ok () -> do
                            -- 150 MB of address space
                            (code, out, err) <- readProcessWithExitCode "sh" ["-c", "ulimit -v 150000; " ++ exe] ""
                            pure (testAssertEq (code, out, err) (ExitSuccess, expected, ""))

-- Builds the program, which tests the IR without running it
buildsOnly :: String -> IO TestResult
buildsOnly source = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else case llvmSource source of
            Error e -> pure (Just e)
            Ok ir -> do
                tmp <- getTemporaryDirectory
                let dir = tmp </> "tersus-native-test"
                createDirectoryIfMissing True dir
                built <- buildExecutable (dir </> "builds_only") ir
                pure $ case built of
                    Error e -> Just e
                    Ok () -> Nothing

-- The programs are built so that the runtime checks its use of memory: a value freed twice, or still there when the program
-- ends, fails the run, and a value that is used after it is freed reads 0xDD
checkedBuild :: [String]
checkedBuild = ["-DTERSUS_CHECK"]

-- The programs that are run again under valgrind, which finds the same mistakes without the help of the runtime: those that
-- take values apart, change them in place, or call through a function value
valgrindCases :: [String]
valgrindCases =
    [ "examples/enums.tersus", "examples/structs.tersus", "examples/linked_list.tersus", "examples/update_list.tersus"
    , "examples/termination.tersus", "examples/packet_parser.tersus"
    , "recursive function", "data built in a loop", "struct update", "match", "build in a loop", "set a list in a list"
    , "push to an empty list of lists", "in a list", "in a struct", "a parameter", "a builtin on lists"
    ]

-- Builds the program with the memory checks of the runtime and runs it, and for some programs builds it again as it is
-- built for use and runs that under valgrind, which finds the same mistakes without the help of the runtime. It has to
-- print what the executor prints, and have nothing to say to valgrind.
buildAndRun :: String -> String -> String -> (ExitCode, String, String) -> IO TestResult
buildAndRun file name ir expectation = do
    tmp <- getTemporaryDirectory
    let dir = tmp </> "tersus-native-test"
        exe = dir </> file
    createDirectoryIfMissing True dir
    checked <- buildExecutableWith checkedBuild exe ir
    case checked of
        Error e -> pure (Just e)
        Ok () -> do
            plain <- readProcessWithExitCode exe [] ""
            case testAssertEq plain expectation of
                Just failure -> pure (Just failure)
                Nothing -> do
                    available <- if name `elem` valgrindCases then valgrindAvailable else pure False
                    if not available
                        then pure Nothing
                        else do
                            built <- buildExecutable (exe ++ "_plain") ir
                            case built of
                                Error e -> pure (Just e)
                                Ok () -> do
                                    result <- readProcessWithExitCode "valgrind" ["-q", "--error-exitcode=99", "--leak-check=full", "--errors-for-leak-kinds=definite,possible", exe ++ "_plain"] ""
                                    pure (fmap ("under valgrind:\n" ++) (testAssertEq result expectation))

valgrindAvailable :: IO Bool
valgrindAvailable = do
    outcome <- try (readProcessWithExitCode "valgrind" ["--version"] "")
    pure $ case outcome of
        Left e -> const False (e :: IOException)
        Right (code, _, _) -> code == ExitSuccess

-- The same for a program that is lowered without being validated
sameAsUnvalidated :: String -> String -> IO TestResult
sameAsUnvalidated name source = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else case lowerSource source of
            Left e -> pure (Just e)
            Right program -> case emitProgram program of
                Error e -> pure (Just e)
                Ok ir -> do
                    buildAndRun ("unvalidated_" ++ map safeChar name) name ir (expected (runProgram program))
  where
    expected (Ok result) = (ExitSuccess, maybe "" ((++ "\n") . renderMirValue) result, "")
    expected (Error e) = (ExitFailure 1, "", "Evaluation failed: " ++ e ++ "\n")

lowerSource :: String -> Either String M.Program
lowerSource source = case parseStatementBlock source of
    Left err -> Left ("Parse failed: " ++ show err)
    Right stmts -> case lowerProgram stmts of
        Error e -> Left e
        Ok program -> Right program

safeChar :: Char -> Char
safeChar c = if c `elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] then c else '_'

clangAvailable :: IO Bool
clangAvailable = do
    outcome <- try (readProcessWithExitCode "clang" ["--version"] "")
    pure $ case outcome of
        Left e -> const False (e :: IOException)
        Right (code, _, _) -> code == ExitSuccess
