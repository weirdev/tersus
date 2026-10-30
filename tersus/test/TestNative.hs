module TestNative
    ( testNative
    , nativeExamples
    , validatedPrograms
    , unvalidatedPrograms
    , clangAvailable
    , runExecutableBytes
    ) where

import Control.Exception (IOException, finally, try)
import Data.Char (isAscii)
import Data.List (isInfixOf)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist, getTemporaryDirectory, listDirectory, removeDirectoryRecursive)
import GHC.IO.Encoding (char8, getFileSystemEncoding, getLocaleEncoding, setFileSystemEncoding, setLocaleEncoding)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.IO (IOMode (..), hGetContents, hPutStr, withBinaryFile)
import System.Process (CreateProcess (..), proc, readCreateProcessWithExitCode, readProcessWithExitCode)

import Cli
import qualified Mir as M
import MirEval (renderMirValue, runProgram)
import MirLower (lowerProgram)
import LlvmEmit (emitProgram)
import Native (buildExecutable, buildExecutableWith, runExecutable)
import Parse (parseStatementBlock)
import Pipeline
import TestHarness
import Utils

-- Native code: the LLVM IR of a program, and the executable clang builds from it. The executable has to do what the
-- executor of the MIR does, so each program here is built, run, and compared with `tersus eval`: the same output, the same
-- error and the same exit status. The builds need clang, and pass without it.

testNative :: Test
testNative =
    TestList
        "testNative"
        [ testNativeIr
        , TestList "examples" [testNativeProgram path | path <- nativeExamples]
        , TestList "arithmetic" [TestCase name (sameAsMir name source) | (name, source) <- arithmeticPrograms]
        , TestList "lists" [TestCase name (sameAsMir name source) | (name, source) <- listPrograms]
        , TestList "strings" [TestCase name (sameAsMir name source) | (name, source) <- stringPrograms]
        , TestList "bytes" [TestCase name (sameAsMir name source) | (name, source) <- bytePrograms]
        , TestList "files" ([TestCase name (sameAsMirFiles name files source) | (name, files, source) <- filePrograms] ++ [testUnwritableFile])
        , TestList "arguments" [TestCase name (sameAsMirWorld name (noWorld{worldArgs = map encodeUtf8 args}) source) | (name, args, source) <- argumentPrograms]
        , TestList "error" [TestCase name (sameAsMir name source) | (name, source) <- errorPrograms]
        , TestList "output" [TestCase name (sameAsMir name source) | (name, source) <- outputPrograms]
        , TestList "input" [TestCase name (sameAsMirWithInput name input source) | (name, input, source) <- inputPrograms]
        , TestList "arrays" [TestCase name (sameAsMir name source) | (name, source) <- arrayPrograms]
        , TestList "data" [TestCase name (sameAsMir name source) | (name, source) <- dataPrograms]
        , TestList "a list written in Tersus" [TestCase name (sameAsMir name (vecLibrary ++ body)) | (name, body) <- vecPrograms]
        , TestList "methods of generic structs" [TestCase name (sameAsMir name source) | (name, source) <- genericImplPrograms]
        , TestList "function values" [TestCase name (sameAsUnvalidated name source) | (name, source) <- functionPrograms]
        , TestList "control flow" [TestCase name (sameAsMir name source) | (name, source) <- controlPrograms]
        , TestList "build" [testBuildKeepsFiles, testEveryExampleIsBuilt, testRunExecutable]
        , TestList "memory" memoryTests
        , TestList "stops" [TestCase name (sameAsMir name source) | (name, source) <- stopPrograms]
        , TestList "layout" [TestCase name (sameAsMir name source) | (name, source) <- layoutPrograms]
        , TestList "layout and C" [TestCase name (nativeOnly i name source expected) | (i, (name, source, expected)) <- zip [1 :: Int ..] cPrograms]
        ]

-- Values laid out as C lays them out (Mir.layoutOf): narrow numbers stored and loaded, structs and enums with their fields at aligned offsets, printed and
-- compared by their descriptors, as the executor of the MIR has them
layoutPrograms :: [(String, String)]
layoutPrograms =
    [ ("a struct of fixed-width fields", "struct H { kind: U16, flags: Byte, length: I32, ok: Bool, small: I8 }; return H { kind: 60000, flags: 255, length: -5, ok: true, small: -128 };")
    , ("compared", "struct H { kind: U16, length: I32 }; a = H { kind: 1, length: -2 }; b = H { kind: 1, length: -2 }; return a = b;")
    , ("in a list", "l = push(push(push([], I32::from(-7)), I32::from(2000000000)), I32::from(0)); return toInt(get(l, 0)) + toInt(get(l, 1));")
    , ("in an array", "a = array(3, U16::from(65535)); a = set(a, 1, U16::from(7)); return a;")
    , ("Bools in a list and an array", "l = push(push([], true), false); a = #[true, false, true]; if get(a, 2) && !get(l, 1) { return size(l) + size(a); }; return 0;")
    , ("an enum with narrow fields", "enum E { A { x: Byte }, B { y: I16, z: Int } }; e = E::B { y: -300, z: 9 }; return e;")
    , ("in memory", "(p, b) = Addr::alloc(3); b = Addr::write(p, 0, I32::from(-1), b); b = Addr::write(p, 2, I32::from(5), b); x = Addr::get(p, 0, b); b = Addr::dropValue(p, 0, b); y = Addr::get(p, 2, b); b = Addr::dropValue(p, 2, b); return toInt(x) * 10 + toInt(y) + Addr::free(p, b);")
    , ("a Box of a narrow value", "b = Box::new(I8::from(-3)); return toInt(Box::unbox(b));")
    ]

-- Programs that only native code runs (they call C), with what they print
cPrograms :: [(String, String, String)]
cPrograms =
    [ ("a struct takes the bytes of the same struct of C", "struct H { kind: U16, flags: Byte, length: I32 }; (p, b) = Addr::alloc(2); b = Addr::write(p, 0, H { kind: 1, flags: 2, length: 3 }, b); n = Addr::toInt(Addr::offset(p, 1)) - Addr::toInt(p); b = Addr::dropValue(p, 0, b); d = Addr::free(p, b); return n;", "8\n")
    , ("an enum is a U32 tag and its widest variant", "enum E { A { x: Byte }, B { y: Int } }; (p, b) = Addr::alloc(1); b = Addr::write(p, 0, E::B { y: 3 }, b); n = Addr::toInt(Addr::offset(p, 1)) - Addr::toInt(p); b = Addr::dropValue(p, 0, b); d = Addr::free(p, b); return n;", "16\n")
    , ("C reads the bytes of memory the program wrote", "extern fn strlen(p: Addr<Byte>) -> Int [{ }] [{ affirm return >= 0; }]; (p, b) = Addr::alloc(3); b = Addr::write(p, 0, toByte(104), b); b = Addr::write(p, 1, toByte(105), b); b = Addr::write(p, 2, toByte(0), b); n = strlen(p); b = Addr::dropRange(p, 0, 3, b); return n + Addr::free(p, b);", "2\n")
    , ("memory that C allocated", "extern fn malloc(bytes: Int) -> Addr<Int> [{ affirm bytes > 0; }] [{ }]; extern fn free(p: Addr<Int>, ghost b: Block<Int>) -> Int [{ affirm count(b) = 0; }] [{ }]; p = malloc(16); b = Block::assume(p, 2); b = Addr::write(p, 1, 42, b); (x, b) = Addr::take(p, 1, b); d = free(p, b); return x;", "42\n")
    ]

-- Builds the program with the memory checks of the runtime and runs it: it has to print what is expected
nativeOnly :: Int -> String -> String -> String -> IO TestResult
nativeOnly i name source expected = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else case llvmSource source of
            Error e -> pure (Just e)
            Ok ir -> buildAndRun "" [] ("c_program_" ++ show i) name ir (ExitSuccess, expected, "")

-- Every example that validates
nativeExamples :: [FilePath]
nativeExamples =
    [ "examples/" ++ name ++ ".tersus"
    | name <-
        [ "arithmetic", "array_data", "array_owners", "array_sizes", "arrays", "args", "basics", "booleans", "borrowing", "box_array", "branching", "build_list", "bytes", "contracts", "early_return", "element_facts"
        , "enums", "files", "for_loops", "forall_facts", "frame_facts", "functions", "generic_lists", "generic_structs", "hello", "helper_functions", "linear"
        , "linked_list", "loop_return", "loops", "packet_parser", "parallel_sum", "proofs", "recursion", "rewrites", "rules"
        , "list_methods", "safe_access", "sized_structs", "spec_functions", "structs", "termination", "traits", "type_parameters", "types", "update_list", "upper", "vec", "addresses", "drops", "strings", "text", "mir_reader", "emit"
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
        , TestCase "a list is the struct of the library, which holds its elements in memory at an address" . pure $
            withIr "x = push([1], 2); return x;" (\ir -> testAssertTrue ("@\"data.StdList<Int>\" = private constant" `isInfixOf` ir && "call i64 @tersus_addr_alloc" `isInfixOf` ir && "call i64 @tersus_addr_resize" `isInfixOf` ir && not ("tersus_list_" `isInfixOf` ir && "call ptr @tersus_list_" `isInfixOf` ir)))
        , TestCase "a struct is held in the frame, as its fields, with a descriptor" . pure $
            withIr "struct P { x: Int, y: Int }; p = P { x: 1, y: 2 }; return p;" (\ir -> testAssertTrue ("= alloca [2 x i64]" `isInfixOf` ir && "@\"data.P\" = private constant" `isInfixOf` ir && not ("tersus_data_new" `isInfixOf` ir)))
        , TestCase "an enum value is a tag (a U32) and the widest of its variants, in the frame" . pure $
            withIr "enum S { A, B { w: Int } }; x = S::B { w: 2 }; return x is S::B;" (\ir -> testAssertTrue ("= alloca [2 x i64]" `isInfixOf` ir && "store i32 1, ptr" `isInfixOf` ir && "icmp eq i32" `isInfixOf` ir))
        , TestCase "a Box takes room on the heap for what it holds" . pure $
            withIr "struct P { x: Int, y: Int }; b = Box::new(P { x: 1, y: 2 }); return b.y;" (\ir -> testAssertTrue ("call i64 @tersus_addr_alloc(i64 1, i64 16)" `isInfixOf` ir && "call void @\"fn.stdBoxNew<P>\"" `isInfixOf` ir))
        , TestCase "a Box of an array is a list of the library" . pure $
            withIr "a = Array::boxed(3, 1); b = Box::new(#[1, 2]); return size(a) + get(b, 1);" (\ir -> testAssertTrue ("@\"fn.stdListFilled<Int>\"" `isInfixOf` ir && "call i64 @tersus_addr_alloc(i64 2, i64 8)" `isInfixOf` ir && not ("call ptr @tersus_box_new" `isInfixOf` ir)))
        , TestCase "a Box is the struct of the library, freed by its drop" . pure $
            withIr "b = Box::new(5); return Box::unbox(b);" (\ir -> testAssertTrue ("@\"fn.<StdBox<Int> as Drop>::drop\"" `isInfixOf` ir && "@\"fn.stdBoxUnbox<Int>\"" `isInfixOf` ir && not ("call ptr @tersus_box_new" `isInfixOf` ir)))
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
                Right program -> case emitProgram (nativeProgram program) of
                    Error e -> Just e
                    Ok ir -> testAssertTrue ("store ptr @\"fn.inc\"" `isInfixOf` ir && "call i64 %" `isInfixOf` ir)
        , TestCase "a function with a size is made for each size it is called with" . pure $
            withIr "fn count<n>(a: Array<Int, n>) -> Int { return n; }; return count(#[1, 2, 3]) + count(#[1]) + count(#[4, 5, 6]);" (\ir -> testAssertTrue ("@\"fn.count<3>\"" `isInfixOf` ir && "@\"fn.count<1>\"" `isInfixOf` ir && not ("@\"fn.count\"" `isInfixOf` ir)))
        , TestCase "an array that a size makes too large for a frame is refused when the size is known" . pure $
            testAssertErrorContains "In f<8192>: " (llvmSource "fn f<n>(a: Array<Int, n>) -> Int { b = array(n, a); return size(b); }; return f(array(8192, 0));")
        , TestCase "a list that is moved to the call is not copied" . pure $
            withIr "fn total(a: List<Int>) -> Int { return size(a); }; l = push([], 1); return total(l);" (\ir -> testAssertTrue (not ("call void @tersus_clone" `isInfixOf` ir)))
        , TestCase "a list that is lent is not copied for the call" . pure $
            withIr "fn total(a: &List<Int>) -> Int { return size(a); }; l = push([], 1); return total(l) + total(l);" (\ir -> testAssertTrue (not ("call void @tersus_clone" `isInfixOf` ir)))
        , TestCase "a list that is cloned for a call is copied, and one that is moved is not" . pure $
            withIr "fn total(a: List<Int>) -> Int { return size(a); }; l = push([], 1); return total(clone(l)) + total(l);" (\ir -> testAssertTrue ("call void @tersus_clone" `isInfixOf` ir))
        , TestCase "an array that is lent is read where it is, and one that is given is copied into the function" . pure $
            withIr "fn ends(a: &Array<Int, 4>) -> Int { return get(a, 0) + get(a, 3); }; x = #[1, 2, 3, 4]; return ends(x);" (\ir -> testAssertTrue ("define internal i64 @\"fn.ends\"(ptr %l.1)" `isInfixOf` ir))
        , TestCase "an array that is given has room of its own in the function" . pure $
            withIr "fn ends(a: Array<Int, 4>) -> Int { return get(a, 0) + get(a, 3); }; x = #[1, 2, 3, 4]; return ends(x);" (\ir -> testAssertTrue ("define internal i64 @\"fn.ends\"(ptr %p.1)" `isInfixOf` ir && "%l.1 = alloca [4 x i64]" `isInfixOf` ir))
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
    , ("recursive enum", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; return T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Node { l: Box::new(T::Leaf), v: 2, r: Box::new(T::Leaf) }) };")
    , ("recursive function", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; fn sum(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; }; return sum(Box::new(T::Node { l: Box::new(T::Node { l: Box::new(T::Leaf), v: 3, r: Box::new(T::Leaf) }), v: 1, r: Box::new(T::Node { l: Box::new(T::Leaf), v: 2, r: Box::new(T::Leaf) }) }));")
    , ("equal structs", "struct P { x: Int, y: List<Int> }; p = P { x: 1, y: [2, 3] }; q = P { y: [2, 3], x: 1 }; return p = q;")
    , ("different structs", "struct P { x: Int, y: List<Int> }; p = P { x: 1, y: [2, 3] }; q = P { x: 1, y: [2] }; return p = q;")
    , ("unequal structs", "struct P { x: Int }; return P { x: 1 } != P { x: 2 };")
    , ("equal variants", "enum S { A { r: Int }, C }; a = S::A { r: 1 }; return a = S::A { r: 1 };")
    , ("variants with other fields", "enum S { A { r: Int }, C }; a = S::A { r: 1 }; return a = S::A { r: 2 };")
    , ("different variants", "enum S { A { r: Int }, C }; a = S::A { r: 1 }; return a = S::C;")
    , ("fieldless variants", "enum S { A { r: Int }, C }; return S::C = S::C;")
    , ("equal trees", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; a = T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Leaf) }; return a = T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Leaf) };")
    , -- Box: what a struct or an enum is held in
      ("a boxed struct", "struct P { x: Int, y: Int }; b = Box::new(P { x: 4, y: 5 }); return b;")
    , ("a field of a box", "struct P { x: Int, y: Int }; b = Box::new(P { x: 4, y: 5 }); return b.x * 10 + b.y;")
    , ("unbox", "struct P { x: Int, y: Int }; b = Box::new(P { x: 4, y: 5 }); p = Box::unbox(b); return p;")
    , ("a box is used twice", "struct P { x: Int, y: Int }; impl Clone for P { }; b = Box::new(P { x: 4, y: 5 }); c = clone(b); return b = c;")
    , ("a box in a struct", "struct P { x: Int }; struct Q { p: Box<P>, n: Int }; return Q { p: Box::new(P { x: 3 }), n: 5 };")
    , ("boxes in a list", "struct P { x: Int }; ps = push(push([], Box::new(P { x: 1 })), Box::new(P { x: 2 })); return get(ps, 1).x + size(ps);")
    , ("a tree is used twice", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; impl Clone for T { }; fn sum(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; }; t = Box::new(T::Node { l: Box::new(T::Leaf), v: 3, r: Box::new(T::Node { l: Box::new(T::Leaf), v: 4, r: Box::new(T::Leaf) }) }); return sum(clone(t)) * 10 + sum(t);")
    , ("a chain", "enum C { End, Link { v: Int, rest: Box<C> } }; fn len(c: Box<C>) -> Int shrinks c { return match c { C::End => 0, C::Link { v: v, rest: r } => 1 + len(r) }; }; return len(Box::new(C::Link { v: 1, rest: Box::new(C::Link { v: 2, rest: Box::new(C::End) }) }));")
    , ("a tree built in a loop", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; fn sum(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; }; t = Box::new(T::Leaf); i = 0; while i < 200 [{ affirm i >= 0; }] shrinks 200 - i { t = Box::new(T::Node { l: t, v: i, r: Box::new(T::Leaf) }); i = i + 1; }; return sum(t);")
    , -- structs and enums are held inline, as their words
      ("a struct in a struct", "struct In { a: Int, b: Int }; struct Out { i: In, c: Int }; o = Out { i: In { a: 1, b: 2 }, c: 3 }; return o;")
    , ("a field of a field", "struct In { a: Int, b: Int }; struct Out { i: In, c: Int }; o = Out { i: In { a: 1, b: 2 }, c: 3 }; return o.i.b * 10 + o.c;")
    , ("a struct in a variant", "struct P { x: Int, y: Int }; enum E { A { p: P }, B }; e = E::A { p: P { x: 1, y: 2 } }; return e;")
    , ("a match takes a struct out of a variant", "struct P { x: Int, y: Int }; enum E { A { p: P }, B }; e = E::A { p: P { x: 1, y: 2 } }; return match e { E::A { p: p } => p.x + p.y, E::B => 0 };")
    , ("a list of structs", "struct P { x: Int, y: Int }; ps = push(push([], P { x: 1, y: 2 }), P { x: 3, y: 4 }); return ps;")
    , ("a field of an element of a list of structs", "struct P { x: Int, y: Int }; ps = push(push([], P { x: 1, y: 2 }), P { x: 3, y: 4 }); return get(ps, 1).x * 10 + size(ps);")
    , ("first and last of a list of structs", "struct P { x: Int, y: Int }; ps = push(push([], P { x: 1, y: 2 }), P { x: 3, y: 4 }); return last(ps).y + first(ps).x;")
    , ("set in a list of structs", "struct P { x: Int, y: Int }; ps = push(push([], P { x: 1, y: 2 }), P { x: 3, y: 4 }); ps = set(ps, 0, P { x: 9, y: 9 }); return ps;")
    , ("a list of enums of different widths", "enum E { A { v: Int }, B { x: Int, y: Int }, C }; return push(push(push([], E::A { v: 1 }), E::B { x: 2, y: 3 }), E::C);")
    , ("a list of structs with lists", "struct S { xs: List<Int> }; return push(push([], S { xs: [1] }), S { xs: [2, 3] });")
    , ("a list of structs with lists is used twice", "struct S { xs: List<Int> }; impl Clone for S { }; ss = push(push([], S { xs: [1] }), S { xs: [2, 3] }); tt = clone(ss); tt = set(tt, 0, S { xs: [] }); return ss;")
    , ("a struct with a list is passed and returned", "struct S { n: Int, xs: List<Int> }; fn grow(s: S) -> S { return S { n: s.n + 1, xs: push(s.xs, s.n) }; }; return grow(grow(S { n: 0, xs: [] }));")
    , ("a struct with a list is used twice", "struct S { n: Int, xs: List<Int> }; impl Clone for S { }; a = S { n: 1, xs: [2] }; b = clone(a); return b = a;")
    , ("a struct is updated in a loop", "struct S { n: Int, xs: List<Int> }; s = S { n: 0, xs: [] }; i = 0; while i < 100 [{ affirm i >= 0; }] shrinks 100 - i { s = S { n: s.n + 1, xs: push(s.xs, i) }; i = i + 1; }; return s.n + size(s.xs);")
    , ("a struct is assigned again", "struct S { xs: List<Int> }; s = S { xs: [1] }; s = S { xs: [2, 3] }; return s;")
    , ("a Box of a struct with a list", "struct S { xs: List<Int> }; b = Box::new(S { xs: [1, 2] }); c = b; return c.xs;")
    , ("a struct made in a function in a loop", "struct S { n: Int, xs: List<Int> }; fn mk(i: Int) -> S { return S { n: i, xs: push([], i) }; }; t = 0; i = 0; while i < 1000 [{ affirm i >= 0; }] shrinks 1000 - i { s = mk(i); t = t + s.n + size(s.xs); i = i + 1; }; return t;")
    , ("an enum with a list is used twice", "enum E { A { xs: List<Int> }, B }; impl Clone for E { }; e = E::A { xs: [1, 2] }; f = clone(e); return e = f;")
    , ("a list taken out of a nested struct", "struct In { xs: List<Int> }; struct Out { i: In, n: Int }; o = Out { i: In { xs: [1, 2] }, n: 3 }; return o.i.xs;")
    , ("a nested struct with a list is passed", "struct In { xs: List<Int> }; struct Out { i: In, n: Int }; fn total(o: Out) -> Int { return size(o.i.xs) + o.n; }; return total(Out { i: In { xs: [1, 2] }, n: 3 });")
    , ("a struct holds a Box that holds a struct", "struct P { x: Int }; struct Q { b: Box<P>, n: Int }; q = Q { b: Box::new(P { x: 4 }), n: 5 }; r = q; return r;")
    , ("a Box is cast and read", "enum E { A { v: Int }, B }; b = Box::new(E::A { v: 7 }); return (b as E::A).v;")
    , ("a Box is unboxed and boxed again", "struct P { x: Int, xs: List<Int> }; b = Box::new(P { x: 1, xs: [2] }); p = Box::unbox(b); c = Box::new(p); return c;")
    , -- a struct has no tag: it is its own constructor, and `is` and `as` of it are about its type
      ("a struct is its own type", "struct P { x: Int }; p = P { x: 7 }; return p is P;")
    , ("an empty struct is its own type", "struct E {}; e = E {}; return e is E;")
    , ("a Box of a struct is its own type", "struct P { x: Int }; b = Box::new(P { x: 4 }); return b is P;")
    , ("a struct is cast to itself and passed", "struct P { x: Int, y: Int }; fn f(p: P) -> Int { return p.y; }; p = P { x: 1, y: 2 }; q = p as P; return f(q);")
    , ("a struct with a list is cast to itself and passed", "struct P { x: Int, xs: List<Int> }; fn f(p: P) -> Int { return size(p.xs) + p.x; }; p = P { x: 1, xs: [2, 3] }; q = p as P; return f(q);")
    , ("a Box of a struct is cast to it", "struct P { x: Int, y: Int }; b = Box::new(P { x: 4, y: 5 }); q = b as P; return q.y;")
    , ("a loop walks down a tree", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; fn depth(t: Box<T>) -> Int { d = 0; while t is T::Node shrinks t { t = (t as T::Node).l; d = d + 1; }; return d; }; return depth(Box::new(T::Node { l: Box::new(T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Leaf) }), v: 2, r: Box::new(T::Leaf) }));")
    , ("lists of structs equal", "struct P { x: Int }; l = push([], P { x: 1 }); return l = push([], P { x: 1 });")
    , ("data parameter and result", "struct P { x: Int, y: Int }; fn swap(p: P) -> P { return P { x: p.y, y: p.x }; }; return swap(P { x: 1, y: 2 });")
    , ("data built in a loop", "struct P { x: Int }; l = []; i = 0; while i < 50 [{ affirm i >= 0; }] shrinks 50 - i { l = push(l, P { x: i }); i = i + 1; }; return size(l);")
    , ("a variant returned in a branch only", "enum S { A { r: Int }, C }; x = S::C; if x is S::A { return x; };")
    ]

-- Function values. The validator cannot yet follow a call of a function that is a value, so these are lowered without
-- validation (as the MIR tests are) and compared with the executor of the MIR.
functionPrograms :: [(String, String)]
functionPrograms =
    [ ("a function that lends is a value", "fn total(a: &List<Int>) -> Int { return size(a); }; f = total; l = push([], 1); return f(l) + f(l) + size(l);")
    , ("a function that lends is a parameter", "fn total(a: &List<Int>) -> Int { return size(a); }; fn apply(f: fn(&List<Int>) -> Int, l: List<Int>) -> Int { return f(l) + f(l); }; return apply(total, push([], 1));")
    , ("a function as a result", "fn inc(n: Int) -> Int { return n + 1; }; return inc;")
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

-- Strings are the library struct String over a list of bytes (lib/string.tersus), so native code has nothing of its own for them
stringPrograms :: [(String, String)]
stringPrograms =
    [ ("an Int as text", "return String::fromInt(0 - 4072);")
    , ("the least Int as text", "return String::fromInt(0 - 9223372036854775807 - 1);")
    , ("0 as text", "return String::fromInt(0);")
    , ("a slice", "return \"abcdef\".slice(1, 4);")
    , ("find", "return \"hello world\".find(toByte(32), 0) * 10 + \"abc\".find(toByte(122), 0);")
    , ("starts with", "return \"hello\".startsWith(\"he\") && !\"hello\".startsWith(\"hx\");")
    , ("literal", "return \"hi\";")
    , ("empty", "return \"\";")
    , ("utf-8", "return \"caf\\u{e9}\\u{1f600}\";")
    , ("concat", "s = \"ab\"; t = s.concat(\"cd\"); return t;")
    , ("a string that is borrowed twice", "t = \"x\"; s = \"a\".concat(t).concat(t); return size(s) * 10 + size(t);")
    , ("push and set", "s = \"ab\".push(toByte(99)); return set(s, 0, toByte(65));")
    , ("equal", "return \"ab\" = \"a\".push(toByte(98));")
    , ("not equal", "return \"ab\" = \"ac\";")
    , ("in a struct and a list", "struct Named { name: String, n: Int }; xs = push(push([], Named { name: \"a\", n: 1 }), Named { name: \"bc\", n: 2 }); return xs;")
    , ("in an enum", "enum E { S { s: String }, N }; fn f(e: E) -> Int [{ }] [{ }] { return match e { E::S { s: s } => size(s), E::N => 0 }; }; return f(E::S { s: \"abc\" });")
    ]

-- A Byte is a word, like an Int: the same on the MIR and natively
bytePrograms :: [(String, String)]
bytePrograms =
    [ ("a Byte as an Int", "b = toByte(200); return toInt(b) + 1;")
    , ("the ends of the range", "return toInt(toByte(0)) * 1000 + toInt(toByte(255));")
    , ("Bytes are equal", "b = toByte(9); c = toByte(4 + 5); if b = c { return 1; }; return 0;")
    , ("a Byte in a struct", "struct P { r: Byte, g: Byte }; p = P { r: toByte(1), g: toByte(2) }; return p;")
    , ("a list of Bytes", "bs = push(push(push([], toByte(1)), toByte(2)), toByte(255)); return bs;")
    , ("a list of Bytes is read", "bs = push(push([], toByte(7)), toByte(9)); return toInt(get(bs, 1)) * 10 + toInt(first(bs));")
    , ("a Byte is passed and returned", "fn next(b: Byte) -> Byte [{ affirm toInt(b) < 255; }] [{ }] { return toByte(toInt(b) + 1); }; return next(toByte(41));")
    , ("a list of Bytes is passed", "fn total(a: &List<Byte>) -> Int [{ }] [{ }] { n = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { n = n + toInt(get(a, i)); i = i + 1; }; return n; }; return total(push(push([], toByte(100)), toByte(200)));")
    , ("an array of Bytes", "a = #[1, 2, 3]; return toInt(toByte(get(a, 2)));")
    , ("a Byte is written", "b = toByte(72); writeByte(b); writeByte(105); return 0;")
    , ("a Byte in an enum", "enum E { A { b: Byte }, N }; e = E::A { b: toByte(5) }; return e;")
    ]

-- What a program reads and writes of files is the same on the MIR and natively
filePrograms :: [(String, [(FilePath, String)], String)]
filePrograms =
    [ ("read a file", [("in.txt", "hello file\nline 2\n")], "t = String::readFile(\"in.txt\", 1000); t.print(); return size(t);")
    , ("a file that is not there", [], "t = String::readFile(\"nope.txt\", 1000); return size(t) * 10 + (0 - String::fileSize(\"nope.txt\"));")
    , ("the size of a file", [("a.bin", "abcdefg")], "return String::fileSize(\"a.bin\");")
    , ("cut at the limit", [("a.txt", "0123456789")], "t = String::readFile(\"a.txt\", 4); t.print(); return size(t);")
    , ("write a file", [], "r = \"written\\n\".writeFile(\"out.txt\"); return r;")
    , ("write over a file", [("out.txt", "a long old text\n")], "r = \"new\".writeFile(\"out.txt\"); return r;")
    , ("copy a file", [("src.txt", "copy me\n")], "t = String::readFile(\"src.txt\", 1000); r = t.writeFile(\"dst.txt\"); return r;")
    , ("read what was written", [], "r = \"abc\".writeFile(\"x.txt\"); t = String::readFile(\"x.txt\", 10); t.print(); return size(t) + r;")
    , ("a file of all the bytes", [("all.bin", map toEnum [0 .. 255])], "t = String::readFile(\"all.bin\", 1000); r = t.writeFile(\"copy.bin\"); return size(t) * 10 + (0 - r);")
    , ("an empty file", [("empty.txt", "")], "t = String::readFile(\"empty.txt\", 10); return String::fileSize(\"empty.txt\") * 100 + size(t);")
    , ("UTF-8 in a name", [("caf\195\169.txt", "x")], "t = String::readFile(\"caf\\u{e9}.txt\", 10); return size(t);")
    , ("no path", [], "r = \"x\".writeFile(\"\"); return 0 - r;")
    , ("two spellings of one file", [], "\"1\".writeFile(\"x\"); \"2\".writeFile(\"./x\"); \"3\".writeFile(\"x\"); t = String::readFile(\".//x\", 10); t.print(); return size(t);")
    , ("two files", [("a.txt", "AAA"), ("b.txt", "BB")], "a = String::readFile(\"a.txt\", 10); b = String::readFile(\"b.txt\", 10); r = a.clone().concat(b).writeFile(\"ab.txt\"); return size(a) * 10 + size(b);")
    ]

-- What a program is given as arguments is the same on the MIR and natively
argumentPrograms :: [(String, [String], String)]
argumentPrograms =
    [ ("none", [], "return argCount();")
    , ("a count", ["a", "bc", "def"], "return argCount();")
    , ("a byte", ["A"], "return argByte(0, 0);")
    , ("no such byte", ["A"], "return argByte(0, 1);")
    , ("no such argument", ["A"], "return argByte(1, 0);")
    , ("a negative index", ["A"], "return argByte(0 - 1, 0) * 10 + argByte(0, 0 - 1);")
    , ("an argument", ["hello"], "s = String::arg(0, 100); s.print(); return size(s);")
    , ("all of them", ["a", "b c", "d"], "n = argCount(); i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] ~ { String::arg(i, 100).print(); writeByte(10); i = i + 1; }; return n;")
    , ("an argument longer than the limit", ["abcdef"], "s = String::arg(0, 3); s.print(); return size(s);")
    , ("UTF-8", ["caf\233 \8364"], "s = String::arg(0, 100); s.print(); return size(s);")
    , ("an empty argument", [""], "s = String::arg(0, 100); return argCount() * 10 + size(s);")
    ]

-- What a program writes to the standard error is the same too, and comes out on the other stream
errorPrograms :: [(String, String)]
errorPrograms =
    [ ("a byte", "writeError(69); return 1;")
    , ("a string", "n = \"oops\\n\".printError(); return n;")
    , ("both streams", "\"out\".print(); \"err\".printError(); writeByte(33); writeError(33); return 0;")
    , ("UTF-8", "n = \"caf\\u{e9}\".printError(); return n;")
    , ("in a loop", "i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { writeError(toByte(48 + i)); i = i + 1; }; return i;")
    , ("nothing on the standard output", "\"to stderr\".printError(); return 7;")
    ]

-- What a program reads is the same on the MIR and natively: they are given the same input
inputPrograms :: [(String, String, String)]
inputPrograms =
    [ ("a byte", "A", "return readByte();")
    , ("the end of the input", "", "return readByte();")
    , ("a byte after the end", "A", "a = readByte(); b = readByte(); c = readByte(); return a * 1000000 + (b + 1) * 1000 + (c + 1);")
    , ("a byte of 255", "\255", "return readByte();")
    , ("echo", "abc", "a = readByte(); b = readByte(); c = readByte(); if a >= 0 { writeByte(toByte(a)); }; if b >= 0 { writeByte(toByte(b)); }; if c >= 0 { writeByte(toByte(c)); }; return 0;")
    , ("a loop until the end", "hello", "n = 0; c = readByte(); while c >= 0 [{ affirm n >= 0; affirm c >= 0 - 1; affirm c < 256; }] ~ { n = n + 1; c = readByte(); }; return n;")
    , ("a line", "first\nsecond\n", "l = String::readLine(100); l.print(); return size(l);")
    , ("two lines", "first\nsecond\nthird", "a = String::readLine(100); b = String::readLine(100); a.print(); writeByte(124); b.print(); return size(a) * 100 + size(b);")
    , ("the last line has no new line", "last", "a = String::readLine(100); return size(a);")
    , ("no input", "", "a = String::readLine(100); b = String::read(100); return size(a) + size(b);")
    , ("a line longer than the limit", "abcdefgh\nxy", "a = String::readLine(3); b = String::readLine(100); a.print(); writeByte(124); b.print(); return size(a) * 100 + size(b);")
    , ("all of the input", "one\ntwo\n", "a = String::read(1000); a.print(); return size(a);")
    , ("a limit of 0 reads nothing", "abc", "a = String::read(0); b = String::read(10); b.print(); return size(a) * 10 + size(b);")
    , ("UTF-8 passes through", "caf\195\169\n", "a = String::readLine(100); a.print(); return size(a);")
    , ("bytes that are not UTF-8 pass through", "\255\254\n", "a = String::readLine(100); a.print(); return size(a);")
    , ("the read is validated", "xyz", "a = String::read(2); affirm size(a) <= 2; return size(a);")
    ]

-- What a program writes is the same on the MIR and natively: the bytes, then the value on a line of its own
outputPrograms :: [(String, String)]
outputPrograms =
    [ ("a byte", "writeByte(104); writeByte(105); return 1;")
    , ("a byte is its value", "x = writeByte(65); return x;")
    , ("the ends of the range", "writeByte(0); writeByte(255); writeByte(toByte(65)); return 0;")
    , ("a string", "\"ab\\n\".print(); return 7;")
    , ("UTF-8", "n = \"caf\\u{e9}\\u{1f600}\".print(); return n;")
    , ("bytes that are not UTF-8", "writeByte(255); writeByte(65); writeByte(0); return 0;")
    , ("in the order of the calls", "\"a\".print(); writeByte(98); \"c\".concat(\"d\").print(); return 0;")
    , ("in a loop", "i = 0; while i < 5 [{ affirm i >= 0; affirm i <= 5; }] shrinks 5 - i { writeByte(toByte(48 + i)); i = i + 1; }; return i;")
    , ("in a function", "fn shout(s: String) -> Int [{ }] [{ }] { n = s.print(); writeByte(33); return n + 1; }; return shout(\"hey\");")
    , ("a string that is printed twice", "s = \"ab\"; s.print(); s.print(); return size(s);")
    , ("a long string", "s = \"0123456789\"; i = 0; while i < 20 [{ affirm i >= 0; affirm i <= 20; }] shrinks 20 - i { s = s.clone().concat(s); i = i + 1; if i = 3 { return s.print(); }; }; return 0;")
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
    , ("push does not change its argument", "x = [1]; y = push(clone(x), 2); return x;")
    , ("set", "x = [1, 2, 3]; y = set(x, 1, 9); return y;")
    , ("set does not change its argument", "x = [1, 2, 3]; y = set(clone(x), 1, 9); return x;")
    , ("push to an empty list of lists", "x = [1, 2]; rows = push([], x); rows = push(rows, [3]); return rows;")
    , ("set a list in a list", "rows = [[1], [2]]; rows = set(rows, 0, [7, 8]); return rows;")
    , ("get a list from a list", "rows = [[1], [2, 3]]; return clone(get(rows, 1));")
    , ("booleans in a list", "x = push([true], false); return get(x, 1) = false;")
    , ("last of booleans", "x = [false, true]; return last(x);")
    , ("an empty list among constants has the type that is read", "fn f() -> List<Bool> { return first([[]]); }; return f();")
    , ("pop", "l = push(push(push([], 1), 2), 3); l = pop(l); return l;")
    , ("pop of a constant whose first list is empty", "return pop([[], [true]]);")
    , ("pop and push again", "l = push(push([], [1]), [2]); l = pop(l); l = push(l, [3, 4]); return l;")
    , ("a list that was popped equals the shorter one", "a = push(push([], 1), 2); b = pop(a); return b = [1];")
    , ("pop in a loop", "l = []; i = 0; while i < 20 [{ affirm i >= 0; affirm i <= 20; affirm size(l) = i; }] shrinks 20 - i { l = push(l, i); i = i + 1; }; j = 0; while j < 15 [{ affirm j >= 0; affirm j <= 15; affirm size(l) = 20 - j; }] shrinks 15 - j { l = pop(l); j = j + 1; }; return l;")
    , ("methods", "l = []; l = l.push(3).push(4); return l.get(1) * 10 + l.size() + l.first() + l.last();")
    , ("lists with different room are equal", "a = push(push(push(push(push([], 1), 2), 3), 4), 5); b = push([], 1); b = push(b, 2); b = push(b, 3); b = push(b, 4); b = push(b, 5); return a = b;")
    , ("a list that grew is not a list that is longer", "a = push(push(push(push(push([], 1), 2), 3), 4), 5); b = push(clone(a), 6); return a = b;")
    , ("a list that grew prints as a list", "l = []; i = 0; while i < 11 [{ affirm i >= 0; affirm i <= 11; affirm size(l) = i; }] shrinks 11 - i { l = push(l, i * i); i = i + 1; }; return l;")
    , ("a list of lists that grew prints as one", "l = []; i = 0; while i < 6 [{ affirm i >= 0; affirm i <= 6; affirm size(l) = i; }] shrinks 6 - i { l = push(l, push([], i)); i = i + 1; }; return l;")
    , ("an empty list of lists", "l = []; l = push(l, []); l = push(l, [1]); return l;")
    , ("an empty list is equal to an empty list", "a = push([], 1); b = set(a, 0, 2); c = []; return c = [];")
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
    , ("a parameter assigned a part that is kept", "fn f(row: List<Int>, rows: List<List<Int>>) -> List<Int> [{ affirm size(rows) > 0; }] [{ }] { row = clone(get(rows, 0)); return row; }; return f([1], [[2, 3]]);")
    , ("a parameter assigned a field", "struct P { xs: List<Int> }; fn f(xs: List<Int>, p: P) -> Int { xs = p.xs; return size(xs); }; return f([1], P { xs: [2, 3] });")
    , ("a list that is not returned", "x = [1, 2];")
    , ("returned in a branch only", "x = [1]; if size(x) > 5 { return x; };")
    ]

-- Arrays are held inline, in the frame of the function: no pointer, nothing to free
arrayPrograms :: [(String, String)]
arrayPrograms =
    [ ("array of copies", "return array(3, 7);")
    , ("array of no elements", "return array(0, 7);")
    , ("array of zeros", "return array(5, 0);")
    , ("array of false", "return array(3, false);")
    , ("size is arithmetic", "return array(2 * 3 - 1, 4);")
    , ("literal", "return #[1, 2, 3];")
    , ("negative elements", "return #[-1, 2];")
    , ("empty literal", "a = #[]; return size(a);")
    , ("booleans", "return #[true, false, true];")
    , ("size, get, first and last", "a = #[4, 5, 6]; return size(a) * 1000 + get(a, 1) * 100 + first(a) * 10 + last(a);")
    , ("set", "a = #[1, 2, 3]; b = set(a, 1, 9); return b;")
    , ("set does not change its argument", "a = #[1, 2, 3]; b = set(a, 1, 9); return a;")
    , ("set again and again", "a = array(3, 0); a = set(a, 0, 1); a = set(a, 2, 3); a = set(a, 0, 4); return a;")
    , ("a copy is its own", "a = #[1, 2]; b = a; b = set(b, 0, 9); return a;")
    , ("a constant is read", "return get(#[7, 8, 9], 2) + first(#[5]) + last(#[1, 2]) + size(#[0, 0]);")
    , ("equality", "return #[1, 2] = #[1, 2];")
    , ("equality of a local and a constant", "a = array(2, 1); return a = #[1, 1];")
    , ("inequality", "a = #[1, 2]; return a != #[1, 3];")
    , ("equality of booleans", "return array(2, true) = #[true, true];")
    , ("a grid", "m = array(2, array(3, 1)); return m;")
    , ("a row of a grid", "m = array(2, array(3, 1)); m = set(m, 1, set(get(m, 1), 2, 9)); return get(m, 1);")
    , ("an element of a grid", "m = array(2, array(3, 1)); m = set(m, 1, set(get(m, 1), 2, 9)); return get(get(m, 1), 2);")
    , ("the last row", "m = set(array(3, array(2, 0)), 2, #[5, 6]); return last(m);")
    , ("a grid of grids", "return get(get(array(2, array(2, array(2, 3))), 1), 0);")
    , ("equality of grids", "return array(2, array(2, 1)) = array(2, array(2, 1));")
    , ("a parameter indexed under a contract", "fn pick(a: Array<Int, 3>, i: Int) -> Int [{ affirm i >= 0; affirm i < 3; }] [{ }] { return get(a, i); }; return pick(#[5, 6, 7], 2);")
    , ("an array parameter", "fn total(a: Array<Int, 4>) -> Int { s = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { s = s + get(a, i); i = i + 1; }; return s; }; return total(#[1, 2, 3, 4]);")
    , ("the argument is not changed", "fn bump(a: Array<Int, 2>) -> Array<Int, 2> { a = set(a, 0, 9); return a; }; x = array(2, 1); y = bump(x); return x;")
    , ("an array that is returned", "fn make() -> Array<Int, 4> { return array(4, 1); }; return make();")
    , ("a function given its own result", "fn bump(a: Array<Int, 2>) -> Array<Int, 2> { return set(a, 0, get(a, 0) + 1); }; x = array(2, 1); x = bump(x); x = bump(x); return x;")
    , ("two arrays given", "fn add(a: Array<Int, 2>, b: Array<Int, 2>) -> Array<Int, 2> { return set(set(array(2, 0), 0, get(a, 0) + get(b, 0)), 1, get(a, 1) + get(b, 1)); }; return add(#[1, 2], #[10, 20]);")
    , ("one array given twice", "fn same(a: Array<Int, 2>, b: Array<Int, 2>) -> Bool { return a = b; }; x = #[3, 4]; return same(x, x);")
    , ("a grid given", "fn corner(m: Array<Array<Int, 2>, 2>) -> Int { return get(get(m, 1), 1); }; return corner(set(array(2, array(2, 0)), 1, #[5, 6]));")
    , ("a recursive function with an array", "fn count(a: Array<Int, 2>, n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n = 0 { return get(a, 0); }; return count(set(a, 0, get(a, 0) + 1), n - 1); }; return count(#[0, 0], 5);")
    , ("filled in a loop", "a = array(300, 0); i = 0; while i < 300 [{ affirm i >= 0; affirm i <= 300; }] shrinks 300 - i { a = set(a, i, i * i); i = i + 1; }; return get(a, 299);")
    , ("a function that makes an array in a loop", "fn make(k: Int) -> Array<Int, 3> { return set(array(3, 0), 1, k); }; s = 0; i = 0; while i < 1000 [{ affirm i >= 0; affirm i <= 1000; }] shrinks 1000 - i { a = make(i); s = s + get(a, 1); i = i + 1; }; return s;")
    , ("a branch that sets", "a = array(2, 0); if size(a) > 1 { a = set(a, 0, 1); } else { a = set(a, 1, 1); }; return a;")
    , ("the most the frame can hold", "a = array(8192, 1); a = set(a, 8191, 5); return get(a, 8191) + get(a, 0) + size(a);")
    , ("a struct beside an array", "struct P { x: Int, ys: List<Int> }; p = P { x: 1, ys: [2, 3] }; a = array(2, p.x); return a;")
    , -- arrays in structs, enums and lists: their words in line
      ("a struct with an array field", "struct G { name: Int, cells: Array<Int, 3>, last: Int }; g = G { name: 1, cells: #[4, 5, 6], last: 9 }; return g;")
    , ("a field read after an array", "struct G { name: Int, cells: Array<Int, 3>, last: Int }; g = G { name: 1, cells: #[4, 5, 6], last: 9 }; return g.last * 100 + get(g.cells, 2) * 10 + g.name;")
    , ("an update around an array", "struct G { name: Int, cells: Array<Int, 3>, last: Int }; g = G { name: 1, cells: #[4, 5, 6], last: 9 }; h = G { cells: set(g.cells, 0, 7), ..g }; return h;")
    , ("the first struct after an update", "struct G { name: Int, cells: Array<Int, 3> }; g = G { name: 1, cells: #[4, 5, 6] }; h = G { cells: set(g.cells, 0, 7), ..g }; return g;")
    , ("a struct with an array is used twice", "struct G { name: Int, cells: Array<Int, 2> }; impl Clone for G { }; impl Copy for G { }; g = G { name: 1, cells: #[4, 5] }; h = g; return G { name: 2, cells: h.cells } = g;")
    , ("a struct with two arrays and a list", "struct G { a: Array<Int, 2>, xs: List<Int>, b: Array<Bool, 3> }; return G { a: #[1, 2], xs: [3], b: #[true, false, true] };")
    , ("equality of structs with arrays", "struct G { cells: Array<Int, 2> }; return G { cells: #[1, 2] } = G { cells: array(2, 1) };")
    , ("enum variants of different widths", "enum E { A { v: Array<Int, 2> }, B { x: Int, v: Array<Int, 4> }, C }; return E::B { x: 1, v: array(4, 7) };")
    , ("a match takes the array out", "enum E { A { v: Array<Int, 2> }, B { x: Int, v: Array<Int, 4> }, C }; e = E::B { x: 1, v: array(4, 7) }; return match e { E::A { v: v } => size(v), E::B { x: x, v: v } => get(v, 3) + x, E::C => 0 };")
    , ("a list of arrays", "rows = push(push([], #[1, 2]), #[3, 4]); return rows;")
    , ("a list of arrays is read", "rows = push(push([], #[1, 2]), #[3, 4]); return get(get(rows, 1), 0) * 10 + size(rows);")
    , ("first and last of a list of arrays", "rows = push(push([], #[1, 2]), #[3, 4]); return first(rows) = last(rows);")
    , ("last of a list of arrays", "rows = push(push([], #[1, 2]), #[3, 4]); return last(rows);")
    , ("set in a list of arrays", "rows = push(push([], #[1, 2]), #[3, 4]); rows = set(rows, 0, #[9, 9]); return rows;")
    , ("an empty list of arrays", "rows = push([], #[1]); rows = set(rows, 0, #[2]); return size(rows);")
    , ("a list of arrays that grows", "rows = []; i = 0; while i < 300 [{ affirm i >= 0; }] shrinks 300 - i { rows = push(rows, array(3, i)); i = i + 1; }; return get(get(rows, 299), 2) + size(rows);")
    , ("an empty list put in an array of lists has the type of the elements", "a = array(1, [true]); return set(a, 0, []);")
    , ("a list of arrays is used twice", "rows = push(push([], #[1, 2]), #[3, 4]); other = clone(rows); other = set(other, 0, #[0, 0]); return rows;")
    , ("lists of arrays are equal", "rows = push(push([], #[1, 2]), #[3, 4]); return rows = push(push([], #[1, 2]), #[3, 4]);")
    , ("a list of lists of arrays", "inner = push([], #[1, 2]); outer = push([], inner); return outer;")
    , ("an array of arrays in a list", "m = array(2, array(2, 5)); rows = push([], m); return get(get(get(rows, 0), 1), 0);")
    , ("an array in a struct in a list", "struct P { v: Array<Int, 2> }; ps = push([], P { v: #[3, 4] }); ps = push(ps, P { v: #[5, 6] }); return ps;")
    , ("a list of structs with arrays is used twice", "struct P { v: Array<Int, 2> }; impl Clone for P { }; ps = push([], P { v: #[3, 4] }); qs = clone(ps); qs = set(qs, 0, P { v: #[0, 0] }); return ps;")
    , ("a function takes and gives a struct with an array", "struct G { cells: Array<Int, 2> }; fn bump(g: G) -> G { return G { cells: set(g.cells, 0, get(g.cells, 0) + 1) }; }; return bump(bump(G { cells: #[1, 1] }));")
    , ("a function takes a list of arrays", "fn total(rows: List<Array<Int, 2>>) -> Int { s = 0; i = 0; while i < size(rows) [{ affirm i >= 0; affirm i <= size(rows); }] shrinks size(rows) - i { s = s + get(get(rows, i), 0) + get(get(rows, i), 1); i = i + 1; }; return s; }; return total(push(push([], #[1, 2]), #[3, 4]));")
    , ("a function gives a list of arrays", "fn make(n: Int) -> List<Array<Int, 2>> [{ affirm n >= 0; }] [{ }] { rows = []; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { rows = push(rows, array(2, i)); i = i + 1; }; return rows; }; return make(4);")
    , ("a list is lent", "fn total(a: &List<Int>) -> Int { t = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { t = t + get(a, i); i = i + 1; }; return t; }; l = push(push([], 3), 4); return total(l) + total(l) + size(l);")
    , ("a value made for the call is lent", "fn total(a: &List<Int>) -> Int { return size(a); }; return total(push(push([], 1), 2)) + total([1]);")
    , ("an array is lent", "fn ends(a: &Array<Int, 4>) -> Int { return get(a, 0) + get(a, 3); }; x = #[1, 2, 3, 4]; return ends(x) + ends(x) + get(x, 1);")
    , ("an array is lent to a function that gives another", "fn bump(a: &Array<Int, 3>) -> Array<Int, 3> { return set(a, 0, get(a, 0) + 1); }; x = #[1, 2, 3]; x = bump(x); x = bump(x); return x;")
    , ("a struct that owns a list is lent", "struct S { xs: List<Int>, n: Int }; fn count(s: &S) -> Int { return size(s.xs) + s.n; }; s = S { xs: push(push([], 1), 2), n: 10 }; return count(s) + count(s) + size(s.xs);")
    , ("a lent struct gives a copy of a part", "struct S { xs: List<Int>, n: Int }; fn part(s: &S) -> List<Int> { return clone(s.xs); }; s = S { xs: push([], 1), n: 10 }; l = part(s); l = push(l, 2); return s.xs;")
    , ("a lent parameter is returned as a copy", "fn same(a: &List<Int>) -> List<Int> { return clone(a); }; l = push([], 5); m = same(l); m = push(m, 6); return l;")
    , ("a lent parameter is passed on, and to an owner", "fn inner(a: &List<Int>) -> Int { return size(a); }; fn outer(a: &List<Int>) -> Int { return inner(a) + inner(a) + size(a); }; fn owner(a: List<Int>) -> Int { return size(a); }; fn mixed(a: &List<Int>) -> Int { return owner(clone(a)) + size(a); }; l = push([], 1); return outer(l) + mixed(l);")
    , ("a lent parameter and an owned one are the same list", "fn both(a: &List<Int>, b: List<Int>) -> Int { return size(a) + size(push(b, 1)); }; l = push([], 1); return both(l, clone(l));")
    , ("a list that is lent and given in one call is not shared", "fn both(a: &List<Int>, b: List<Int>) -> Int { b = push(b, 9); b = push(b, 8); b = push(b, 7); return size(a) * 10 + size(b); }; l = push([], 1); return both(l, clone(l));")
    , ("an empty list that is lent is of the type of the parameter", "fn count(a: &List<Bool>) -> Int { return size(a); }; return count([]) + count([true]);")
    , ("a constant that is lent next to another list", "fn two(a: &List<Bool>, b: List<Int>) -> Int { return size(a) * 10 + size(b); }; return two([true, false], push([], 1)) + two([], push(push([], 1), 2));")
    , ("a constant struct that is lent", "struct S { xs: List<Int> }; fn count(s: &S) -> Int { return size(s.xs); }; return count(S { xs: [1, 2, 3] });")
    , ("a lent list in a loop", "fn total(a: &List<Int>) -> Int { return size(a); }; l = push(push([], 1), 2); n = 0; s = 0; while n < 1000 [{ affirm n >= 0; }] shrinks 1000 - n { s = s + total(l); n = n + 1; }; return s;")
    , ("a lent array that the caller then changes", "fn lead(a: &Array<Int, 2>) -> Int { return get(a, 0); }; x = #[1, 2]; a = lead(x); x = set(x, 0, 9); return a * 10 + lead(x);")
    , ("a function with a size lends", "fn count<n>(a: &Array<Int, n>) -> Int { return n; }; return count(#[1, 2, 3]) + count(array(2, 0));")
    , ("an array of lists", "a = array(3, push([], 1)); a = set(a, 1, push(push([], 2), 3)); return a;")
    , ("an array of lists is made over another", "a = array(2, push([], 1)); a = array(2, push([], 2)); return a;")
    , ("an array of lists is made over another in a loop", "n = 0; a = array(3, push([], 1)); while n < 5 [{ affirm n >= 0; }] shrinks 5 - n { a = array(3, push(push([], n), n)); n = n + 1; }; return a;")
    , ("an array of structs that own lists is made over another", "struct P { xs: List<Int> }; impl Clone for P { }; a = array(2, P { xs: push([], 1) }); a = array(2, P { xs: push([], 2) }); return a;")
    , ("an array of lists is read", "a = array(2, push(push([], 5), 6)); return size(get(a, 0)) + get(get(a, 1), 1);")
    , ("an array of lists is copied", "a = array(2, push([], 5)); c = clone(a); c = set(c, 0, push([], 9)); return a;")
    , ("an element of an array of lists is changed and the array is not", "a = array(2, push([], 1)); l = clone(get(a, 0)); l = push(l, 7); return a;")
    , ("an array of structs that own lists", "struct P { xs: List<Int>, n: Int }; impl Clone for P { }; a = array(2, P { xs: push([], 1), n: 7 }); a = set(a, 0, P { xs: [], n: 9 }); return a;")
    , ("an array of Boxes", "a = array(2, Box::new(5)); return Box::unbox(get(a, 1));")
    , ("an array of arrays of lists", "a = array(2, array(2, push([], 5))); return a;")
    , ("arrays of lists are compared", "return array(2, push([], 1)) = array(2, push([], 1));")
    , ("an array of lists is given and returned", "fn grow(a: Array<List<Int>, 2>) -> Array<List<Int>, 2> { return set(a, 1, push(clone(get(a, 1)), 9)); }; return grow(grow(array(2, [])));")
    , ("an array of lists is lent", "fn total(a: &Array<List<Int>, 2>) -> Int { return size(get(a, 0)) + size(get(a, 1)); }; a = array(2, push([], 1)); return total(a) + total(a) + size(a);")
    , ("a struct that has an array of lists", "struct H { items: Array<List<Int>, 2>, n: Int }; h = H { items: array(2, push([], 3)), n: 1 }; g = H { n: 2, ..h }; return g;")
    , ("an enum that has an array of lists", "enum Shape { Pair { xs: Array<List<Int>, 2> }, None }; s = Shape::Pair { xs: array(2, push([], 4)) }; return match s { Shape::Pair { xs: xs } => size(get(xs, 1)), Shape::None => 0 };")
    , ("a list of arrays of lists", "l = push(push([], array(2, push([], 1))), array(2, [])); return clone(get(l, 0));")
    , ("a Box of an array of lists", "b = Box::new(array(2, push([], 1))); return b;")
    , ("Array::boxed of lists", "b = Array::boxed(3, push([], 1)); b = set(b, 2, push(push([], 4), 5)); return b;")
    , ("Array::boxed of lists is copied", "b = Array::boxed(2, push([], 1)); c = clone(b); c = set(c, 0, []); return b;")
    , ("Array::boxed of structs", "struct P { xs: List<Int> }; impl Clone for P { }; a = Array::boxed(2, P { xs: push([], 1) }); return clone(get(a, 1).xs);")
    , ("a size parameter and an array of lists", "fn count<n>(a: Array<List<Int>, n>) -> Int { return n; }; return count(array(3, [])) + count(array(2, push([], 1)));")
    , ("a type parameter", "fn lead<T>(a: &List<T>) -> T [{ define s = size(a); rewrite eqToGtZero s; affirm s > 0; }] [{ }] { return clone(get(a, 0)); }; return lead(push([], 7)) + 1;")
    , ("a type parameter, once for each type", "fn lead<T>(a: &List<T>) -> T [{ define s = size(a); rewrite eqToGtZero s; affirm s > 0; }] [{ }] { return clone(get(a, 0)); }; return lead(push([], 7)) + size(lead(push([], push([], 1)))) + size(lead(push([], push(push([], 2), 3))));")
    , ("a type parameter of a Bool and of a list", "fn id<T>(a: T) -> T { return a; }; l = id(push([], 3)); return id(l) = id(push([], 3)) ;")
    , ("a type parameter owned and lent", "fn twice<T>(a: &T) -> Array<T, 2> { return array(2, clone(a)); }; fn wrap<T>(a: T) -> Box<T> { return Box::new(a); }; return twice(wrap(push([], 5)));")
    , ("two type parameters", "fn pick<A, B>(a: A, b: B) -> B { return b; }; return pick(1, push([], 3));")
    , ("a function passes on its type", "fn count<T>(a: &List<T>) -> Int { return size(a); }; fn twice<T>(a: &List<T>) -> Int { return count(a) + count(a); }; return twice(push([], 1)) + twice(push([], true)) + twice([[1]]);")
    , ("a type parameter makes a list of structs", "struct P { xs: List<Int> }; fn mk<T>(x: T, n: Int) -> List<T> [{ define s = n; affirm s >= 0; }] [{ }] { out = []; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { out = push(out, clone(x)); i = i + 1; }; return out; }; return mk(P { xs: push([], 4) }, 3);")
    , ("a type and a size together", "fn fill<T, n>(a: &Array<T, n>, x: T) -> Array<T, n> [{ define k = n; rewrite eqToGtZero k; affirm k > 0; }] [{ }] { return set(clone(a), 0, x); }; l = fill(array(3, push([], 1)), push(push([], 7), 8)); b = fill(#[true, true], false); return l;")
    , ("a type parameter that is an empty list", "fn same<T>(a: T, b: T) -> Bool { return a = b; }; return same([], []);")
    , ("a function with a type calls itself", "fn f<T>(a: T, n: Int) -> Int [{ define k = n; affirm k >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return 1 + f(a, n - 1); }; return f(push([], 2), 3);")
    , ("a function with two types calls itself with them swapped", "fn f<A, B>(a: A, b: B, n: Int) -> Int [{ define k = n; affirm k >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return 1 + f(b, a, n - 1); }; return f(1, push([], 2), 3);")
    , ("a struct for a type", "struct Pair<T> { a: T, b: T }; p = Pair<Int> { a: 1, b: 2 }; return p.a + p.b;")
    , ("a struct with a small letter as a type", "struct point { x: Int }; struct Holder<T> { value: T }; fn x<U>(h: &Holder<U>) -> Int { return 1; }; h = Holder<point> { value: point { x: 1 } }; return h.value.x + x(h);")
    , ("a struct for a type that owns", "struct Pair<T> { a: T, b: T }; return Pair<List<Int>> { a: push([], 1), b: push(push([], 2), 3) };")
    , ("a function over structs of any type", "struct Pair<T> { a: T, b: T }; fn swap<U>(p: &Pair<U>) -> Pair<U> { return Pair<U> { a: clone(p.b), b: clone(p.a) }; }; q = swap(Pair<List<Int>> { a: push([], 1), b: push(push([], 2), 3) }); r = swap(Pair<Bool> { a: true, b: false }); return q;")
    , ("a struct of a struct, both with the type", "struct Pair<T> { a: T, b: T }; struct Wrap<T> { inner: Pair<T>, tag: Int }; fn mk<T>(x: T, y: T) -> Wrap<T> { return Wrap<T> { inner: Pair<T> { a: x, b: y }, tag: 7 }; }; return mk(push([], 1), push([], 2));")
    , ("a struct with a type is copied and updated", "struct Pair<T> { a: T, b: T }; a = Pair<List<Int>> { a: push([], 1), b: [] }; b = Pair<List<Int>> { b: push([], 9), ..clone(a) }; return a;")
    , ("a struct with a type in an array, a list and a Box", "struct Pair<T> { a: T, b: T }; impl<T> Clone for Pair<T> { }; l = push([], Pair<Int> { a: 1, b: 2 }); a = array(2, Pair<List<Int>> { a: push([], 4), b: [] }); b = Box::new(Pair<Int> { a: 5, b: 6 }); return a;")
    , ("a struct with a type and a size", "struct Vec<T, n> { cells: Array<T, n>, used: Int }; fn capacity<T, m>(v: &Vec<T, m>) -> Int { return m + v.used; }; return capacity(Vec<Int, 3> { cells: #[1, 2, 3], used: 1 }) * 10 + capacity(Vec<Bool, 2> { cells: #[true, false], used: 0 });")
    , ("a struct with a Box of an array of its type", "struct Holder<T> { items: Box<Array<T>>, len: Int }; fn holder<T>(x: T, n: Int) -> Holder<T> [{ define s = n; rewrite eqToGtZero s; affirm s > 0; }] [{ affirm size(return.items) = n; }] { return Holder<T> { items: Array::boxed(n, x), len: n }; }; fn at<T>(h: &Holder<T>, i: Int) -> T [{ define s = size(h.items); affirm i >= 0; affirm i < s; }] [{ }] { return clone(get(h.items, i)); }; h = holder(push([], 5), 3); g = holder(true, 2); return at(h, 2);")
    , ("a struct with a type holds itself in a Box", "struct Node<T> { value: T, next: List<Node<T>> }; n = Node<List<Int>> { value: push([], 1), next: push([], Node<List<Int>> { value: [], next: [] }) }; return n;")
    , ("a type that nothing decides", "fn nil<T>() -> List<T> { return []; }; return size(nil());")
    , ("a size parameter", "fn dot<n>(a: Array<Int, n>, b: Array<Int, n>) -> Int { total = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { total = total + get(a, i) * get(b, i); i = i + 1; }; return total; }; return dot(#[1, 2, 3], #[4, 5, 6]) + dot(#[2], #[5]);")
    , ("a size parameter, once for each size", "fn count<n>(a: Array<Int, n>) -> Int { return n; }; return count(#[1, 2, 3]) * 100 + count(array(4, 0)) * 10 + count(#[]);")
    , ("a size parameter makes an array", "fn ones<n>(a: Array<Int, n>) -> Array<Int, n> { return array(n, 1); }; return ones(#[7, 8, 9]);")
    , ("an array of the size of a parameter is set", "fn ones<n>(a: Array<Int, n>) -> Array<Int, n> [{ define k = n; rewrite eqToGtZero k; affirm k > 0; }] [{ }] { b = array(n, 1); b = set(b, 0, 5); return b; }; return ones(#[7, 8, 9]);")
    , ("two size parameters", "fn grid<n, m>(a: Array<Array<Int, n>, m>) -> Int { return n * 10 + m; }; return grid(array(3, array(2, 0)));")
    , ("a function passes on its size", "fn count<n>(a: Array<Int, n>) -> Int { return n; }; fn outer<m>(a: Array<Int, m>) -> Int { return count(a) + count(#[1, 2]); }; return outer(#[1]) + outer(#[1, 2, 3]);")
    , ("a function with a size calls itself", "fn count<n>(a: Array<Int, n>, k: Int) -> Int [{ define z = k; affirm z >= 0; }] [{ }] shrinks k { if k = 0 { return n; }; return count(a, k - 1); }; return count(#[1, 2, 3], 4);")
    , ("a size parameter with a Box", "fn f<n>(a: Array<Int, n>, b: Box<Array<Int, n>>) -> Int { return size(b) + n; }; return f(#[1, 2], Box::new(#[3, 4]));")
    , ("a size parameter and the unsizing conversion", "fn mk<n>(a: Array<Int, n>) -> Box<Array<Int>> { return Box::new(a); }; x = mk(#[1, 2, 3]); return size(x) * 2;")
    , ("a function with a size whose name is assigned elsewhere", "fn count<n>(a: Array<Int, n>) -> Int { return n; }; fn other() -> Int { count = 1; return count; }; return count(#[1]) + other();")
    , ("a struct with a size", "struct P<n> { id: Int, body: Array<Int, n> }; p = P<3> { id: 7, body: #[1, 2, 3] }; return p.id + size(p.body) + get(p.body, 2);")
    , ("a size that no field uses is the size of an Int", "struct Tag<n> { x: Int }; fn width<m>(p: Tag<m>) -> Int { return m; }; return width(Tag<9223372036854775807> { x: 0 });")
    , ("a struct with a size is printed", "struct P<n> { id: Int, body: Array<Int, n> }; return P<2> { id: 1, body: #[5, 6] };")
    , ("a function over structs of every size", "struct P<n> { id: Int, body: Array<Int, n> }; fn total<m>(p: P<m>) -> Int { s = p.id; i = 0; while i < m [{ affirm i >= 0; affirm i <= m; }] shrinks m - i { s = s + get(p.body, i); i = i + 1; }; return s; }; return total(P<3> { id: 7, body: #[1, 2, 3] }) + total(P<1> { id: 1, body: #[10] });")
    , ("a struct made in a function that has the size", "struct P<n> { id: Int, body: Array<Int, n> }; fn blank<m>(a: Array<Int, m>) -> P<m> { return P<m> { id: m, body: array(m, 0) }; }; return blank(#[1, 2]);")
    , ("a struct of a struct, both with the size", "struct I<n> { cells: Array<Int, n> }; struct O<n> { tag: Int, inner: I<n> }; fn w<m>(o: O<m>) -> Int { return m * 10 + o.tag; }; return w(O<2> { tag: 4, inner: I<2> { cells: #[1, 2] } });")
    , ("a struct with a size is updated", "struct P<n> { id: Int, body: Array<Int, n> }; a = P<2> { id: 1, body: #[5, 6] }; b = P<2> { id: 9, ..a }; return b;")
    , ("a struct with a size in a Box and a list", "struct P<n> { id: Int, body: Array<Int, n> }; b = Box::new(P<2> { id: 1, body: #[5, 6] }); l = push([], P<2> { id: 2, body: #[7, 8] }); return b.id + size(b.body) + get(l, 0).id;")
    , ("structs with sizes are compared", "struct P<n> { id: Int, body: Array<Int, n> }; return P<2> { id: 1, body: #[1, 2] } = P<2> { id: 1, body: #[1, 2] };")
    , ("a size parameter and a struct", "struct S { a: Array<Int, 2> }; fn count<n>(a: Array<Int, n>) -> Int { return n; }; s = S { a: #[1, 2] }; return count(s.a);")
    , ("a Box of an Int", "b = Box::new(5); return Box::unbox(b) + 1;")
    , ("a Box of a Bool", "return Box::unbox(Box::new(true));")
    , ("a Box of a list", "b = Box::new(push([], 4)); l = Box::unbox(b); return size(l);")
    , ("a Box of a Box", "b = Box::new(Box::new(3)); c = Box::unbox(b); return Box::unbox(c);")
    , ("a Box of an array", "b = Box::new(#[1, 2, 3]); return b;")
    , ("a Box of an array is read", "a = Box::new(#[1, 2, 3]); return last(a) + first(a) + get(a, 1) + size(a);")
    , ("a Box of an array is set", "b = Box::new(#[1, 2, 3]); b = set(b, 0, 9); return b;")
    , ("a Box of an array is copied", "b = Box::new(#[1, 2, 3]); c = clone(b); b = set(b, 0, 9); return get(b, 0) * 10 + get(c, 0);")
    , ("a Box of an array of arrays", "b = Box::new(array(2, #[1, 2])); return get(get(Box::unbox(b), 1), 0);")
    , ("Array::boxed", "a = Array::boxed(3, 1); return a;")
    , ("Array::boxed of no elements", "a = Array::boxed(0, 5); return size(a);")
    , ("Array::boxed with a size the program computes", "n = 2 + 1; a = Array::boxed(n, 4); return a;")
    , ("Array::boxed of arrays", "a = Array::boxed(3, #[1, 2]); a = set(a, 1, #[7, 8]); return get(get(a, 1), 0) + size(a);")
    , ("Array::boxed of Bools", "a = Array::boxed(2, true); a = set(a, 0, false); return a;")
    , ("Array::boxed of zeros", "n = 4; return Array::boxed(n, 0);")
    , ("Array::boxed is set in place", "b = Array::boxed(5, 3); b = set(b, 2, 40); return get(b, 2) + get(b, 4) + size(b);")
    , ("a Box with its size is a copy", "a = Array::boxed(3, 1); b = clone(a); a = set(a, 0, 5); return get(a, 0) + get(b, 0);")
    , ("last of a Box with its size", "a = Array::boxed(4, 1); a = set(a, 3, 8); return last(a);")
    , ("equal Boxes with their size", "a = Array::boxed(2, 2); b = Array::boxed(2, 2); return a = b;")
    , ("unequal Boxes with their size", "a = Array::boxed(2, 2); b = Array::boxed(3, 2); return a != b;")
    , ("equal Boxes of a size and of any size", "fn same(a: Box<Array<Int>>, b: Box<Array<Int>>) -> Bool { return a = b; }; return same(Box::new(#[2, 2]), Array::boxed(2, 2));")
    , ("a Box of a size is given as one of any size", "fn total(a: Box<Array<Int>>) -> Int { return size(a) * 2; }; t = Box::new(#[1, 2, 3]); return total(clone(t)) + size(t);")
    , ("it is given more than once", "fn n(a: Box<Array<Int>>) -> Int { return size(a); }; return n(Box::new(#[1])) * 100 + n(Box::new(#[1, 2])) * 10 + n(Array::boxed(3, 0));")
    , ("it is returned", "fn wide() -> Box<Array<Int>> { return Box::new(#[5, 6]); }; a = wide(); return a;")
    , ("it is returned from a function that is given one", "fn id(a: Box<Array<Int>>) -> Box<Array<Int>> { return a; }; return id(Box::new(#[5, 6]));")
    , ("it is assigned over one", "a = Array::boxed(2, 0); a = Box::new(#[1, 2, 3]); return size(a);")
    , ("in a loop", "fn sum(a: Box<Array<Int>>) -> Int [{ define s = size(a); affirm s >= 0; }] [{ }] { t = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { t = t + get(a, i); i = i + 1; }; return t; }; return sum(Box::new(#[1, 2, 3, 4])) + sum(Array::boxed(5, 2));")
    , ("in a struct", "struct S { a: Box<Array<Int>>, n: Int }; s = S { a: Array::boxed(3, 9), n: 1 }; return s;")
    , ("in a struct, from a Box of a size", "struct S { a: Box<Array<Int>>, n: Int }; s = S { a: Box::new(#[1, 2, 3]), n: 1 }; return size(s.a) + s.n;")
    , ("in an enum", "enum E { A { a: Box<Array<Int>> }, B }; e = E::A { a: Array::boxed(3, 4) }; return match e { E::A { a: a } => size(a), E::B => 0 };")
    , ("in a list", "l = push(push([], Array::boxed(2, 5)), Array::boxed(3, 6)); return size(get(l, 1)) + size(l);")
    , ("a list of them is copied", "l = push([], Array::boxed(2, 5)); m = clone(l); l = push(l, Array::boxed(1, 1)); return m;")
    , ("a struct with one is copied", "struct S { a: Box<Array<Int>> }; impl Clone for S { }; s = S { a: Array::boxed(2, 5) }; t = clone(s); return t.a = s.a;")
    , ("a result that is one is printed", "struct S { a: Box<Array<Int>>, n: Int }; return S { a: Array::boxed(2, 5), n: 3 };")
    , ("a Box of a struct that has one", "struct S { a: Box<Array<Int>> }; b = Box::new(S { a: Array::boxed(2, 5) }); return size(b.a);")
    ]

-- `impl<T> Pair<T> { ... }`: a function of the impl is made for each list of types and sizes it is called with
genericImplPrograms :: [(String, String)]
genericImplPrograms =
    [ ("a function of an impl with its own parameters", "struct S { x: Int }; impl S { fn f<n>(a: Array<Int, n>) -> Int { return n; }; fn id<T>(a: T) -> T { return a; }; }; return S::f(#[1, 2, 3]) * 10 + S::id(4);")
    , ("a method of a struct with a type", "struct Box2<T> { a: T, b: T }; impl<T> Box2<T> { fn first(self: &Self) -> T { return clone(self.a); }; fn swap(self: Self) -> Self { return Self { a: self.b, b: self.a }; }; }; x = Box2<Int> { a: 1, b: 2 }.swap(); return x.first() * 10 + x.b;")
    , ("for lists that own things", "struct Box2<T> { a: T, b: T }; impl<T> Clone for Box2<T> { }; impl<T> Box2<T> { fn first(self: &Self) -> T { return clone(self.a); }; fn swap(self: Self) -> Self { return Self { a: self.b, b: self.a }; }; }; x = Box2<List<Int>> { a: push([], 1), b: push(push([], 2), 3) }; y = x.clone().swap(); return size(x.first()) * 10 + size(y.first());")
    , ("for two types at once", "struct Box2<T> { a: T, b: T }; impl<T> Box2<T> { fn first(self: &Self) -> T { return clone(self.a); }; }; l = Box2<List<Int>> { a: push([], 1), b: [] }; i = Box2<Int> { a: 4, b: 5 }; return size(l.first()) + i.first();")
    , ("a size of the impl", "struct Packet<n> { cells: Array<Int, n>, tag: Int }; impl<n> Packet<n> { fn count(self: &Self) -> Int { return n + self.tag; }; fn bump(self: Self) -> Self { return Self { tag: self.tag + 1, ..self }; }; fn twice(self: Self) -> Int { return self.bump().bump().count(); }; }; return Packet<3> { cells: #[1, 2, 3], tag: 10 }.twice() + Packet<2> { cells: #[1, 2], tag: 0 }.count();")
    , ("a type and a size", "struct Row<T, n> { cells: Array<T, n> }; impl<T, n> Row<T, n> { fn width(self: &Self) -> Int { return n; }; fn head(self: &Self) -> T [{ affirm n > 0; }] [{ }] { return clone(get(self.cells, 0)); }; }; r = Row<Int, 3> { cells: #[7, 8, 9] }; return r.head() + r.width() * 10;")
    , ("a function without self, through Self", "struct Pair<A, B> { a: A, b: B }; impl<X, Y> Pair<X, Y> { fn make(x: X, y: Y) -> Self { return Self { a: x, b: y }; }; fn again(self: &Self) -> Self { return Self::make(clone(self.a), clone(self.b)); }; fn flip(self: &Self) -> Pair<Y, X> { return Pair<Y, X> { a: clone(self.b), b: clone(self.a) }; }; }; q = Pair::make(push([], 4), true).again().flip(); return size(q.b) + 10;")
    ]

-- Programs over the library list of examples/vec.tersus (`vecLibrary`, written out in the program). Run with the checks of the runtime on, they show that
-- the arrays it grows, the elements it moves and the Vecs it holds are each freed once.
vecPrograms :: [(String, String)]
vecPrograms =
    [ ("pushed and read", "v = Vec::new(0).push(5).push(6); return v.get(0) * 10 + v.get(1);")
    , ("pushed past its capacity", loop 10 "0" "v = v.push(i * i);" ++ "return size(v) + v.get(9);")
    , ("pushed past it again and again", loop 300 "0" "v = v.push(i);" ++ "return size(v) + v.get(299);")
    , ("set and popped", "v = Vec::new(false).push(true).push(false).set(0, true).pop(); return size(v);")
    , ("a copy is a Vec of its own", "a = Vec::new(0).push(1); b = a.clone().set(0, 7); return a.get(0) * 10 + b.get(0);")
    , ("of lists", loop 9 "push([], 0)" "v = v.push(push(push([], i), i));" ++ "return size(v.get(8)) + size(v);")
    , ("of lists, one taken out", "rows = Vec::new(push([], 0)).push(push(push([], 4), 5)); r = rows.get(0); return size(r) + size(rows.data);")
    , ("of Vecs", "g = Vec::new(Vec::new(0)).push(Vec::new(0).push(8).push(9)); return size(g.get(0));")
    , ("of Vecs that grow", "g = Vec::new(Vec::new(0)); i = 0; while i < 9 [{ affirm i >= 0; affirm i <= 9; affirm size(g) = i; }] shrinks 9 - i { g = g.push(Vec::new(i).push(i)); i = i + 1; }; return size(g) + size(g.get(8));")
    , ("of structs that own a list", "struct P { n: Int, xs: List<Int> }; ps = Vec::new(P { n: 0, xs: [] }).push(P { n: 3, xs: push([], 1) }); p = ps.get(0); return p.n + size(p.xs);")
    , ("in a struct", "struct Bag { items: Vec<Int>, tag: Int }; b = Bag { items: Vec::new(0).push(4), tag: 2 }; return b.tag + size(b.items);")
    , ("in a list", "l = push(push([], Vec::new(0).push(1)), Vec::new(5)); return size(l);")
    , ("one function for a Vec, a List and an Array", total ++ "return total(Vec::new(0).push(10).push(20).push(30)) * 10000 + total(push(push([], 3), 4)) * 100 + total(array(3, 5));")
    , ("for sequences of lists", "fn lens<S: Sequence<List<Int>>>(s: &S) -> Int [{ }] [{ }] { n = 0; i = 0; while i < size(s) [{ affirm i >= 0; affirm i <= size(s); }] shrinks size(s) - i { n = n + size(get(s, i)); i = i + 1; }; return n; }; v = Vec::new(push([], 0)).push(push(push([], 4), 5)); l = push(push([], push([], 1)), push(push([], 2), 3)); return lens(v) * 10 + lens(l);")
    , ("for a sequence that grows", "fn add<S: Growable<Int>>(s: S, x: Int) -> S [{ }] [{ affirm size(return) = size(s) + 1; }] { return push(s, x); }; v = add(add(Vec::new(0), 4), 5); l = add(add([], 6), 7); return size(v) * 10 + size(l) + v.get(1) + get(l, 1);")
    , ("made and dropped in a loop", "t = 0; i = 0; while i < 1000 [{ affirm i >= 0; }] shrinks 1000 - i { v = Vec::new(push([], i)).push(push([], i)).push(push([], 7)); t = t + size(v); i = i + 1; }; return t;")
    ]
  where
    total = "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { sum = 0; i = 0; while i < size(s) [{ affirm i >= 0; affirm i <= size(s); }] shrinks size(s) - i { sum = sum + get(s, i); i = i + 1; }; return sum; }; "
    -- A Vec made with the filler and pushed to by the statement `n` times
    loop n filler step =
        "v = Vec::new(" ++ filler ++ "); i = 0; while i < " ++ show (n :: Int) ++ " [{ affirm i >= 0; affirm i <= " ++ show n ++ "; affirm size(v) = i; }] shrinks " ++ show n ++ " - i { " ++ step ++ " i = i + 1; }; "

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
    , ("and", "a = 3; b = 5; return a < b && b < 9;")
    , ("or and not", "a = 3; return !(a > 5) || a = 3 && false;")
    , ("a connective does not evaluate what it does not need", "a = 0; return a != 0 && 10 / a > 1;")
    , ("a loop with two tests", "i = 0; s = 0; while i < 10 && s < 20 shrinks 10 - i { s = s + i * 2; i = i + 1; }; return s;")
    , ("a loop with an or", "i = 0; while i < 3 || i < 5 [{ affirm i >= 0; affirm i <= 5; }] shrinks 5 - i { i = i + 1; }; return i;")
    , ("a connective in a returned value", "a = 2; b = 7; return !(a > b) && (a < 3 || b < 3);")
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

-- `tersus run` compiles and runs the program: the exit status of the program comes back, and what it prints goes to the output of this process
testRunExecutable :: Test
testRunExecutable = TestCase "run builds, runs and removes the executable" $ do
    available <- clangAvailable
    if not available
        then pure Nothing
        else do
            ran <- case llvmSource "return 6 * 7;" of
                Error e -> pure (Error e)
                Ok ir -> runExecutable ir []
            failing <- case llvmSource "return 9223372036854775807 + 1;" of
                Error e -> pure (Error e)
                Ok ir -> runExecutable ir []
            pure (testAssertEq (ran, failing) (Ok ExitSuccess, Ok (ExitFailure 1)))

-- Every example that validates is run natively: a new example has to be added to `nativeExamples`
testEveryExampleIsBuilt :: Test
testEveryExampleIsBuilt = TestCase "every example is in nativeExamples" $ do
    files <- listDirectory "examples"
    let examples = [f | f <- files, reverse (take 8 (reverse f)) == ".tersus"]
        missing = [f | f <- examples, "examples/" ++ f `notElem` nativeExamples]
    pure (testAssertEq missing [])

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
sameAsMir name = sameAsMirWithInput name ""

-- The same for a program that reads: both are given the input (bytes as characters from 0 to 255)
sameAsMirWithInput :: String -> String -> String -> IO TestResult
sameAsMirWithInput name input = sameAsMirWorld name noWorld{worldInput = input}

-- The same for a program that has arguments too (each as its bytes)
sameAsMirWorld :: String -> World -> String -> IO TestResult
sameAsMirWorld name world source = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else case compileSource source of
            Error e -> pure (Just ("Does not compile: " ++ e))
            Ok _ -> case llvmSource source of
                Error e -> pure (Just e)
                Ok ir -> do
                    buildAndRun (worldInput world) (worldArgs world) (map safeChar name) name ir (expected (runSourceIn world Interpret source))
  where
    expected (Ok (output, errors)) = (ExitSuccess, if null output then "" else output ++ "\n", errors)
    expected (Error e) = (ExitFailure 1, "", e ++ "\n")

-- A list built by pushing, and changed by setting, is built in place: it needs memory in proportion to its length and not to its
-- length squared (a million pushes copied each time would need terabytes), and a limit on the memory of the program shows it
memoryTests :: [Test]
memoryTests =
    [ TestCase "a million pushes" (underLimit "l = []; i = 0; while i < 1000000 [{ affirm i >= 0; }] shrinks 1000000 - i { l = push(l, i); i = i + 1; }; return size(l);" "1000000\n")
    , TestCase "pushes and sets" (underLimit "l = []; i = 0; while i < 300000 [{ affirm i >= 0; }] shrinks 300000 - i { l = push(l, i); i = i + 1; }; k = 0; while k < 300000 [{ affirm k >= 0; }] shrinks 300000 - k { l = set(l, k, get(l, k) + 1); k = k + 1; }; return get(l, 299999);" "300000\n")
    , TestCase "the largest array set in place, again and again" (underLimit "a = array(8192, 0); i = 0; while i < 2000000 [{ affirm i >= 0; }] shrinks 2000000 - i { a = set(a, 8191, i); i = i + 1; }; return get(a, 8191);" "1999999\n")
    , TestCase "arrays made, given and returned in a loop do not grow the frame" (underLimit "fn bump(a: Array<Int, 4>) -> Array<Int, 4> { return set(a, 0, get(a, 0) + 1); }; s = 0; i = 0; while i < 1000000 [{ affirm i >= 0; }] shrinks 1000000 - i { a = bump(set(array(4, 0), 1, i)); s = s + get(a, 0) + get(#[1, 2], 1); i = i + 1; }; return s;" "3000000\n")
    , TestCase "a list of structs that own lists" (underLimit "struct S { n: Int, xs: List<Int> }; l = []; i = 0; while i < 50000 [{ affirm i >= 0; }] shrinks 50000 - i { l = push(l, S { n: i, xs: push([], i) }); i = i + 1; }; return size(l);" "50000\n")
    , TestCase "a struct with a list is made and dropped in a loop" (underLimit "struct S { n: Int, xs: List<Int> }; fn mk(i: Int) -> S { return S { n: i, xs: push([], i) }; }; t = 0; i = 0; while i < 1000000 [{ affirm i >= 0; }] shrinks 1000000 - i { s = mk(i); t = t + size(s.xs); i = i + 1; }; return t;" "1000000\n")
    , TestCase "boxed arrays made, set and dropped in a loop" (underLimit "n = 0; total = 0; while n < 200000 [{ affirm n >= 0; }] shrinks 200000 - n { a = Array::boxed(n % 7 + 1, n); a = set(a, 0, 1); total = total + size(a) + get(a, 0); n = n + 1; }; return total;" "999994\n")
    , TestCase "boxes of arrays made and dropped in a loop" (underLimit "n = 0; total = 0; while n < 1000000 [{ affirm n >= 0; }] shrinks 1000000 - n { a = Box::new(array(2, n)); total = total + get(a, 0); n = n + 1; }; return total;" "499999500000\n")
    , TestCase "arrays of lists made, changed and dropped in a loop" (underLimit "n = 0; total = 0; while n < 200000 [{ affirm n >= 0; }] shrinks 200000 - n { a = array(3, push(push([], n), n)); a = set(a, 1, push([], n)); total = total + size(get(a, 0)) + size(get(a, 1)); n = n + 1; }; return total;" "600000\n")
    , TestCase "an array of lists made over another in a loop" (underLimit "n = 0; total = 0; a = array(3, push([], 1)); while n < 2000000 [{ affirm n >= 0; }] shrinks 2000000 - n { a = array(3, push(push([], n), n)); total = total + size(get(a, 2)); n = n + 1; }; return total;" "4000000\n")
    , TestCase "boxed arrays of lists made, changed and dropped in a loop" (underLimit "n = 0; total = 0; while n < 100000 [{ affirm n >= 0; }] shrinks 100000 - n { a = Array::boxed(n % 5 + 1, push([], n)); a = set(a, 0, []); total = total + size(a) + size(get(a, 0)); n = n + 1; }; return total;" "300000\n")
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
buildAndRun :: String -> [String] -> String -> String -> String -> (ExitCode, String, String) -> IO TestResult
buildAndRun input args file name ir expectation = do
    tmp <- getTemporaryDirectory
    let dir = tmp </> "tersus-native-test"
        exe = dir </> file
    createDirectoryIfMissing True dir
    checked <- buildExecutableWith checkedBuild exe ir
    case checked of
        Error e -> pure (Just e)
        Ok () -> do
            plain <- runExecutableBytes exe args input
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
                                    result <- runExecutableBytes "valgrind" ["-q", "--error-exitcode=99", "--leak-check=full", "--errors-for-leak-kinds=definite,possible", exe ++ "_plain"] input
                                    pure (fmap ("under valgrind:\n" ++) (testAssertEq result expectation))

-- The one thing the MIR run does not know: a file that cannot be written (it keeps the file to itself and the command line writes it when the program has
-- ended). Natively the write says -1.
testUnwritableFile :: Test
testUnwritableFile = TestCase "a file that cannot be written (natively)" $ do
    available <- clangAvailable
    let source = "r = \"x\".writeFile(\"no/such/dir/x.txt\"); return 0 - r;"
    if not available
        then pure Nothing
        else case llvmSource source of
            Error e -> pure (Just e)
            Ok ir -> buildAndRun "" [] "unwritable_file" "a file that cannot be written" ir (ExitSuccess, "1\n", "")

-- A program that reads and writes files, run natively in a directory of its own that holds the files given (each path with the bytes of its contents) and on
-- the MIR with the same files: the output and the standard error have to be the same, and so does each file that the MIR run wrote
sameAsMirFiles :: String -> [(FilePath, String)] -> String -> IO TestResult
sameAsMirFiles name initial source = do
    available <- clangAvailable
    if not available
        then pure Nothing
        else case compileSource source of
            Error e -> pure (Just ("Does not compile: " ++ e))
            Ok _ -> case llvmSource source of
                Error e -> pure (Just e)
                Ok ir -> case runSourceFiles noWorld{worldFile = \path -> lookup path initial} Interpret source of
                    Error e -> pure (Just ("The MIR run failed: " ++ e))
                    Ok ((out, err), files) -> withByteNames $ do
                        tmp <- getTemporaryDirectory
                        let dir = tmp </> "tersus-native-files" </> map safeChar name
                            exe = tmp </> "tersus-native-files" </> (map safeChar name ++ "_exe")
                        exists <- doesDirectoryExist dir
                        if exists then removeDirectoryRecursive dir else pure ()
                        createDirectoryIfMissing True dir
                        mapM_ (\(path, contents) -> withBinaryFile (dir </> path) WriteMode (\h -> hPutStr h contents)) initial
                        built <- buildExecutable exe ir
                        case built of
                            Error e -> pure (Just e)
                            Ok () -> do
                                saved <- getLocaleEncoding
                                setLocaleEncoding char8
                                (code, nativeOut, nativeErr) <- readCreateProcessWithExitCode (proc exe []){cwd = Just dir} "" `finally` setLocaleEncoding saved
                                let expectedOut = if null out then "" else out ++ "\n"
                                    sameStreams = testAssertEq (code, decodeUtf8 nativeOut, decodeUtf8 nativeErr) (ExitSuccess, expectedOut, err)
                                written <- mapM (\(path, contents) -> readBytes (dir </> path) >>= \actual -> pure (path, actual, contents)) files
                                let sameFiles = case [path ++ ": expected " ++ show contents ++ ", got " ++ show actual | (path, actual, contents) <- written, actual /= contents] of
                                        [] -> Nothing
                                        problems -> Just (unlines problems)
                                pure (maybe sameFiles Just sameStreams)
  where
    -- (the names of files are bytes here too)
    withByteNames action = do
        savedFs <- getFileSystemEncoding
        setFileSystemEncoding char8
        action `finally` setFileSystemEncoding savedFs
    readBytes path = do
        saved <- getLocaleEncoding
        setLocaleEncoding char8
        (do contents <- withBinaryFile path ReadMode (\h -> hGetContents h >>= \c -> length c `seq` pure c)
            pure contents) `finally` setLocaleEncoding saved

-- Runs a program and gives what it wrote as the text it is the UTF-8 of, whatever the locale is: the bytes are read as they are (a locale that is
-- not UTF-8 refuses some of them) and decoded
runExecutableBytes :: FilePath -> [String] -> String -> IO (ExitCode, String, String)
runExecutableBytes exe args input = do
    saved <- getLocaleEncoding
    savedFs <- getFileSystemEncoding
    setLocaleEncoding char8
    -- (the arguments are bytes too)
    setFileSystemEncoding char8
    (code, out, err) <- readProcessWithExitCode exe args input `finally` (setLocaleEncoding saved >> setFileSystemEncoding savedFs)
    pure (code, decodeUtf8 out, decodeUtf8 err)

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
            Right program -> case emitProgram (nativeProgram program) of
                Error e -> pure (Just e)
                Ok ir -> do
                    buildAndRun "" [] ("unvalidated_" ++ map safeChar name) name ir (expected (runProgram program))
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
