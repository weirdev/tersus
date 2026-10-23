module TestNative
    ( testNative
    ) where

import Control.Exception (IOException, try)
import Data.List (isInfixOf)
import System.Directory (createDirectoryIfMissing, getTemporaryDirectory)
import System.Exit (ExitCode (..))
import System.FilePath ((</>))
import System.Process (readProcessWithExitCode)

import Cli
import Native (buildExecutable)
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
        , TestList "control flow" [TestCase name (sameAsMir name source) | (name, source) <- controlPrograms]
        , TestList "stops" [TestCase name (sameAsMir name source) | (name, source) <- stopPrograms]
        ]

-- The examples whose every type native code supports so far
nativeExamples :: [FilePath]
nativeExamples =
    [ "examples/arithmetic.tersus"
    , "examples/booleans.tersus"
    , "examples/helper_functions.tersus"
    , "examples/linear.tersus"
    , "examples/loop_return.tersus"
    , "examples/loops.tersus"
    , "examples/proofs.tersus"
    , "examples/rules.tersus"
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
            withIr "x = 3; return x < 4;" (\ir -> testAssertTrue ("icmp slt i64" `isInfixOf` ir && "call void @tersus_print_bool" `isInfixOf` ir))
        , TestCase "function" . pure $
            withIr "fn f(a: Int) -> Int { return a; }; return f(1);" (\ir -> testAssertTrue ("define internal i64 @\"fn.f\"(i64 %p1)" `isInfixOf` ir && "call i64 @\"fn.f\"" `isInfixOf` ir))
        , TestCase "no return" . pure $
            withIr "x = 1;" (\ir -> testAssertTrue ("define internal void @tersus_main()" `isInfixOf` ir))
        , TestCase "ghost statements are dropped" . pure $
            withIr "x = 1; affirm x = 1; return x;" (\ir -> testAssertTrue (not ("affirm" `isInfixOf` ir)))
        , TestCase "lists are not supported yet" . pure $
            testAssertErrorContains "Native code does not support List<Int> yet" (llvmSource "return [1];")
        , TestCase "a program that does not validate is not lowered" . pure $
            testAssertErrorContains "Validation failed" (llvmSource "x = 5; affirm x < 4;")
        , TestCase "command line" . pure $
            testAssertEq
                (map parseCommandLine [["llvm", "a.tersus"], ["build", "a.tersus", "-o", "a"], ["build", "a.tersus"]])
                [Just (Llvm, "a.tersus"), Just (Build "a", "a.tersus"), Nothing]
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

controlPrograms :: [(String, String)]
controlPrograms =
    [ ("comparisons", "a = 3; b = 5; return a < b;")
    , ("equality of booleans", "a = 3 < 5; b = 4 < 2; return a = b;")
    , ("inequality", "a = 3; return a != 3;")
    , ("branch", "a = 3; if a > 2 { a = a * 10; } else { a = 0; }; return a;")
    , ("while loop", "i = 0; s = 0; while i < 10 shrinks 10 - i { s = s + i; i = i + 1; }; return s;")
    , ("no return", "x = 1 + 2;")
    , ("recursion", "fn fact(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n = 0 { return 1; }; return n * fact(n - 1); }; return fact(10);")
    , ("boolean result", "fn even(n: Int) -> Bool { return n % 2 = 0; }; return even(10);")
    , ("boolean parameter", "fn pick(c: Bool, a: Int, b: Int) -> Int { if c { return a; }; return b; }; return pick(1 < 2, 10, 20);")
    ]

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
                    tmp <- getTemporaryDirectory
                    let dir = tmp </> "tersus-native-test"
                        exe = dir </> map safe name
                    createDirectoryIfMissing True dir
                    built <- buildExecutable exe ir
                    case built of
                        Error e -> pure (Just e)
                        Ok () -> do
                            (code, out, err) <- readProcessWithExitCode exe [] ""
                            pure (testAssertEq (code, out, err) (expected (runSource Run source)))
  where
    safe c = if c `elem` ['a' .. 'z'] ++ ['A' .. 'Z'] ++ ['0' .. '9'] then c else '_'
    expected (Ok output) = (ExitSuccess, if null output then "" else output ++ "\n", "")
    expected (Error e) = (ExitFailure 1, "", e ++ "\n")

clangAvailable :: IO Bool
clangAvailable = do
    outcome <- try (readProcessWithExitCode "clang" ["--version"] "")
    pure $ case outcome of
        Left e -> const False (e :: IOException)
        Right (code, _, _) -> code == ExitSuccess
