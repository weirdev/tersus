module TestHarness
    ( TestResult
    , Test (..)
    , TestSummary (..)
    , testSummary
    , combineSummaries
    , testCase
    , testCaseSeq
    , forceTestResult
    , runTest
    , testAssertTrue
    , testAssertEq
    , testAssertErrorContains
    , parseValFailStmtHelper
    , parseEvalProgramHelper
    , parseEvalProgramFailHelper
    , parseValidProgramHelper
    , parseValidateFailProgramHelper
    , nativeInts
    , vecLibrary
    ) where

import qualified Control.Exception as Exception
import Control.Exception (SomeException, displayException, try)
import MirEval (fromMirValue)
import Parse
import Pipeline (runStatements, validateStatements)
import TersusTypes
import Utils

type TestResult = Maybe String

data Test = TestCase String (IO TestResult) | TestList String [Test]

data TestSummary = TestSummary
    { summaryPassed :: Int
    , summaryFailed :: Int
    }

testSummary :: Int -> Int -> TestSummary
testSummary = TestSummary

combineSummaries :: TestSummary -> TestSummary -> TestSummary
combineSummaries
    (TestSummary passedA failedA)
    (TestSummary passedB failedB) =
        TestSummary (passedA + passedB) (failedA + failedB)

testCase :: String -> TestResult -> Test
testCase name result = TestCase name (pure result)

testCaseSeq :: String -> [TestResult] -> Test
testCaseSeq name results =
    TestList
        name
        (zipWith (\i result -> testCase (show i) result) [0 :: Integer ..] results)

forceTestResult :: TestResult -> ()
forceTestResult Nothing = ()
forceTestResult (Just message) = forceString message
  where
    forceString [] = ()
    forceString (c : cs) = c `seq` forceString cs

runTest :: [String] -> Test -> IO TestSummary
runTest prefixes (TestCase name resultIO) = do
    let fullName = unwords (prefixes ++ [name])
    resultOrCrash <- try (resultIO >>= \result -> Exception.evaluate (forceTestResult result) >> pure result) :: IO (Either SomeException TestResult)
    case resultOrCrash of
        Right Nothing -> do
            putStrLn $ "[PASS] " ++ fullName
            pure (testSummary 1 0)
        Right (Just err) -> do
            putStrLn $ "[FAIL] " ++ fullName
            putStrLn err
            pure (testSummary 0 1)
        Left ex -> do
            putStrLn $ "[CRASH] " ++ fullName
            putStrLn (displayException ex)
            pure (testSummary 0 1)
runTest prefixes (TestList name tests) = do
    putStrLn $ "Running " ++ unwords (prefixes ++ [name])
    summaries <- mapM (runTest (prefixes ++ [name])) tests
    putStrLn ""
    pure (foldr combineSummaries (testSummary 0 0) summaries)

testAssertTrue :: Bool -> TestResult
testAssertTrue True = Nothing
testAssertTrue False = Just "Expected True, got False"

testAssertEq :: (Show a, Eq a) => a -> a -> TestResult
testAssertEq actual expected =
    if actual == expected
        then Nothing
        else Just $ "Expected: " ++ show expected ++ "\nGot: " ++ show actual

testAssertErrorContains :: String -> Result a String -> TestResult
testAssertErrorContains expectedSubstring result =
    case result of
        Ok _ -> Just $ "Expected failure containing: " ++ show expectedSubstring
        Error err ->
            if expectedSubstring `contains` err
                then Nothing
                else
                    Just $
                        "Expected failure containing: "
                            ++ show expectedSubstring
                            ++ "\nGot: "
                            ++ show err
  where
    contains [] _ = True
    contains _ [] = False
    contains needle haystack =
        startsWith needle haystack || contains needle (tail haystack)

    startsWith [] _ = True
    startsWith _ [] = False
    startsWith (n : ns) (h : hs) = n == h && startsWith ns hs

parseValFailStmtHelper :: String -> TestResult
parseValFailStmtHelper stmtStr =
    let parseOutput = parseStatement stmtStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            Right (Block stmts) -> case validateStatements stmts of
                Ok _ -> Just "Validation succeeded expected failure"
                Error _ -> Nothing
            Right _ -> Just "Not a block statement"

-- Control flow tests. A program runs on the MIR once it type checks; nothing here validates it.
parseEvalProgramHelper :: String -> Maybe Value -> TestResult
parseEvalProgramHelper source expected =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> case runStatements stmts of
            Ok result -> testAssertEq (fmap fromMirValue result) expected
            Error e -> Just $ "Evaluation failed with error: " ++ e

parseEvalProgramFailHelper :: String -> String -> TestResult
parseEvalProgramFailHelper source expectedError =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> testAssertErrorContains expectedError (runStatements stmts)

parseValidProgramHelper :: String -> TestResult
parseValidProgramHelper source =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> case validateStatements stmts of
            Ok _ -> Nothing
            Error e -> Just $ "Validation failed with error: " ++ e

parseValidateFailProgramHelper :: String -> String -> TestResult
parseValidateFailProgramHelper source expectedError =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> testAssertErrorContains expectedError (validateStatements stmts)

-- Run tests
-- A function over integers only
nativeInts :: Int -> [Statement] -> FunctBody
nativeInts n = NativeFunct (Signature (replicate n TInt) TInt [] []) Nothing


-- The growable list of `examples/vec.tersus` (without the comments), which the tests build programs on
vecLibrary :: String
vecLibrary =
    unlines
        [ "trait Sequence<E> {"
        , "    fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }];"
        , "    fn get(self: &Self, i: Int) -> E [{ affirm i >= 0; affirm i < size(self); }] [{ }];"
        , "    fn set(self: Self, i: Int, x: E) -> Self [{ affirm i >= 0; affirm i < size(self); }] [{ affirm size(return) = size(self); affirm get(return, i) = x; }];"
        , "    fn push(self: Self, x: E) -> Self [{ }] [{ affirm size(return) = size(self) + 1; affirm get(return, size(self)) = x; }];"
        , "};"
        , "struct Vec<T> {"
        , "    data: Box<Array<T>>,"
        , "    len: Int,"
        , "} invariant [{ affirm len >= 0; affirm len <= size(data); affirm size(data) >= 1; }];"
        , "impl<T> Vec<T> {"
        , "    fn new(filler: T) -> Self [{ }] [{ affirm return.len = 0; }] {"
        , "        return Self { data: Array::boxed(4, filler), len: 0 };"
        , "    };"
        , "    fn pop(self: Self) -> Self [{ affirm self.len >= 1; }] [{ affirm return.len = self.len - 1; }] {"
        , "        return Self { data: self.data, len: self.len - 1 };"
        , "    };"
        , "};"
        , "impl<T> Sequence<T> for Vec<T> {"
        , "    fn size(self: &Self) -> Int [{ }] [{ affirm return = self.len; }] {"
        , "        return self.len;"
        , "    };"
        , "    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return = get(self.data, i); }] {"
        , "        return get(self.data, i);"
        , "    };"
        , "    fn set(self: Self, i: Int, x: T) -> Self [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return.len = self.len; affirm get(return.data, i) = x; }] {"
        , "        return Self { data: set(self.data, i, x), len: self.len };"
        , "    };"
        , "    fn push(self: Self, x: T) -> Self [{ }] [{ affirm return.len = self.len + 1; affirm get(return.data, self.len) = x; }] {"
        , "        if self.len < size(self.data) {"
        , "            return Self { data: set(self.data, self.len, x), len: self.len + 1 };"
        , "        };"
        , "        big = Array::boxed(size(self.data) * 2, x);"
        , "        i = 0;"
        , "        while i < self.len [{ affirm i >= 0; affirm i <= self.len; affirm size(big) = size(self.data) * 2; }] shrinks self.len - i {"
        , "            big = set(big, i, get(self.data, i));"
        , "            i = i + 1;"
        , "        };"
        , "        return Self { data: set(big, self.len, x), len: self.len + 1 };"
        , "    };"
        , "};"
        ]
