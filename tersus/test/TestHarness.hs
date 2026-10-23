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
    ) where

import qualified Control.Exception as Exception
import Control.Exception (SomeException, displayException, try)
import MirLower (lowerElaborated, lowerProgram)
import MirValidate (validateProgram)
import TypeCheck (elaborate)
import Parse
import Proof
import ProofHelpers
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
            Right (Block stmts) -> case valReturningBlock (initVStateWStatements stmts) of
                Ok _ -> Just "Validation succeeded expected failure"
                Error _ -> case newValidate stmts of
                    Ok () -> Just "NEW validator accepted a program that should fail"
                    Error _ -> Nothing
            Right _ -> Just "Not a block statement"

-- Control flow tests
parseEvalProgramHelper :: String -> Maybe Value -> TestResult
parseEvalProgramHelper source expected =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> case evaluate stmts of
            Ok state -> testAssertEq (getReturn state) expected
            Error e -> Just $ "Evaluation failed with error: " ++ e

parseEvalProgramFailHelper :: String -> String -> TestResult
parseEvalProgramFailHelper source expectedError =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> testAssertErrorContains expectedError (evaluate stmts)

parseValidProgramHelper :: String -> TestResult
parseValidProgramHelper source =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> case validate stmts of
            -- (a program that validates must also lower to a MIR that passes the verifier)
            Ok _ -> case lowerProgram stmts of
                Ok _ -> case newValidate stmts of
                    Ok () -> Nothing
                    Error e -> Just $ "NEW validator failed with error: " ++ e
                Error e -> Just $ "Lowering failed with error: " ++ e
            Error e -> Just $ "Validation failed with error: " ++ e

parseValidateFailProgramHelper :: String -> String -> TestResult
parseValidateFailProgramHelper source expectedError =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> case testAssertErrorContains expectedError (validate stmts) of
            Just e -> Just e
            Nothing -> case newValidate stmts of
                Ok () -> Just "NEW validator accepted a program that should fail"
                Error e -> fmap ("NEW validator: " ++) (testAssertErrorContains expectedError (Error e :: Result () String))

-- Validation on the MIR
newValidate :: [Statement] -> Result () String
newValidate stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` \program ->
            mapResult (const ()) (validateProgram program)

-- Run tests
-- A function over integers only
nativeInts :: Int -> [Statement] -> FunctBody
nativeInts n = NativeFunct (Signature (replicate n TInt) TInt) Nothing
