module TestTersus where

import Data.Map (fromList)

import Parse
import Proof
import TersusTypes

-- Test result is possible error output, else success
type TestResult = Maybe String
data Test = TestCase String TestResult | TestList String [Test] deriving (Show)

testCaseSeq :: String -> [TestResult] -> Test
testCaseSeq s results = TestList s (map (\(i, r) -> TestCase (s ++ (show i)) r) (zip [0 ..] results))

runTest :: Test -> IO ()
runTest (TestCase s r) =
    putStrLn $
        s
            ++ " - "
            ++ ( case r of
                    Nothing -> "Pass"
                    Just e -> "Fail\n" ++ e
               )
runTest (TestList s ts) = do
    putStrLn $ "Running test list: " ++ s
    mapM_ runTest ts
    putStrLn ""

testAssertEq :: (Show a, Eq a) => a -> a -> TestResult
testAssertEq actual expected =
    if actual == expected
        then Nothing
        else Just $ "Expected: " ++ (show expected) ++ "\nGot: " ++ (show actual)

testParseSimpleAssign :: Test
testParseSimpleAssign =
    let parseOutput = parseStatementBlock "assign x = 5"
     in let result = case parseOutput of
                Left _ -> Nothing
                Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
         in TestCase "testParseSimpleAssign" result

testParseComplexAssign :: Test
testParseComplexAssign =
    let parseOutput = parseStatementBlock "assign x = size([5]); assign yy = 1 - 1;"
     in let result = case parseOutput of
                Left _ -> Nothing
                Right parsed -> testAssertEq parsed [Assign "x" (F Size [(Val (VIntList [5]))]), Assign "yy" (F Minus [(Val (VInt 1)), (Val (VInt 1))])]
         in TestCase "testParseComplexAssign" result

testParse :: Test
testParse = TestList "testParse" [testParseSimpleAssign, testParseComplexAssign]

evalFCHelper :: [Statement] -> [(Variable, Value)] -> TestResult
evalFCHelper stmts expected =
    let (vals, _, _) = evaluate stmts
     in testAssertEq vals (Data.Map.fromList expected)

testEvaluateFullContext :: Test
testEvaluateFullContext =
    testCaseSeq
        "testEvaluateFullContext"
        [ evalFCHelper [Assign "x" (F Size [(Val (VIntList [5]))])] [("x", VInt 1)]
        ]

main :: IO ()
main = do
    runTest testParse
    runTest testEvaluateFullContext