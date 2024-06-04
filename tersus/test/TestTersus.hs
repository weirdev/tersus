module TestTersus where

import TersusTypes
import Parse

data Test = TestCase String Bool | TestList String [Test] deriving Show

runTest :: Test -> IO ()
runTest (TestCase s b) = putStrLn $ s ++ " - " ++ (if b then "Pass" else "Fail")
runTest (TestList s ts) = do
    putStrLn $ "Running test list: " ++ s
    mapM_ runTest ts
    putStrLn ""

testParseSimpleAssign :: Test
testParseSimpleAssign = let parseOutput = parseStatementBlock "assign x = 5"
            in let result = case parseOutput of
                    Left _ -> False
                    Right parsed -> parsed == [Assign "x" (Val (VInt 5))]
                in TestCase "testParseSimpleAssign" result

testParseComplexAssign :: Test
testParseComplexAssign = let parseOutput = parseStatementBlock "assign x = size([5]); assign yy = 1 - 1;"
            in let result = case parseOutput of
                    Left _ -> False
                    Right parsed -> parsed == [Assign "x" (F Size [(Val (VIntList [5]))]), Assign "yy" (F Minus [(Val (VInt 1)), (Val (VInt 1))])]
                in TestCase "testParseComplexAssign" result

testParse :: Test
testParse = TestList "testParse" [testParseSimpleAssign, testParseComplexAssign]

main :: IO ()
main = do 
    runTest testParse