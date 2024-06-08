module TestTersus where

import Data.Map (Map, fromList, lookup)

import Parse
import Proof
import TersusTypes

-- Core Test data structures
-- Test result is possible error output, else success
type TestResult = Maybe String
data Test = TestCase String TestResult | TestList String [Test] deriving (Show)

type IotaAssignments = Map Iota Iota
type IotaFailedAssignments = Map Iota [Iota]
type VarAssignedProof = Proof (Either Iota String)

-- Core Test helper functions

testCaseSeq :: String -> [TestResult] -> Test
testCaseSeq s results = TestList s (zipWith (\i r -> TestCase (s ++ show i) r) [0 :: Integer ..] results)

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
        else Just $ "Expected: " ++ show expected ++ "\nGot: " ++ show actual

testAllTrue :: (Show a) => (a -> Bool) -> [a] -> TestResult
testAllTrue _ [] = Nothing
testAllTrue f (x : xs) =
    if f x
        then testAllTrue f xs
        else Just $ "Failed for: " ++ show x

-- Tests
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
                Right parsed -> testAssertEq parsed [Assign "x" (F Size [Val (VIntList [5])]), Assign "yy" (F Minus [Val (VInt 1), Val (VInt 1)])]
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
        [ evalFCHelper [Assign "x" (F Size [Val (VIntList [5])])] [("x", VInt 1)]
        , evalFCHelper [Assign "x" (F Size [Val (VIntList [5])]), Assign "y" (F Minus [Val (VInt 1), Val (VInt 1)])] [("x", VInt 1), ("y", VInt 0)]
        ]

expectedProofMatch :: VariableProof -> [IotaProof] -> Map Variable Iota -> Bool
expectedProofMatch _ [] _ = False
expectedProofMatch vp (ip : ips) varMap = expectedProofCompare vp ip varMap || expectedProofMatch vp ips varMap

expectedProofCompare :: VariableProof -> IotaProof -> Map Variable Iota -> Bool
expectedProofCompare (CTerm v1) (CTerm v2) _ = v1 == v2
expectedProofCompare (ATerm var) (ATerm iota2) varMap = case Data.Map.lookup var varMap of
    Just iota1 -> iota1 == iota2
    Nothing -> False
expectedProofCompare (FApp2 f1 ps1) (FApp2 f2 ps2) varMap = f1 == f2 && all (\(p1, p2) -> expectedProofCompare p1 p2 varMap) (zip ps1 ps2)
expectedProofCompare _ _ _ = False

validateFCHelper :: [Statement] -> [VariableProof] -> TestResult
validateFCHelper stmts expected =
    let (varMap, iproofs, _) = validate stmts
     in testAllTrue (\vp -> expectedProofMatch vp iproofs varMap) expected

testValidateFullContextSuccesses :: Test
testValidateFullContextSuccesses =
    testCaseSeq
        "testValidateFullContextSuccess"
        [ validateFCHelper [Assign "x" (F Size [Val (VIntList [5])])] [FApp2 (Rel Eq) [ATerm "x", CTerm (VInt 1)]]
        , validateFCHelper [Assign "x" (Val (VIntList [5, 4])), Assign "y" (F Size [Var "x"])] [FApp2 (Rel Eq) [ATerm "x", CTerm (VIntList [5, 4])], FApp2 (Rel Eq) [ATerm "y", CTerm (VInt 2)]]
        , validateFCHelper [Assign "x" (F Size [Val (VIntList [5])]), Assign "y" (F Minus [Val (VInt 1), Val (VInt 1)])] [FApp2 (Rel Eq) [ATerm "x", CTerm (VInt 1)], FApp2 (Rel Eq) [ATerm "y", CTerm (VInt 0)]]
        , validateFCHelper [Assign "x" (Val (VInt 5)), ProofAssert (FApp2 (Rel Eq) [ATerm "x", CTerm (VInt 5)])] [FApp2 (Rel Eq) [ATerm "x", CTerm (VInt 5)]]
        , validateFCHelper [Assign "x" (Val (VInt 5)), Rewrite (EqToLtPlus1 "x"), ProofAssert (FApp2 (Rel Lt) [ATerm "x", CTerm (VInt 6)])] [FApp2 (Rel Eq) [ATerm "x", CTerm (VInt 5)], FApp2 (Rel Lt) [ATerm "x", CTerm (VInt 6)]]
        , validateFCHelper [Assign "x" (Val (VInt 5)), AssignProofVar "a" (Val (VInt 5)), Rewrite (Refl "x"), ProofAssert (FApp2 (Rel Eq) [ATerm "x", ATerm "a"])] [FApp2 (Rel Eq) [ATerm "x", CTerm (VInt 5)], FApp2 (Rel Eq) [ATerm "a", CTerm (VInt 5)], FApp2 (Rel Eq) [ATerm "x", ATerm "a"], FApp2 (Rel Eq) [ATerm "a", ATerm "x"]]
        ]

main :: IO ()
main = do
    runTest testParse
    runTest testEvaluateFullContext
    runTest testValidateFullContextSuccesses