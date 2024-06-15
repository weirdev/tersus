module TestTersus where

import Data.Map (Map, empty, fromList, lookup)

import Parse
import Proof
import TersusTypes

-- Core Test data structures
-- Test result is possible error output, else success
type TestResult = Maybe String
data Test = TestCase String TestResult | TestList String [Test] deriving (Show)

-- Core Test helper functions

testCaseSeq :: String -> [TestResult] -> Test
testCaseSeq s results =
    TestList
        s
        (zipWith (\i r -> TestCase (s ++ show i) r) [0 :: Integer ..] results)

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

testAssertTrue :: Bool -> TestResult
testAssertTrue True = Nothing
testAssertTrue False = Just "Expected True, got False"

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

-- Parse tests
testParseSimpleAssign :: Test
testParseSimpleAssign =
    let parseOutput = parseStatementBlock "x = 5"
     in let result = case parseOutput of
                Left _ -> Nothing
                Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
         in TestCase "testParseSimpleAssign" result

testParseComplexAssign :: Test
testParseComplexAssign =
    let parseOutput = parseStatementBlock "x = size([5]); rr = 1 - 1;"
     in let result = case parseOutput of
                Left _ -> Nothing
                Right parsed -> testAssertEq parsed [Assign "x" (F Size [Val (VIntList [5])]), Assign "rr" (F Minus [Val (VInt 1), Val (VInt 1)])]
         in TestCase "testParseComplexAssign" result

testParse :: Test
testParse = TestList "testParse" [testParseSimpleAssign, testParseComplexAssign]

-- Evaluate tests
evalFCHelper :: [Statement] -> [(Variable, Value)] -> TestResult
evalFCHelper stmts expected =
    let State (vals, _) = evaluate stmts
     in testAssertEq vals (Data.Map.fromList expected)

testEvaluateFullContext :: Test
testEvaluateFullContext =
    testCaseSeq
        "testEvaluateFullContext"
        [ evalFCHelper [Assign "x" (F Size [Val (VIntList [5])])] [("x", VInt 1)]
        , evalFCHelper [Assign "x" (F Size [Val (VIntList [5])]), Assign "y" (F Minus [Val (VInt 1), Val (VInt 1)])] [("x", VInt 1), ("y", VInt 0)]
        , evalFCHelper [Assign "x" (Block [Assign "y" (Val (VInt 5)), Assign "z" (F Plus [Var "y", Val (VInt 1)]), Return (Var "z")])] [("x", VInt 6)]
        , evalFCHelper [Assign "f" (Val (VFunct [] (Val (VInt 3)))), Assign "result" (F Call [Var "f"])] [("result", VInt 3), ("f", VFunct [] (Val (VInt 3)))]
        , evalFCHelper [Assign "f" (Val (VFunct [] (Block [Assign "y" (Val (VInt 2)), Return (Var "y")]))), Assign "result" (F Call [Var "f"])] [("result", VInt 2), ("f", VFunct [] (Block [Assign "y" (Val (VInt 2)), Return (Var "y")]))]
        , evalFCHelper [Assign "id" (Val (VFunct ["v"] (Block [Return (Var "v")]))), Assign "result" (F Call [Var "id", Val (VInt 7)])] [("result", VInt 7), ("id", VFunct ["v"] (Block [Return (Var "v")]))]
        , evalFCHelper [Assign "add" (Val (VFunct ["l", "r"] (Block [Return (F Plus [Var "l", Var "r"])]))), Assign "result" (F Call [Var "add", Val (VInt 7), Val (VInt 13)])] [("result", VInt 20), ("add", VFunct ["l", "r"] (Block [Return (F Plus [Var "l", Var "r"])]))]
        ]

evalExprHelper :: Expression -> Value -> TestResult
evalExprHelper expr expected =
    let (mval, _) = evalExpression (State (Data.Map.empty, Nothing)) expr
     in case mval of
            Just val -> testAssertEq val expected
            Nothing -> Just "Expression did not produce a value"

parseEvalExprHelper :: String -> Value -> TestResult
parseEvalExprHelper exprStr expected =
    let parseOutput = parseExpression exprStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> evalExprHelper parsed expected

testParseEvalSimpleExpression :: TestResult
testParseEvalSimpleExpression =
    parseEvalExprHelper "0" (VInt 0)

testParseEvalCompoundExpression :: TestResult
testParseEvalCompoundExpression =
    parseEvalExprHelper "10-5-5" (VInt 0)

testParseEvalBlockExpr :: TestResult
testParseEvalBlockExpr =
    parseEvalExprHelper
        "{x = [5,4,3];\
        \ y = size(x);\
        \ return y;}"
        (VInt 3)

testParseEvalWFunctDef :: TestResult
testParseEvalWFunctDef =
    parseEvalExprHelper
        "{x = 6;\
        \ fn add1(i) {\
        \   return i + 1;\
        \ };\
        \ return add1;}"
        (VFunct ["i"] (Block [Return (F Plus [Var "i", Val (VInt 1)])]))

testParseEvalWUdfCall :: TestResult
testParseEvalWUdfCall =
    parseEvalExprHelper
        "{x = [3, 6, 9, 12];\
        \ fn sumFirstLast(lst) {\
        \   return first(lst) + last(lst);\
        \ };\
        \ return sumFirstLast(x);}"
        (VInt 15)

testParseEval :: Test
testParseEval =
    testCaseSeq
        "testParseEval"
        [ testParseEvalSimpleExpression
        , testParseEvalCompoundExpression
        , testParseEvalBlockExpr
        , testParseEvalWFunctDef
        , testParseEvalWUdfCall
        ]

-- Validation tests
expectedProofMatch :: VariableProof -> [IotaProof] -> Map Variable Iota -> Bool
expectedProofMatch _ [] _ = False
expectedProofMatch vp (ip : ips) varMap = expectedProofCompare vp ip varMap || expectedProofMatch vp ips varMap

expectedProofCompare :: VariableProof -> IotaProof -> Map Variable Iota -> Bool
expectedProofCompare (CTerm v1) (CTerm v2) _ = v1 == v2
expectedProofCompare (ATerm var) (ATerm iota2) varMap = case Data.Map.lookup var varMap of
    Just iota1 -> iota1 == iota2
    Nothing -> False
expectedProofCompare (FApp f1 ps1) (FApp f2 ps2) varMap = f1 == f2 && all (\(p1, p2) -> expectedProofCompare p1 p2 varMap) (zip ps1 ps2)
expectedProofCompare _ _ _ = False

-- Validate with expected proofs
validateWEMatchHelper :: [Statement] -> [VariableProof] -> TestResult
validateWEMatchHelper stmts expected =
    case validate stmts of
        Ok (varMap, iproofs, _) -> testAllTrue (\vp -> expectedProofMatch vp iproofs varMap) expected
        Error e -> Just $ "Validation failed with error: " ++ e

validateWEMismatchHelper :: [Statement] -> [VariableProof] -> TestResult
validateWEMismatchHelper stmts expected =
    case validate stmts of
        Ok (varMap, iproofs, _) -> testAssertTrue (not (all (\vp -> expectedProofMatch vp iproofs varMap) expected))
        Error e -> Just $ "Validation failed with error: " ++ e

validationFailHelper :: [Statement] -> TestResult
validationFailHelper stmts =
    case validate stmts of
        Ok _ -> Just "Validation passed when it should have failed"
        Error _ -> Nothing

testValidateWithExpectedMatch :: Test
testValidateWithExpectedMatch =
    testCaseSeq
        "testValidateWithExpectedMatch"
        [ validateWEMatchHelper [Assign "x" (F Size [Val (VIntList [5])])] [FApp (Rel Eq) [ATerm "x", CTerm (VInt 1)]]
        , validateWEMatchHelper [Assign "x" (Val (VIntList [5, 4])), Assign "y" (F Size [Var "x"])] [FApp (Rel Eq) [ATerm "x", CTerm (VIntList [5, 4])], FApp (Rel Eq) [ATerm "y", CTerm (VInt 2)]]
        , validateWEMatchHelper [Assign "x" (F Size [Val (VIntList [5])]), Assign "y" (F Minus [Val (VInt 1), Val (VInt 1)])] [FApp (Rel Eq) [ATerm "x", CTerm (VInt 1)], FApp (Rel Eq) [ATerm "y", CTerm (VInt 0)]]
        , validateWEMatchHelper [Assign "x" (Val (VInt 5)), ProofAssert (FApp (Rel Eq) [ATerm "x", CTerm (VInt 5)])] [FApp (Rel Eq) [ATerm "x", CTerm (VInt 5)]]
        , validateWEMatchHelper [Assign "x" (Val (VInt 5)), Rewrite (EqToLtPlus1 "x"), ProofAssert (FApp (Rel Lt) [ATerm "x", CTerm (VInt 6)])] [FApp (Rel Eq) [ATerm "x", CTerm (VInt 5)], FApp (Rel Lt) [ATerm "x", CTerm (VInt 6)]]
        , validateWEMatchHelper [Assign "x" (Val (VInt 5)), AssignProofVar "a" (Val (VInt 5)), Rewrite (Refl "x"), ProofAssert (FApp (Rel Eq) [ATerm "x", ATerm "a"])] [FApp (Rel Eq) [ATerm "x", CTerm (VInt 5)], FApp (Rel Eq) [ATerm "a", CTerm (VInt 5)], FApp (Rel Eq) [ATerm "x", ATerm "a"], FApp (Rel Eq) [ATerm "a", ATerm "x"]]
        ]

testValidateWithExpectedMismatch :: Test
testValidateWithExpectedMismatch =
    testCaseSeq
        "testValidateWithExpectedMismatch"
        [ validateWEMismatchHelper [Assign "x" (F Size [Val (VIntList [5])])] [FApp (Rel Eq) [ATerm "y", CTerm (VInt 1)]]
        , validateWEMismatchHelper [Assign "x" (Val (VIntList [5, 4])), Assign "y" (F Size [Var "x"])] [FApp (Rel Eq) [ATerm "x", CTerm (VIntList [5, 4])], FApp (Rel Eq) [ATerm "y", CTerm (VInt 2)], FApp (Rel Eq) [ATerm "z", CTerm (VInt 2)]]
        , validateWEMismatchHelper [Assign "x" (Val (VInt 5)), AssignProofVar "a" (Val (VInt 5)), Rewrite (Refl "x"), ProofAssert (FApp (Rel Eq) [ATerm "x", ATerm "a"])] [FApp (Rel Eq) [ATerm "x", CTerm (VInt 5)], FApp (Rel Eq) [ATerm "a", CTerm (VInt 5)], FApp (Rel Eq) [ATerm "x", ATerm "a"], FApp (Rel Eq) [ATerm "b", ATerm "x"]]
        ]

testValidationFail :: Test
testValidationFail =
    testCaseSeq
        "testValidationFail"
        [ validationFailHelper [ProofAssert (FApp (Rel Lt) [ATerm "x", CTerm (VInt 5)])]
        , validationFailHelper [Assign "x" (Val (VInt 5)), ProofAssert (FApp (Rel Lt) [ATerm "x", CTerm (VInt 4)])]
        ]

-- Run tests
main :: IO ()
main = do
    runTest testParse
    runTest testEvaluateFullContext
    runTest testParseEval
    runTest testValidateWithExpectedMatch
    runTest testValidateWithExpectedMismatch
    runTest testValidationFail