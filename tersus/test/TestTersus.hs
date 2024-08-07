module TestTersus where

import Data.Map (Map, fromList, lookup)

import Parse
import Proof
import ProofHelpers
import StdLib
import TersusTypes
import Utils

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
                Right parsed ->
                    testAssertEq
                        parsed
                        [ Assign "x" (F (Var "size") [Val (VIntList [5])])
                        , Assign "rr" (F (Val (builtinFunct Minus)) [Val (VInt 1), Val (VInt 1)])
                        ]
         in TestCase "testParseComplexAssign" result

testParse :: Test
testParse = TestList "testParse" [testParseSimpleAssign, testParseComplexAssign]

-- Evaluate tests
evalFCHelper :: [Statement] -> [(Variable, Value)] -> TestResult
evalFCHelper stmts expected =
    let State (ScopeState (vals, _, _), _) = evaluate stmts
     in testAssertEq vals (Data.Map.fromList expected)

testEvaluateFullContext :: Test
testEvaluateFullContext =
    testCaseSeq
        "testEvaluateFullContext"
        [ evalFCHelper [Assign "x" (F (Var "size") [Val (VIntList [5])])] [("x", VInt 1)]
        , evalFCHelper
            [ Assign "x" (F (Var "size") [Val (VIntList [5])])
            , Assign "y" (F (Val (builtinFunct Minus)) [Val (VInt 1), Val (VInt 1)])
            ]
            [("x", VInt 1), ("y", VInt 0)]
        , evalFCHelper
            [ Assign "f" (Val (VFunct [] [] (NativeFunct [Return (Val (VInt 3))]) []))
            , Assign "result" (F (Var "f") [])
            ]
            [("result", VInt 3), ("f", VFunct [] [] (NativeFunct [Return (Val (VInt 3))]) [])]
        , evalFCHelper
            [ Assign "f" (Val (VFunct [] [] (NativeFunct [Assign "y" (Val (VInt 2)), Return (Var "y")]) []))
            , Assign "result" (F (Var "f") [])
            ]
            [("result", VInt 2), ("f", VFunct [] [] (NativeFunct [Assign "y" (Val (VInt 2)), Return (Var "y")]) [])]
        , evalFCHelper
            [ Assign "id" (Val (VFunct ["v"] [] (NativeFunct [Return (Var "v")]) []))
            , Assign "result" (F (Var "id") [Val (VInt 7)])
            ]
            [("result", VInt 7), ("id", VFunct ["v"] [] (NativeFunct [Return (Var "v")]) [])]
        , evalFCHelper
            [ Assign "add" (Val (VFunct ["l", "r"] [] (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "l", Var "r"])]) []))
            , Assign "result" (F (Var "add") [Val (VInt 7), Val (VInt 13)])
            ]
            [("result", VInt 20), ("add", VFunct ["l", "r"] [] (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "l", Var "r"])]) [])]
        ]

evalExprHelper :: Expression -> Value -> TestResult
evalExprHelper expr expected =
    let (mval, _) = evalExpression initState expr
     in case mval of
            Just val -> testAssertEq val expected
            Nothing -> Just "Expression did not produce a value"

parseEvalExprHelper :: String -> Value -> TestResult
parseEvalExprHelper exprStr expected =
    let parseOutput = parseExpression exprStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> evalExprHelper parsed expected

parseEvalReturningStmtHelper :: String -> Value -> TestResult
parseEvalReturningStmtHelper stmtStr expected =
    let parseOutput = parseStatement stmtStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            Right (Block stmts) -> case evalReturningBlock (setPScope (initStateWStatements stmts) (Just emptyScopeState)) of
                (_, Just val) -> testAssertEq val expected
                (_, Nothing) -> Just "No value returned"
            Right _ -> Just "Not a block statement"

testParseEvalSimpleExpression :: TestResult
testParseEvalSimpleExpression =
    parseEvalExprHelper "0" (VInt 0)

testParseEvalCompoundExpression :: TestResult
testParseEvalCompoundExpression =
    parseEvalExprHelper "10-5-5" (VInt 0)

testParseEvalBlockExpr :: TestResult
testParseEvalBlockExpr =
    parseEvalReturningStmtHelper
        "{\
        \  x = [5,4,3];\
        \  y = size(x);\
        \  return y;\
        \}"
        (VInt 3)

testParseEvalWFunctDef :: TestResult
testParseEvalWFunctDef =
    parseEvalReturningStmtHelper
        "{\
        \  x = 6;\
        \  fn add1(i) {\
        \    return i + 1;\
        \  };\
        \  return add1;\
        \}"
        (VFunct ["i"] [] (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "i", Val (VInt 1)])]) [])

testParseEvalWUdfCall :: TestResult
testParseEvalWUdfCall =
    parseEvalReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  fn sumFirstLast(lst) {\
        \    return first(lst) + last(lst);\
        \  };\
        \  return sumFirstLast(x);\
        \}"
        (VInt 15)

testParseNestedBlocks :: TestResult
testParseNestedBlocks =
    parseEvalReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  {\
        \    x = [1];\
        \  };\
        \  return size(x);\
        \}"
        (VInt 1)

testParseFunctReturnNestedBlocks :: TestResult
testParseFunctReturnNestedBlocks =
    parseEvalReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  fn getFirst(y) {\
        \    x = [1];\
        \    {\
        \      return first(y);\
        \    };\
        \    return first(x);\
        \  };\
        \  return getFirst(x);\
        \}"
        (VInt 3)

testParseEval :: Test
testParseEval =
    testCaseSeq
        "testParseEval"
        [ testParseEvalSimpleExpression
        , testParseEvalCompoundExpression
        , testParseEvalBlockExpr
        , testParseEvalWFunctDef
        , testParseEvalWUdfCall
        , testParseNestedBlocks
        , testParseFunctReturnNestedBlocks
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
expectedProofCompare (FApp f1 ps1) (FApp f2 ps2) varMap =
    expectedProofCompare f1 f2 varMap
        && all (\(p1, p2) -> expectedProofCompare p1 p2 varMap) (zip ps1 ps2)
expectedProofCompare _ _ _ = False

-- Validate with expected proofs
validateWEMatchHelper :: [Statement] -> [VariableProof] -> TestResult
validateWEMatchHelper stmts expected =
    case validate stmts of
        Ok (VState (VScopeState (varMap, iproofs, _, _), _, _, _)) ->
            testAllTrue (\vp -> expectedProofMatch vp iproofs varMap) expected
        Error e -> Just $ "Validation failed with error: " ++ e

validateWEMismatchHelper :: [Statement] -> [VariableProof] -> TestResult
validateWEMismatchHelper stmts expected =
    case validate stmts of
        Ok (VState (VScopeState (varMap, iproofs, _, _), _, _, _)) ->
            testAssertTrue (not (all (\vp -> expectedProofMatch vp iproofs varMap) expected))
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
        [ validateWEMatchHelper
            [ Assign "x" (F (Val (builtinFunct Size)) [Val (VIntList [5])])
            ]
            [FApp eqProof [ATerm "x", CTerm (VInt 1)]]
        , validateWEMatchHelper
            [ Assign "x" (Val (VIntList [5, 4]))
            , Assign "y" (F (Val (builtinFunct Size)) [Var "x"])
            ]
            [ FApp eqProof [ATerm "x", CTerm (VIntList [5, 4])]
            , FApp eqProof [ATerm "y", CTerm (VInt 2)]
            ]
        , validateWEMatchHelper
            [ Assign "x" (F (Val (builtinFunct Size)) [Val (VIntList [5])])
            , Assign "y" (F (Val (builtinFunct Minus)) [Val (VInt 1), Val (VInt 1)])
            ]
            [ FApp eqProof [ATerm "x", CTerm (VInt 1)]
            , FApp eqProof [ATerm "y", CTerm (VInt 0)]
            ]
        , validateWEMatchHelper
            [ Assign "x" (Val (VInt 5))
            , ValidationStatement (ProofAssert (FApp eqProof [ATerm "x", CTerm (VInt 5)]))
            ]
            [FApp eqProof [ATerm "x", CTerm (VInt 5)]]
        , validateWEMatchHelper
            [ Assign "x" (Val (VInt 5))
            , ValidationStatement (Rewrite (EqToLtPlus1 "x"))
            , ValidationStatement (ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 6)]))
            ]
            [ FApp eqProof [ATerm "x", CTerm (VInt 5)]
            , FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 6)]
            ]
        , validateWEMatchHelper
            [ Assign "x" (Val (VInt 5))
            , ValidationStatement (AssignProofVar "a" (Val (VInt 5)))
            , ValidationStatement (Rewrite (Refl (ATerm "x")))
            , ValidationStatement (ProofAssert (FApp eqProof [ATerm "x", ATerm "a"]))
            ]
            [ FApp eqProof [ATerm "x", CTerm (VInt 5)]
            , FApp eqProof [ATerm "a", CTerm (VInt 5)]
            , FApp eqProof [ATerm "x", ATerm "a"]
            , FApp eqProof [ATerm "a", ATerm "x"]
            ]
        ]

testValidateWithExpectedMismatch :: Test
testValidateWithExpectedMismatch =
    testCaseSeq
        "testValidateWithExpectedMismatch"
        [ validateWEMismatchHelper
            [ Assign
                "x"
                ( F
                    (Val (builtinFunct Size))
                    [Val (VIntList [5])]
                )
            ]
            [FApp eqProof [ATerm "y", CTerm (VInt 1)]]
        , validateWEMismatchHelper
            [ Assign "x" (Val (VIntList [5, 4]))
            , Assign "y" (F (Val (builtinFunct Size)) [Var "x"])
            ]
            [ FApp eqProof [ATerm "x", CTerm (VIntList [5, 4])]
            , FApp eqProof [ATerm "y", CTerm (VInt 2)]
            , FApp eqProof [ATerm "z", CTerm (VInt 2)]
            ]
        , validateWEMismatchHelper
            [ Assign
                "x"
                (Val (VInt 5))
            , ValidationStatement (AssignProofVar "a" (Val (VInt 5)))
            , ValidationStatement (Rewrite (Refl (ATerm "x")))
            , ValidationStatement (ProofAssert (FApp eqProof [ATerm "x", ATerm "a"]))
            ]
            [ FApp eqProof [ATerm "x", CTerm (VInt 5)]
            , FApp eqProof [ATerm "a", CTerm (VInt 5)]
            , FApp eqProof [ATerm "x", ATerm "a"]
            , FApp eqProof [ATerm "b", ATerm "x"]
            ]
        ]

testValidationFail :: Test
testValidationFail =
    testCaseSeq
        "testValidationFail"
        [ validationFailHelper [ValidationStatement (ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 5)]))]
        , validationFailHelper [Assign "x" (Val (VInt 5)), ValidationStatement (ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 4)]))]
        ]

testIotaProofVarProofMatch :: Iota -> [IotaProof] -> Variable -> [VariableProof] -> TestResult
testIotaProofVarProofMatch i ip v vp =
    let varMap = Data.Map.fromList [(v, i)]
     in case testAllTrue (\p -> expectedProofMatch p ip varMap) vp of
            Nothing -> Nothing
            Just e -> Just $ e ++ " had " ++ show ip

parseValReturningStmtHelper :: String -> Variable -> [VariableProof] -> TestResult
parseValReturningStmtHelper stmtStr expVar expected =
    let parseOutput = parseStatement stmtStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            -- Just $ VScopeState (Data.Map.empty, [], emptyContinuations, Nothing)
            Right (Block stmts) -> case valReturningBlock (initVStateWStatements stmts) of
                Ok (VState (VScopeState (_, proofs, _, _), _, _, _), Just iota) -> testIotaProofVarProofMatch iota proofs expVar expected
                Ok (_, Nothing) -> Just "No value returned"
                Error e -> Just $ "Validation failed with error: " ++ e
            Right _ -> Just "Not a block statement"

testParseValBlockExpr :: TestResult
testParseValBlockExpr =
    parseValReturningStmtHelper
        "{\
        \  x = [5,4,3];\
        \  y = size(x);\
        \  return y;\
        \}"
        "ret"
        [FApp eqProof [ATerm "ret", CTerm (VInt 3)]]

testParseValWFunctDef :: TestResult
testParseValWFunctDef =
    parseValReturningStmtHelper
        "{\
        \  x = 6;\
        \  fn add1(i) {\
        \    return i + 1;\
        \  };\
        \  return add1;\
        \}"
        "ret"
        [ FApp
            eqProof
            [ ATerm "ret"
            , CTerm (VFunct ["i"] [] (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "i", Val (VInt 1)])]) [])
            ]
        ]

testParseValWUdfCall :: TestResult
testParseValWUdfCall =
    parseValReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  fn sumFirstLast(lst) {\
        \    return first(lst) + last(lst);\
        \  };\
        \  return sumFirstLast(x);\
        \}"
        "ret"
        [FApp eqProof [ATerm "ret", CTerm (VInt 15)]]

testValidateNestedBlocks :: TestResult
testValidateNestedBlocks =
    parseValReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  {\
        \    x = [1];\
        \  };\
        \  return size(x);\
        \}"
        "ret"
        [FApp eqProof [ATerm "ret", CTerm (VInt 1)]]

testParseValFunctReturnNestedBlocks :: TestResult
testParseValFunctReturnNestedBlocks =
    parseValReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  fn getFirst(y) {\
        \    x = [1];\
        \    {\
        \      return first(y);\
        \    };\
        \    return first(x);\
        \  };\
        \  return getFirst(x);\
        \}"
        "ret"
        [FApp eqProof [ATerm "ret", CTerm (VInt 3)]]

testParseVal :: Test
testParseVal =
    testCaseSeq
        "testParseVal"
        [ testParseValBlockExpr
        , testParseValWFunctDef
        , testParseValWUdfCall
        , testValidateNestedBlocks
        , testParseValFunctReturnNestedBlocks
        ]

parseValFailStmtHelper :: String -> TestResult
parseValFailStmtHelper stmtStr =
    let parseOutput = parseStatement stmtStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            Right (Block stmts) -> case valReturningBlock (initVStateWStatements stmts) of
                Ok _ -> Just "Validation succeeded expected failure"
                Error _ -> Nothing
            Right _ -> Just "Not a block statement"

testParseValAffirmFail :: TestResult
testParseValAffirmFail =
    parseValFailStmtHelper
        "{\
        \  x = 5;\
        \  affirm x < 4;\
        \}"

testParseValAffirmParensFail :: TestResult
testParseValAffirmParensFail =
    parseValFailStmtHelper
        "{\
        \  x = 5;\
        \  affirm x < (5 - 1);\
        \}"

testParseValFail :: Test
testParseValFail =
    testCaseSeq
        "testParseValFail"
        [ testParseValAffirmFail
        , testParseValAffirmParensFail
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
    runTest testParseVal
    runTest testParseValFail