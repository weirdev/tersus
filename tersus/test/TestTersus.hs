module TestTersus (main) where

import qualified Control.Exception as Exception
import Control.Exception (SomeException, displayException, try)
import Control.Monad (when)
import Data.List (isInfixOf)
import qualified Data.Map as Map
import System.Exit (exitFailure)

import Cli
import Parse
import Proof
import qualified ProofEngine as Engine
import ProofHelpers
import StdLib
import TersusTypes
import TypeCheck
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

testAllTrue :: (Show a) => (a -> Bool) -> [a] -> TestResult
testAllTrue _ [] = Nothing
testAllTrue f (x : xs) =
    if f x
        then testAllTrue f xs
        else Just $ "Failed for: " ++ show x

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

-- Tests

-- Parse tests
testParseSimpleAssign :: Test
testParseSimpleAssign =
    let parseOutput = parseStatementBlock "x = 5"
     in let result = case parseOutput of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
          in testCase "testParseSimpleAssign" result

testParseComplexAssign :: Test
testParseComplexAssign =
    let parseOutput = parseStatementBlock "x = size([5]); rr = 1 - 1;"
     in let result = case parseOutput of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed ->
                    testAssertEq
                        parsed
                        [ Assign "x" (F (Var "size") [Val (VList [VInt 5])])
                        , Assign "rr" (F (Val (builtinFunct Minus)) [Val (VInt 1), Val (VInt 1)])
                        ]
          in testCase "testParseComplexAssign" result

testParseBoolLiteral :: Test
testParseBoolLiteral =
    testCaseSeq
        "testParseBoolLiteral"
        [ case parseStatementBlock "x = true" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "x" (Val (VBool True))]
        , case parseStatement "affirm b = false" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (ProofAssert (FApp eqVarProof [ATerm "b", CTerm (VBool False)])))
        ]

testParseKeywordBoundaryIdentifiers :: Test
testParseKeywordBoundaryIdentifiers =
    testCaseSeq
        "testParseKeywordBoundaryIdentifiers"
        [ case parseStatementBlock "returnx = 5" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "returnx" (Val (VInt 5))]
        , case parseStatementBlock "rewriteRule = 5" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "rewriteRule" (Val (VInt 5))]
        , case parseStatementBlock "affirmed = 5" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "affirmed" (Val (VInt 5))]
        , case parseStatementBlock "defineVar = 5" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "defineVar" (Val (VInt 5))]
        ]

testParseInvalidProofBuiltin :: Test
testParseInvalidProofBuiltin =
    testCase "testParseInvalidProofBuiltin" $
        case parseStatement "affirm bogus(x)" of
            Left _ -> Nothing
            Right parsed -> Just $ "Expected parse failure, got: " ++ show parsed

testParseInvalidRewriteRule :: Test
testParseInvalidRewriteRule =
    testCase "testParseInvalidRewriteRule" $
        case parseStatement "rewrite noSuchRule x" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (Rewrite (UserRewrite "noSuchRule" [ATerm "x"])))

testParseRewriteRules :: Test
testParseRewriteRules =
    testCaseSeq
        "testParseRewriteRules"
        [ case parseStatement "rewrite refl x = 5" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (Rewrite (Refl (FApp eqVarProof [ATerm "x", CTerm (VInt 5)]))))
        , case parseStatement "rewrite eqToLtPlus1 x" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (Rewrite (UserRewrite "eqToLtPlus1" [ATerm "x"])))
        , case parseStatement "rewrite eqToGtZero x" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (Rewrite (UserRewrite "eqToGtZero" [ATerm "x"])))
        , case parseStatement "rewrite eval x" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (Rewrite (Eval "x")))
        , case parseStatement "rewrite evalAll" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (Rewrite EvalAll))
        , case parseStatement "rewrite checkGtZero x" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed (ValidationStatement (Rewrite (CheckGtZero (ATerm "x"))))
        , case parseStatement "rewrite checkRel i < 3" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed ->
                testAssertEq
                    parsed
                    (ValidationStatement (Rewrite (CheckRel (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "i", CTerm (VInt 3)]))))
        ]

testParseUserRuleDefinitions :: Test
testParseUserRuleDefinitions =
    testCaseSeq
        "testParseUserRuleDefinitions"
        [ case parseStatement "axiom five(x) [{}] [{ affirm x = 5; }]" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed ->
                testAssertEq
                    parsed
                    ( AxiomDef
                        "five"
                        ["x"]
                        []
                        [ProofAssert (FApp eqVarProof [ATerm "x", CTerm (VInt 5)])]
                    )
        , case parseStatement "proof keepGt(x) [{ affirm x > 0; }] [{ affirm x > 0; }] { affirm x > 0; }" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed ->
                let gtZero = ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])
                 in testAssertEq parsed (ProofDef "keepGt" ["x"] [gtZero] [gtZero] [gtZero])
        ]

testParseComments :: Test
testParseComments =
    testCaseSeq
        "testParseComments"
        [ case parseStatementBlock "x = 5; // trailing\n// whole line\ny = x;" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5)), Assign "y" (Var "x")]
        , case parseStatementBlock "// leading\nx = 5 // before the semicolon\n;// no space\n" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
        , case parseStatementBlock "x = 5; // ends the input" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
        , case parseStatementBlock "x = [1, // one\n 2];\nfn f(a: List<Int>) -> List<Int> [{ // in\n affirm a = 1; // out\n}] { // body\n return a; };" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertTrue (length parsed == 2)
        , case parseStatementBlock "x = 5; // y = 6;\n" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
        , case parseStatementBlock "x = 5 /" of
            Left _ -> Nothing
            Right parsed -> Just $ "Expected parse failure for a dangling slash, got: " ++ show parsed
        ]

testParse :: Test
testParse =
    TestList
        "testParse"
        [ testParseSimpleAssign
        , testParseComments
        , testParseComplexAssign
        , testParseBoolLiteral
        , testParseKeywordBoundaryIdentifiers
        , testParseInvalidProofBuiltin
        , testParseInvalidRewriteRule
        , testParseRewriteRules
        , testParseUserRuleDefinitions
        ]

-- Evaluate tests
evalFCHelper :: [Statement] -> [(Variable, Value)] -> TestResult
evalFCHelper stmts expected =
    case evaluate stmts of
        Ok (State (ScopeState vals _ _) _) -> testAssertEq vals (Map.fromList expected)
        Error e -> Just $ "Evaluation failed with error: " ++ e

testEvaluateFullContext :: Test
testEvaluateFullContext =
    testCaseSeq
        "testEvaluateFullContext"
        [ evalFCHelper [Assign "x" (F (Var "size") [Val (VList [VInt 5])])] [("x", VInt 1)]
        , evalFCHelper
            [ Assign "x" (F (Var "size") [Val (VList [VInt 5])])
            , Assign "y" (F (Val (builtinFunct Minus)) [Val (VInt 1), Val (VInt 1)])
            ]
            [("x", VInt 1), ("y", VInt 0)]
        , evalFCHelper
            [ Assign "f" (Val (VFunct [] [] [] (nativeInts 1 [Return (Val (VInt 3))]) []))
            , Assign "result" (F (Var "f") [])
            ]
            [("result", VInt 3), ("f", VFunct [] [] [] (nativeInts 1 [Return (Val (VInt 3))]) [])]
        , evalFCHelper
            [ Assign "f" (Val (VFunct [] [] [] (nativeInts 1 [Assign "y" (Val (VInt 2)), Return (Var "y")]) []))
            , Assign "result" (F (Var "f") [])
            ]
            [("result", VInt 2), ("f", VFunct [] [] [] (nativeInts 1 [Assign "y" (Val (VInt 2)), Return (Var "y")]) [])]
        , evalFCHelper
            [ Assign "id" (Val (VFunct ["v"] [] [] (nativeInts 1 [Return (Var "v")]) []))
            , Assign "result" (F (Var "id") [Val (VInt 7)])
            ]
            [("result", VInt 7), ("id", VFunct ["v"] [] [] (nativeInts 1 [Return (Var "v")]) [])]
        , evalFCHelper
            [ Assign "add" (Val (VFunct ["l", "r"] [] [] (nativeInts 2 [Return (F (Val (builtinFunct Plus)) [Var "l", Var "r"])]) []))
            , Assign "result" (F (Var "add") [Val (VInt 7), Val (VInt 13)])
            ]
            [("result", VInt 20), ("add", VFunct ["l", "r"] [] [] (nativeInts 2 [Return (F (Val (builtinFunct Plus)) [Var "l", Var "r"])]) [])]
        ]

evalExprHelper :: Expression -> Value -> TestResult
evalExprHelper expr expected =
    case evalExpression initState expr of
        Ok (val, _) -> testAssertEq val expected
        Error e -> Just $ "Expression failed with error: " ++ e

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
            Right (Block stmts) -> doTrace (show stmts) $
                case evalReturningBlock (setPScope (initStateWStatements stmts) (Just emptyScopeState)) of
                    Ok (_, Just val) -> testAssertEq val expected
                    Ok (_, Nothing) -> Just "No value returned"
                    Error e -> Just $ "Evaluation failed with error: " ++ e
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
        \  fn add1(i: Int) -> Int {\
        \    return i + 1;\
        \  };\
        \  return add1;\
        \}"
        (VFunct ["i"] [] [] (nativeInts 1 [Return (F (Val (builtinFunct Plus)) [Var "i", Val (VInt 1)])]) [])

testParseEvalWUdfCall :: TestResult
testParseEvalWUdfCall =
    parseEvalReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  fn sumFirstLast(lst: List<Int>) -> Int {\
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
        \  fn getFirst(y: Int) -> Int {\
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
expectedProofMatch :: VariableProof -> [IotaProof] -> Map.Map Variable Iota -> Bool
expectedProofMatch _ [] _ = False
expectedProofMatch vp (ip : ips) varMap = expectedProofCompare vp ip varMap || expectedProofMatch vp ips varMap

expectedProofCompare :: VariableProof -> IotaProof -> Map.Map Variable Iota -> Bool
expectedProofCompare (CTerm v1) (CTerm v2) _ = v1 == v2
expectedProofCompare (ATerm var) (ATerm iota2) varMap = case Map.lookup var varMap of
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
        Ok (VState (VScopeState varMap iproofs _ _) _ _ _ _) ->
            testAllTrue (\vp -> expectedProofMatch vp iproofs varMap) expected
        -- Just $ show (varMap, iproofs)
        Error e -> Just $ "Validation failed with error: " ++ e

validateWEMismatchHelper :: [Statement] -> [VariableProof] -> TestResult
validateWEMismatchHelper stmts expected =
    case validate stmts of
        Ok (VState (VScopeState varMap iproofs _ _) _ _ _ _) ->
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
            [ Assign "x" (F (Val (builtinFunct Size)) [Val (VList [VInt 5])])
            ]
            [FApp eqVarProof [ATerm "x", CTerm (VInt 1)]]
        , validateWEMatchHelper
            [ Assign "x" (Val (VList [VInt 5, VInt 4]))
            , Assign "y" (F (Val (builtinFunct Size)) [Var "x"])
            ]
            [ FApp eqVarProof [ATerm "x", CTerm (VList [VInt 5, VInt 4])]
            , FApp eqVarProof [ATerm "y", CTerm (VInt 2)]
            ]
        , validateWEMatchHelper
            [ Assign "x" (F (Val (builtinFunct Size)) [Val (VList [VInt 5])])
            , Assign "y" (F (Val (builtinFunct Minus)) [Val (VInt 1), Val (VInt 1)])
            ]
            [ FApp eqVarProof [ATerm "x", CTerm (VInt 1)]
            , FApp eqVarProof [ATerm "y", CTerm (VInt 0)]
            ]
        , validateWEMatchHelper
            [ Assign "x" (Val (VInt 5))
            , ValidationStatement (ProofAssert (FApp eqVarProof [ATerm "x", CTerm (VInt 5)]))
            ]
            [FApp eqVarProof [ATerm "x", CTerm (VInt 5)]]
        , validateWEMatchHelper
            [ Assign "x" (Val (VInt 5))
            , ValidationStatement (Rewrite (UserRewrite "eqToLtPlus1" [ATerm "x"]))
            , ValidationStatement (ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 6)]))
            ]
            -- x < 6 is entailed (the ProofAssert above checks it) but no longer stored as a fact,
            -- since applying a rule does not copy every fact with refl
            [FApp eqVarProof [ATerm "x", CTerm (VInt 5)]]
        , validateWEMatchHelper
            [ Assign "x" (Val (VInt 5))
            , ValidationStatement (AssignProofVar "a" (Val (VInt 5)))
            , ValidationStatement (Rewrite (Refl (ATerm "x")))
            , ValidationStatement (ProofAssert (FApp eqVarProof [ATerm "x", ATerm "a"]))
            ]
            [ FApp eqVarProof [ATerm "x", CTerm (VInt 5)]
            , FApp eqVarProof [ATerm "a", CTerm (VInt 5)]
            , FApp eqVarProof [ATerm "x", ATerm "a"]
            , FApp eqVarProof [ATerm "a", ATerm "x"]
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
                    [Val (VList [VInt 5])]
                )
            ]
            [FApp eqVarProof [ATerm "y", CTerm (VInt 1)]]
        , validateWEMismatchHelper
            [ Assign "x" (Val (VList [VInt 5, VInt 4]))
            , Assign "y" (F (Val (builtinFunct Size)) [Var "x"])
            ]
            [ FApp eqVarProof [ATerm "x", CTerm (VList [VInt 5, VInt 4])]
            , FApp eqVarProof [ATerm "y", CTerm (VInt 2)]
            , FApp eqVarProof [ATerm "z", CTerm (VInt 2)]
            ]
        , validateWEMismatchHelper
            [ Assign
                "x"
                (Val (VInt 5))
            , ValidationStatement (AssignProofVar "a" (Val (VInt 5)))
            , ValidationStatement (Rewrite (Refl (ATerm "x")))
            , ValidationStatement (ProofAssert (FApp eqVarProof [ATerm "x", ATerm "a"]))
            ]
            [ FApp eqVarProof [ATerm "x", CTerm (VInt 5)]
            , FApp eqVarProof [ATerm "a", CTerm (VInt 5)]
            , FApp eqVarProof [ATerm "x", ATerm "a"]
            , FApp eqVarProof [ATerm "b", ATerm "x"]
            ]
        ]

testValidationFail :: Test
testValidationFail =
    testCaseSeq
        "testValidationFail"
        [ validationFailHelper [ValidationStatement (ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 5)]))]
        , validationFailHelper [Assign "x" (Val (VInt 5)), ValidationStatement (ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 4)]))]
        ]

testUserRewriteValidation :: Test
testUserRewriteValidation =
    testCaseSeq
        "testUserRewriteValidation"
        [ validateWEMatchHelper
            [ AxiomDef
                "five"
                ["x"]
                []
                [ProofAssert (FApp eqVarProof [ATerm "x", CTerm (VInt 5)])]
            , Assign "x" (Val (VInt 0))
            , ValidationStatement (Rewrite (UserRewrite "five" [ATerm "x"]))
            , ValidationStatement (ProofAssert (FApp eqVarProof [ATerm "x", CTerm (VInt 5)]))
            ]
            [FApp eqVarProof [ATerm "x", CTerm (VInt 5)]]
        , validateWEMatchHelper
            [ ProofDef
                "keepGt"
                ["x"]
                [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])]
                [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])]
                [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])]
            , Assign "x" (Val (VInt 5))
            , ValidationStatement (Rewrite (UserRewrite "eqToGtZero" [ATerm "x"]))
            , ValidationStatement (Rewrite (UserRewrite "keepGt" [ATerm "x"]))
            , ValidationStatement (ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)]))
            ]
            [FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)]]
        , validationFailHelper
            [ AxiomDef
                "guarded"
                ["x"]
                [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])]
                [ProofAssert (FApp eqVarProof [ATerm "x", CTerm (VInt 1)])]
            , Assign "x" (Val (VInt 0))
            , ValidationStatement (Rewrite (UserRewrite "guarded" [ATerm "x"]))
            ]
        , validationFailHelper
            [ Assign "x" (Val (VInt 0))
            , ValidationStatement (Rewrite (UserRewrite "eqToGtZero" [ATerm "x"]))
            ]
        , validationFailHelper
            [ ProofDef
                "badProof"
                ["x"]
                []
                [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])]
                [ProofAssert (FApp eqVarProof [ATerm "x", CTerm (VInt 0)])]
            ]
        , validationFailHelper
            [ AxiomDef "dupe" ["x"] [] [ProofAssert (FApp eqVarProof [ATerm "x", ATerm "x"])]
            , ProofDef "dupe" ["x"] [] [ProofAssert (FApp eqVarProof [ATerm "x", ATerm "x"])] [ProofAssert (FApp eqVarProof [ATerm "x", ATerm "x"])]
            ]
        , validationFailHelper [Assign "x" (Val (VInt 5)), ValidationStatement (Rewrite (UserRewrite "missing" [ATerm "x"]))]
        ]

-- Proof engine tests
testProofEngineInsertDedupes :: TestResult
testProofEngineInsertDedupes =
    let knownProof = FApp eqProof [ATerm (Iota "x"), CTerm (VInt 5)]
        context = Engine.insertProofs [knownProof, knownProof] Engine.emptyProofContext
     in testAssertEq (Engine.proofContextFacts context) [knownProof]

testProofEngineEntailsEquivalentTerms :: TestResult
testProofEngineEntailsEquivalentTerms =
    let iotaX = Iota "x"
        iotaA = Iota "a"
        context =
            Engine.proofContextFromFacts
                [ FApp eqProof [ATerm iotaX, ATerm iotaA]
                , FApp eqProof [ATerm iotaA, CTerm (VInt 5)]
                ]
        goal = FApp eqProof [ATerm iotaX, CTerm (VInt 5)]
     in testAssertTrue (Engine.entails goal context)

testProofEngineReflSubstitutesNestedTerms :: TestResult
testProofEngineReflSubstitutesNestedTerms =
    let iotaX = Iota "x"
        iotaA = Iota "a"
        context =
            Engine.proofContextFromFacts
                [ FApp eqProof [ATerm iotaA, CTerm (VInt 5)]
                , FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iotaX, ATerm iotaA]
                ]
        derived = Engine.deriveRefl context
        goal = FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iotaX, CTerm (VInt 5)]
     in testAssertTrue (Engine.entails goal derived)

testProofEngineEvalDerivesConcreteBuiltinResult :: TestResult
testProofEngineEvalDerivesConcreteBuiltinResult =
    let iotaList = Iota "list"
        iotaSize = Iota "size"
        context =
            Engine.proofContextFromFacts
                [ FApp eqProof [ATerm iotaList, CTerm (VList [VInt 1, VInt 2])]
                , FApp eqProof [ATerm iotaSize, FApp (CTerm (builtinFunct Size)) [ATerm iotaList]]
                ]
        result = Engine.applyRewrite evalBuiltinFunct (Engine.EngineEval iotaSize) context
        goal = FApp eqProof [ATerm iotaSize, CTerm (VInt 2)]
     in case result of
            Ok derived -> testAssertTrue (Engine.entails goal derived)
            Error e -> Just $ "Engine eval failed: " ++ e

-- Every iota in the clique equals every other, so an unmemoized equivalence walk is
-- exponential. The unrelated fact comes first so entailment must exhaust the clique's
-- equivalence class before reaching the fact that matches.
testProofEngineEntailsDenseEqualitiesTerminates :: TestResult
testProofEngineEntailsDenseEqualitiesTerminates =
    let firstIota = Iota "i1"
        secondIota = Iota "i2"
        iotas = firstIota : secondIota : map (Iota . ("i" ++) . show) [3 .. 8 :: Int]
        context =
            Engine.proofContextFromFacts
                ( FApp eqProof [ATerm (Iota "outsideA"), ATerm (Iota "outsideB")]
                    : [FApp eqProof [ATerm a, ATerm b] | a <- iotas, b <- iotas, a /= b]
                )
        related = FApp eqProof [ATerm firstIota, ATerm secondIota]
        unrelated = FApp eqProof [ATerm firstIota, ATerm (Iota "unrelated")]
     in testAssertEq (Engine.entails related context, Engine.entails unrelated context) (True, False)

-- Equal arguments give equal results without any fact having been rewritten (no refl):
-- size(q) = size(s) + 1, s = k and size(k) = l give size(q) = l + 1.
nestedCongruenceFacts :: [IotaProof]
nestedCongruenceFacts =
    let sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        plus a b = FApp (CTerm (builtinFunct Plus)) [a, b]
     in [ FApp eqProof [sizeOf (ATerm (Iota "q")), plus (sizeOf (ATerm (Iota "s"))) (CTerm (VInt 1))]
        , FApp eqProof [ATerm (Iota "s"), ATerm (Iota "k")]
        , FApp eqProof [sizeOf (ATerm (Iota "k")), ATerm (Iota "l")]
        , FApp eqProof [ATerm (Iota "d"), plus (ATerm (Iota "l")) (CTerm (VInt 1))]
        ]

testProofEngineEntailsNestedCongruence :: TestResult
testProofEngineEntailsNestedCongruence =
    let goal = FApp eqProof [FApp (CTerm (builtinFunct Size)) [ATerm (Iota "q")], ATerm (Iota "d")]
        ltGoal = FApp (CTerm (builtinFunct (Rel LtEq))) [FApp (CTerm (builtinFunct Size)) [ATerm (Iota "q")], ATerm (Iota "d")]
        context = Engine.proofContextFromFacts nestedCongruenceFacts
     in testAssertEq (Engine.entails goal context, Engine.entails ltGoal context) (True, True)

-- Dropping the link between s and k breaks the chain, so the goal is no longer entailed
testProofEngineEntailsNestedCongruenceNeedsEveryLink :: TestResult
testProofEngineEntailsNestedCongruenceNeedsEveryLink =
    let goal = FApp eqProof [FApp (CTerm (builtinFunct Size)) [ATerm (Iota "q")], ATerm (Iota "d")]
        context = Engine.proofContextFromFacts (filter (/= (nestedCongruenceFacts !! 1)) nestedCongruenceFacts)
     in testAssertEq (Engine.entails goal context) False

-- A relation that is a fact holds for terms equal to its arguments, and entailsAll answers each goal
testProofEngineEntailsRelationOfEqualTerms :: TestResult
testProofEngineEntailsRelationOfEqualTerms =
    let lt a b = FApp (CTerm (builtinFunct (Rel Lt))) [a, b]
        context =
            Engine.proofContextFromFacts
                [ lt (ATerm (Iota "x")) (ATerm (Iota "n"))
                , FApp eqProof [ATerm (Iota "x"), ATerm (Iota "y")]
                ]
        goals = [lt (ATerm (Iota "y")) (ATerm (Iota "n")), lt (ATerm (Iota "n")) (ATerm (Iota "y"))]
     in testAssertEq (Engine.entailsAll goals context) [True, False]

testProofEngine :: Test
testProofEngine =
    testCaseSeq
        "testProofEngine"
        [ testProofEngineInsertDedupes
        , testProofEngineEntailsDenseEqualitiesTerminates
        , testProofEngineEntailsEquivalentTerms
        , testProofEngineEntailsNestedCongruence
        , testProofEngineEntailsNestedCongruenceNeedsEveryLink
        , testProofEngineEntailsRelationOfEqualTerms
        , testProofEngineReflSubstitutesNestedTerms
        , testProofEngineEvalDerivesConcreteBuiltinResult
        ]

testIotaProofVarProofMatch :: Iota -> [IotaProof] -> Variable -> [VariableProof] -> TestResult
testIotaProofVarProofMatch i ip v vp =
    let varMap = Map.fromList [(v, i)]
     in case testAllTrue (\p -> expectedProofMatch p ip varMap) vp of
            Nothing -> Nothing
            Just e -> Just $ e ++ " had " ++ show ip

parseValReturningStmtHelper :: String -> Variable -> [VariableProof] -> TestResult
parseValReturningStmtHelper stmtStr expVar expected =
    let parseOutput = parseStatement stmtStr
     in case parseOutput of
            Left err -> Just $ "Parse failed: " ++ show err
            -- Just $ VScopeState (Data.Map.empty, [], emptyContinuations, Nothing)
            Right (Block stmts) -> doTrace3 (show stmts) $
                case valReturningBlock (initVStateWStatements stmts) of
                    Ok (VState (VScopeState _ proofs _ _) _ _ _ _, Just iota) -> testIotaProofVarProofMatch iota proofs expVar expected
                    Ok (_, Nothing) -> Just "No value returned"
                    Error e -> Just $ "Validation failed with error: " ++ e
            Right _ -> Just "Not a block statement"

parseValidateWEMatchHelper :: String -> [VariableProof] -> TestResult
parseValidateWEMatchHelper stmtStr expected =
    case parseStatement stmtStr of
        Left err -> Just $ "Parse failed: " ++ show err
        Right (Block stmts) -> validateWEMatchHelper stmts expected
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
        [FApp eqVarProof [ATerm "ret", CTerm (VInt 3)]]

testParseValWFunctDef :: TestResult
testParseValWFunctDef =
    parseValReturningStmtHelper
        "{\
        \  x = 6;\
        \  fn add1(i: Int) -> Int {\
        \    return i + 1;\
        \  };\
        \  return add1;\
        \}"
        "ret"
        [ FApp
            eqVarProof
            [ ATerm "ret"
            , CTerm
                ( VFunct
                    ["i"]
                    []
                    []
                    (nativeInts 1 [Return (F (Val (builtinFunct Plus)) [Var "i", Val (VInt 1)])])
                    [FApp eqVarProof [ATerm "return", FApp (CTerm (builtinFunct Plus)) [ATerm "i", CTerm (VInt 1)]]]
                )
            ]
        ]

testParseValFunctWInputStatements :: TestResult
testParseValFunctWInputStatements =
    parseValReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  return first(x);\
        \}"
        "ret"
        [FApp eqVarProof [ATerm "ret", CTerm (VInt 3)]]

testParseValLastWInputStatements :: TestResult
testParseValLastWInputStatements =
    parseValReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  return last(x);\
        \}"
        "ret"
        [FApp eqVarProof [ATerm "ret", CTerm (VInt 12)]]

testParseValWUdfCall :: TestResult
testParseValWUdfCall =
    parseValReturningStmtHelper
        "{\
        \  fn sumFirstLast(lst: List<Int>) -> Int [{\
        \    define s = size(lst);\
        \    rewrite eqToGtZero s;\
        \    affirm s > 0;\
        \  }] {\
        \    return first(lst) + last(lst);\
        \  };\
        \  x = [3, 6, 9, 12];\
        \  return sumFirstLast(x);\
        \}"
        "ret"
        [FApp eqVarProof [ATerm "ret", CTerm (VInt 15)]]

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
        [FApp eqVarProof [ATerm "ret", CTerm (VInt 1)]]

testParseValFunctReturnNestedBlocks :: TestResult
testParseValFunctReturnNestedBlocks =
    parseValReturningStmtHelper
        "{\
        \  x = [3, 6, 9, 12];\
        \  fn getFirst(y: Int) -> Int [{\
        \    define s = size(y);\
        \    rewrite eqToGtZero s;\
        \    affirm s > 0;\
        \  }] {\
        \    x = [1];\
        \    {\
        \      return first(y);\
        \    };\
        \    return first(x);\
        \  };\
        \  return getFirst(x);\
        \}"
        "ret"
        [FApp eqVarProof [ATerm "ret", CTerm (VInt 3)]]

testParseValFunctWOutputStatements :: TestResult
testParseValFunctWOutputStatements =
    parseValidateWEMatchHelper
        "{\
        \  fn add1(i: Int) -> Int [{}] [{\
        \    affirm return = (i + 1);\
        \  }] {\
        \    return i + 1;\
        \  };\
        \  x = add1(4);\
        \  affirm x = 5;\
        \}"
        [FApp eqVarProof [ATerm "x", CTerm (VInt 5)]]

testParseValFunctExportsProofVar :: TestResult
testParseValFunctExportsProofVar =
    parseValidateWEMatchHelper
        "{\
        \  fn getFirstWithSize(lst: List<Int>) -> Int [{\
        \    define s = size(lst);\
        \    rewrite eqToGtZero s;\
        \    affirm s > 0;\
        \  }] [{\
        \    affirm s > 0;\
        \  }] {\
        \    return first(lst);\
        \  };\
        \  x = [3, 6, 9, 12];\
        \  y = getFirstWithSize(x);\
        \  affirm s > 0;\
        \}"
        [ FApp eqVarProof [ATerm "y", CTerm (VInt 3)]
        , FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "s", CTerm (VInt 0)]
        ]

testParseVal :: Test
testParseVal =
    testCaseSeq
        "testParseVal"
        [ testParseValBlockExpr
        , testParseValWFunctDef
        , testParseValFunctWInputStatements
        , testParseValLastWInputStatements
        , testParseValWUdfCall
        , testValidateNestedBlocks
        , testParseValFunctReturnNestedBlocks
        , testParseValFunctWOutputStatements
        , testParseValFunctExportsProofVar
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

parseEvalFailStmtHelper :: String -> String -> TestResult
parseEvalFailStmtHelper stmtStr expectedError =
    case parseStatement stmtStr of
        Left err -> Just $ "Parse failed: " ++ show err
        Right (Block stmts) ->
            testAssertErrorContains
                expectedError
                (evalReturningBlock (setPScope (initStateWStatements stmts) (Just emptyScopeState)))
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

testParseValFunctBodyValidationFail :: TestResult
testParseValFunctBodyValidationFail =
    parseValFailStmtHelper
        "{\
        \  fn bad(lst: List<Int>) -> Int [{\
        \    define s = size(lst);\
        \    rewrite eqToGtZero s;\
        \    affirm s > 0;\
        \  }] {\
        \    x = [];\
        \    return first(x);\
        \  };\
        \}"

testParseValLastEmptyValidationFail :: TestResult
testParseValLastEmptyValidationFail =
    parseValFailStmtHelper
        "{\
        \  x = [];\
        \  return last(x);\
        \}"

testParseValFirstEmptyValidationFail :: TestResult
testParseValFirstEmptyValidationFail =
    parseValFailStmtHelper
        "{\
        \  x = [];\
        \  return first(x);\
        \}"

testParseValFunctOutputValidationFail :: TestResult
testParseValFunctOutputValidationFail =
    parseValFailStmtHelper
        "{\
        \  fn bad(i: Int) -> Int [{}] [{\
        \    affirm return = i;\
        \  }] {\
        \    return i + 1;\
        \  };\
        \}"

testParseValMissingExportedProofValidationFail :: TestResult
testParseValMissingExportedProofValidationFail =
    parseValFailStmtHelper
        "{\
        \  fn bad(lst: List<Int>) -> Int [{\
        \    define s = size(lst);\
        \    rewrite eqToGtZero s;\
        \    affirm s > 0;\
        \  }] [{\
        \    affirm missing > 0;\
        \  }] {\
        \    return first(lst);\
        \  };\
        \}"

testParseEvalFirstEmptyFail :: TestResult
testParseEvalFirstEmptyFail =
    parseEvalFailStmtHelper
        "{\
        \  return first([]);\
        \}"
        "First requires a non-empty list"

testParseEvalLastEmptyFail :: TestResult
testParseEvalLastEmptyFail =
    parseEvalFailStmtHelper
        "{\
        \  return last([]);\
        \}"
        "Last requires a non-empty list"

testParseEvalFirstWrongTypeFail :: TestResult
testParseEvalFirstWrongTypeFail =
    parseEvalFailStmtHelper
        "{\
        \  return first(1);\
        \}"
        "First only valid for a list"

-- The LANGUAGE.md "Argument Passing" example: the callee's reassignment of a parameter
-- must not reach the caller's variable, in evaluation or after validation.
argPassingSource :: String
argPassingSource =
    "fn reset(xs: List<Int>) -> Int { xs = []; return size(xs); };\
    \xs = [1, 2, 3];\
    \n = reset(xs);\
    \return size(xs) - n;"

testArgPassingByValue :: TestResult
testArgPassingByValue =
    case parseStatementBlock argPassingSource of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts ->
            case (valReturningBlock (initVStateWStatements stmts), evalReturningBlock (initStateWStatements stmts)) of
                (Error e, _) -> Just $ "Validation failed with error: " ++ e
                (_, Error e) -> Just $ "Evaluation failed with error: " ++ e
                (Ok _, Ok (_, ret)) -> testAssertEq ret (Just (VInt 3))

testParseEvalUdfExtraArgsFail :: TestResult
testParseEvalUdfExtraArgsFail =
    parseEvalFailStmtHelper
        "{\
        \  fn f(a: List<Int>) -> List<Int> { return a; };\
        \  return f(1, 2);\
        \}"
        "expected 1 arguments, got 2"

testParseEvalUdfMissingArgsFail :: TestResult
testParseEvalUdfMissingArgsFail =
    parseEvalFailStmtHelper
        "{\
        \  fn f(a: Int, b: Int) -> Int { return a; };\
        \  return f(1);\
        \}"
        "expected 2 arguments, got 1"

testParseValUdfExtraArgsFail :: TestResult
testParseValUdfExtraArgsFail =
    parseValFailStmtHelper
        "{\
        \  fn f(a: List<Int>) -> List<Int> { return a; };\
        \  return f(1, 2);\
        \}"

testParseValUdfMissingArgsFail :: TestResult
testParseValUdfMissingArgsFail =
    parseValFailStmtHelper
        "{\
        \  fn f(a: Int, b: Int) -> Int { return a; };\
        \  return f(1);\
        \}"

testParseValBuiltinExtraArgsFail :: TestResult
testParseValBuiltinExtraArgsFail =
    parseValFailStmtHelper
        "{\
        \  return size([1], [2]);\
        \}"

testCrashRegression :: Test
testCrashRegression =
    testCaseSeq
        "testCrashRegression"
        [ testParseEvalFirstEmptyFail
        , testParseEvalLastEmptyFail
        , testParseEvalFirstWrongTypeFail
        , testArgPassingByValue
        , testParseEvalUdfExtraArgsFail
        , testParseEvalUdfMissingArgsFail
        , testParseValUdfExtraArgsFail
        , testParseValUdfMissingArgsFail
        , testParseValBuiltinExtraArgsFail
        ]

testParseValFail :: Test
testParseValFail =
    testCaseSeq
        "testParseValFail"
        [ testParseValAffirmFail
        , testParseValAffirmParensFail
        , testParseValFunctBodyValidationFail
        , testParseValFunctOutputValidationFail
        , testParseValLastEmptyValidationFail
        , testParseValFirstEmptyValidationFail
        , testParseValMissingExportedProofValidationFail
        ]

-- Example program tests
-- Programs in examples/ must keep behaving as documented in examples/README.md.
-- Paths are relative to the package root, which is where `stack test` runs.
data ExampleExpectation
    = -- Validates, evaluates, and returns this value
      ExpectReturn Value
    | -- Validates and evaluates without a return value
      ExpectValid
    | -- Validation fails with an error containing this text
      ExpectRejected String

testExampleFile :: FilePath -> ExampleExpectation -> Test
testExampleFile path expectation = TestCase path $ do
    source <- readFile path
    pure $ case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> checkExample stmts expectation

checkExample :: [Statement] -> ExampleExpectation -> TestResult
checkExample stmts (ExpectRejected expectedError) =
    testAssertErrorContains expectedError (validate stmts)
checkExample stmts expectation =
    case validate stmts of
        Error e -> Just $ "Validation failed with error: " ++ e
        Ok _ -> case evaluate stmts of
            Error e -> Just $ "Evaluation failed with error: " ++ e
            Ok state -> case expectation of
                ExpectReturn expected -> testAssertEq (getReturn state) (Just expected)
                _ -> testAssertEq (getReturn state) Nothing

testExamples :: Test
testExamples =
    TestList
        "testExamples"
        [ testExampleFile "examples/basics.tersus" (ExpectReturn (VInt 6))
        , testExampleFile "examples/functions.tersus" (ExpectReturn (VInt 21))
        , testExampleFile "examples/booleans.tersus" (ExpectReturn (VBool True))
        , testExampleFile "examples/proofs.tersus" ExpectValid
        , testExampleFile "examples/rewrites.tersus" ExpectValid
        , testExampleFile "examples/safe_access.tersus" (ExpectReturn (VInt 38))
        , testExampleFile "examples/contracts.tersus" (ExpectReturn (VInt 8))
        , testExampleFile "examples/rules.tersus" ExpectValid
        , testExampleFile "examples/branching.tersus" (ExpectReturn (VInt 106))
        , testExampleFile "examples/arithmetic.tersus" (ExpectReturn (VInt 6))
        , testExampleFile "examples/types.tersus" (ExpectReturn (VInt 6))
        , testExampleFile "examples/structs.tersus" (ExpectReturn (VInt 11))
        , testExampleFile "examples/linked_list.tersus" (ExpectReturn (VInt 9))
        , testExampleFile "examples/enums.tersus" (ExpectReturn (VInt 27))
        , testExampleFile "examples/generic_lists.tersus" (ExpectReturn (VList [VList [VInt 1, VInt 2], VList [VInt 3, VInt 4], VList [VInt 1, VInt 2]]))
        , testExampleFile "examples/helper_functions.tersus" (ExpectReturn (VInt 11))
        , testExampleFile "examples/recursion.tersus" (ExpectReturn (VInt 26))
        , testExampleFile "examples/termination.tersus" (ExpectReturn (VInt 23))
        , testExampleFile "examples/for_loops.tersus" (ExpectReturn (VInt 25))
        , testExampleFile "examples/loops.tersus" (ExpectReturn (VInt 30))
        , testExampleFile "examples/early_return.tersus" (ExpectReturn (VInt 104))
        , testExampleFile "examples/loop_return.tersus" (ExpectReturn (VInt 7))
        , testExampleFile "examples/parallel_sum.tersus" (ExpectReturn (VList [VInt 11, VInt 22, VInt 33]))
        , testExampleFile "examples/build_list.tersus" (ExpectReturn (VList [VInt 2, VInt 4, VInt 6]))
        , testExampleFile "examples/update_list.tersus" (ExpectReturn (VList [VInt 101, VInt 102, VInt 103]))
        , testExampleFile "examples/element_facts.tersus" (ExpectReturn (VInt 106))
        , testExampleFile "examples/frame_facts.tersus" (ExpectReturn (VInt 149))
        , testExampleFile "examples/forall_facts.tersus" (ExpectReturn (VInt 5))
        , testExampleFile "examples/rejected/forall_wrong_element.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/forall_invariant_gap.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/forall_unproven.tersus" (ExpectRejected "input validation failed")
        , testExampleFile "examples/rejected/frame_changed_index.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/get_out_of_range.tersus" (ExpectRejected "Relation does not hold")
        , testExampleFile "examples/rejected/get_unproven_index.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/parallel_length.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/call_violates_contract.tersus" (ExpectRejected "Could not prove: n > 0")
        , testExampleFile "examples/rejected/recursion_wrong_contract.tersus" (ExpectRejected "Could not prove: return = 0")
        , testExampleFile "examples/rejected/recursion_input.tersus" (ExpectRejected "Could not prove: n > 0")
        , testExampleFile "examples/rejected/type_return_mismatch.tersus" (ExpectRejected "returned value: expected Int, got List<Int>")
        , testExampleFile "examples/rejected/type_argument_mismatch.tersus" (ExpectRejected "argument 1 of size")
        , testExampleFile "examples/rejected/list_element_mismatch.tersus" (ExpectRejected "argument 2 of push: expected Bool, got Int")
        , testExampleFile "examples/rejected/struct_update_frame.tersus" (ExpectRejected "Could not prove: return.y = p.x")
        , testExampleFile "examples/rejected/struct_field_type.tersus" (ExpectRejected "field value of Node: expected Int, got Bool")
        , testExampleFile "examples/rejected/enum_contract_unmet.tersus" (ExpectRejected "Could not prove: s is Shape::Circle")
        , testExampleFile "examples/rejected/enum_wrong_variant.tersus" (ExpectRejected "Could not prove: s is Shape::Rect")
        , testExampleFile "examples/rejected/linked_list_link_out_of_range.tersus" (ExpectRejected "Could not prove: forall i in 0..size(return): get(return, i).next < size(return)")
        , testExampleFile "examples/rejected/linked_list_link_disagrees.tersus" (ExpectRejected "Could not prove: forall i in 0..size(return): get(return, get(return, i).next).prev = i")
        , testExampleFile "examples/rejected/for_reads_past_end.tersus" (ExpectRejected "Funct input validation failed")
        , testExampleFile "examples/rejected/for_assigns_counter.tersus" (ExpectRejected "Loop invariant is not preserved: Could not prove: i <= (end of for i)")
        , testExampleFile "examples/rejected/loop_without_termination.tersus" (ExpectRejected "Loop must say how it ends")
        , testExampleFile "examples/rejected/loop_variant_not_shrinking.tersus" (ExpectRejected "Loop variant does not shrink: 3 - i")
        , testExampleFile "examples/rejected/loop_variant_unbounded.tersus" (ExpectRejected "Loop variant is not bounded below: i")
        , testExampleFile "examples/rejected/recursion_without_variant.tersus" (ExpectRejected "Not guaranteed to terminate: it calls itself")
        , testExampleFile "examples/rejected/recursion_variant_not_shrinking.tersus" (ExpectRejected "Recursive call does not shrink the variant: n")
        , testExampleFile "examples/rejected/recursion_shrinks_not_a_part.tersus" (ExpectRejected "Recursive call does not shrink the variant: t")
        , testExampleFile "examples/rejected/diverging_call.tersus" (ExpectRejected "it calls a function that is declared ~")
        , testExampleFile "examples/rejected/diverging_loop.tersus" (ExpectRejected "a loop is declared ~")
        , testExampleFile "examples/rejected/linked_list_unchecked_walk.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/call_before_definition.tersus" (ExpectRejected "Undefined variable: later")
        , testExampleFile "examples/rejected/division_by_zero.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/push_size.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/set_out_of_range.tersus" (ExpectRejected "Relation does not hold")
        , testExampleFile "examples/rejected/set_size.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/element_wrong.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/invariant_entry.tersus" (ExpectRejected "Loop invariant does not hold on entry")
        , testExampleFile "examples/rejected/invariant_preserved.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/loop_stale_fact.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/loop_return_invariant.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/loop_missing_return.tersus" (ExpectRejected "Return value not found")
        , testExampleFile "examples/rejected/unguarded_access.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/branch_fact.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/guard_condition.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/missing_return.tersus" (ExpectRejected "Return value not found")
        , testExampleFile "examples/rejected/affirm.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/first_of_empty.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/unmet_contract.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/missing_contract.tersus" (ExpectRejected "Could not prove: size(list) > 0")
        , testExampleFile "examples/rejected/output_contract.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/bad_proof_rule.tersus" (ExpectRejected "Could not prove")
        , testExampleFile "examples/rejected/axiom_input.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/unknown_rule.tersus" (ExpectRejected "Unknown rewrite rule")
        ]

-- CLI tests
testCliParseCommandLine :: TestResult
testCliParseCommandLine =
    testAssertEq
        (map parseCommandLine [["check", "a.tersus"], ["run", "-"], ["run"], ["frob", "a.tersus"], []])
        [Just (Check, "a.tersus"), Just (Run, "-"), Nothing, Nothing, Nothing]

testCliRenderValue :: TestResult
testCliRenderValue =
    testAssertEq
        (map renderValue [VInt 5, VList [], VList [VInt 1, VInt 2], VBool True, VBool False])
        ["5", "[]", "[1, 2]", "true", "false"]

testCliRun :: TestResult
testCliRun =
    testAssertEq
        (map (runSource Run) ["x = [1, 2]; return size(x);", "return [3, 4];", "return 1 < 2;", "x = 5; affirm x = 5;", ""])
        [Ok "2", Ok "[3, 4]", Ok "true", Ok "", Ok ""]

testCliCheck :: TestResult
testCliCheck = testAssertEq (runSource Check "x = 5; affirm x = 5; return x;") (Ok "OK")

testCli :: Test
testCli =
    testCaseSeq
        "testCli"
        [ testCliParseCommandLine
        , testCliRenderValue
        , testCliRun
        , testCliCheck
        , testAssertErrorContains "Parse error" (runSource Run "x = ;")
        , testAssertErrorContains "Validation failed" (runSource Run "x = 5; affirm x < 4;")
        , testAssertErrorContains "Validation failed" (runSource Check "x = 5; affirm x < 4;")
        , -- Validation must reject the program before it is evaluated
          testAssertErrorContains "Validation failed" (runSource Run "return first([]);")
        ]

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
            Ok _ -> Nothing
            Error e -> Just $ "Validation failed with error: " ++ e

parseValidateFailProgramHelper :: String -> String -> TestResult
parseValidateFailProgramHelper source expectedError =
    case parseStatementBlock source of
        Left err -> Just $ "Parse failed: " ++ show err
        Right stmts -> testAssertErrorContains expectedError (validate stmts)

testParseIf :: Test
testParseIf =
    let lt1 = F (Val (builtinFunct (Rel Lt))) [Var "x", Val (VInt 1)]
        setY n = Assign "y" (Val (VInt n))
     in testCaseSeq
            "testParseIf"
            [ case parseStatementBlock "if x < 1 { y = 1; } else { y = 2; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [If lt1 [setY 1] [setY 2]]
            , case parseStatementBlock "if x < 1 { y = 1; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [If lt1 [setY 1] []]
            , case parseStatementBlock "if x < 1 { y = 1; } else if x < 2 { y = 2; } else { y = 3; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed ->
                    testAssertEq
                        parsed
                        [If lt1 [setY 1] [If (F (Val (builtinFunct (Rel Lt))) [Var "x", Val (VInt 2)]) [setY 2] [setY 3]]]
            , case parseStatementBlock "if x < 1 { y = 1; } // done\n// otherwise\nelse { y = 2; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [If lt1 [setY 1] [setY 2]]
            , -- Keywords are only reserved as whole words
              case parseStatementBlock "iffy = 1; elsewhere = 2;" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [Assign "iffy" (Val (VInt 1)), Assign "elsewhere" (Val (VInt 2))]
            ]

testEvalIf :: Test
testEvalIf =
    testCaseSeq
        "testEvalIf"
        [ parseEvalProgramHelper "x = 5; y = 0; if x < 9 { y = 1; } else { y = 2; }; return y;" (Just (VInt 1))
        , parseEvalProgramHelper "x = 5; y = 0; if x > 9 { y = 1; } else { y = 2; }; return y;" (Just (VInt 2))
        , parseEvalProgramHelper "x = 5; y = 7; if x > 9 { y = 1; }; return y;" (Just (VInt 7))
        , parseEvalProgramHelper "x = 5; y = 0; if x < 4 { y = 1; } else if x < 9 { y = 2; } else { y = 3; }; return y;" (Just (VInt 2))
        , parseEvalProgramHelper "x = 5; y = 0; if x < 9 { if x < 3 { y = 1; } else { y = 2; }; }; return y;" (Just (VInt 2))
        , parseEvalProgramHelper "b = 1 < 2; y = 0; if b { y = 4; }; return y;" (Just (VInt 4))
        , parseEvalProgramFailHelper "if 5 { x = 1; };" "Condition must be a boolean"
        , -- A variable first assigned in a branch is local to it
          parseEvalProgramFailHelper "if true { t = 1; }; return t;" "Undefined variable: t"
        ]

testValidateIf :: Test
testValidateIf =
    testCaseSeq
        "testValidateIf"
        [ -- Guarding first() with the list size makes it safe for a list only known at runtime
          parseValidProgramHelper
            "fn firstOr(lst: List<Int>, d: Int) -> Int {\
            \  r = d;\
            \  if size(lst) > 0 {\
            \    define s = size(lst);\
            \    rewrite eqToGtZero s;\
            \    r = first(lst);\
            \  };\
            \  return r;\
            \};\
            \return firstOr([4, 8], 0);"
        , -- A fact both branches establish about the assigned variable survives the join
          parseValidProgramHelper
            "fn f(n: Int) -> Int {\
            \  y = 0;\
            \  if n < 6 { y = 1; rewrite eqToGtZero y; } else { y = 2; rewrite eqToGtZero y; };\
            \  affirm y > 0;\
            \  return y;\
            \};"
        , -- The same guard without enough information is rejected
          parseValidateFailProgramHelper
            "fn firstOr(lst: List<Int>, d: Int) -> Int {\
            \  r = d;\
            \  if size(lst) >= 0 {\
            \    r = first(lst);\
            \  };\
            \  return r;\
            \};\
            \return firstOr([4, 8], 0);"
            "Could not prove: size(list) > 0"
        , -- A fact only one branch establishes does not survive the join
          parseValidateFailProgramHelper
            "fn f(n: Int) -> Int {\
            \  y = 0;\
            \  if n < 6 { y = 1; rewrite eqToGtZero y; } else { y = 0 - 1; };\
            \  affirm y > 0;\
            \};"
            "Could not prove"
        , -- Soundness: the condition only holds inside its branch
          parseValidateFailProgramHelper
            "fn f(n: Int) -> Int {\
            \  y = 0;\
            \  if n < 6 { y = 1; } else { y = 2; };\
            \  affirm n < 6;\
            \};"
            "Could not prove"
        , -- Soundness: a copy made under the condition must not carry the condition out
          parseValidateFailProgramHelper
            "fn f(n: Int) -> Int {\
            \  y = 0;\
            \  if n < 6 { y = n; } else { y = 9; };\
            \  affirm y < 6;\
            \};"
            "Could not prove"
        ]

testParseWhile :: Test
testParseWhile =
    let lt3 = F (Val (builtinFunct (Rel Lt))) [Var "i", Val (VInt 3)]
        inc = Assign "i" (F (Val (builtinFunct Plus)) [Var "i", Val (VInt 1)])
        leProof = ProofAssert (FApp (CTerm (builtinFunct (Rel LtEq))) [ATerm "i", CTerm (VInt 3)])
     in testCaseSeq
            "testParseWhile"
            [ case parseStatementBlock "while i < 3 { i = i + 1; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [While lt3 [] Nothing [inc]]
            , case parseStatementBlock "while i < 3 [{ affirm i <= 3; }] { i = i + 1; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [While lt3 [leProof] Nothing [inc]]
            , -- The condition may call functions, and the invariant may hold several statements
              case parseStatementBlock "while size(xs) > 0 [{ define s = size(xs); affirm s > 0; }] { xs = [1]; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right [While _ inv _ _] -> testAssertEq (length inv) 2
                Right parsed -> Just $ "Unexpected parse: " ++ show parsed
            , case parseStatementBlock "whiley = 1;" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [Assign "whiley" (Val (VInt 1))]
            ]

testEvalWhile :: Test
testEvalWhile =
    testCaseSeq
        "testEvalWhile"
        [ parseEvalProgramHelper "i = 0; n = 0; while i < 3 { i = i + 1; n = n + 2; }; return n;" (Just (VInt 6))
        , -- The body never runs
          parseEvalProgramHelper "i = 5; while i < 3 { i = i + 1; }; return i;" (Just (VInt 5))
        , parseEvalProgramHelper "i = 0; n = 0; while i < 4 { if i < 2 { n = n + 10; } else { n = n + 1; }; i = i + 1; }; return n;" (Just (VInt 22))
        , parseEvalProgramHelper "i = 0; while i < 2 { j = 0; while j < 2 { i = i + 1; j = j + 1; }; }; return i;" (Just (VInt 2))
        , -- The invariant is only used by validation
          parseEvalProgramHelper "i = 0; while i < 3 [{ affirm i <= 3; }] { i = i + 1; }; return i;" (Just (VInt 3))
        , parseEvalProgramFailHelper "while 5 { x = 1; };" "Condition must be a boolean"
        ]

-- The validator does no arithmetic, so these two trusted axioms supply the arithmetic facts
loopAxioms :: String
loopAxioms =
    "axiom zeroWithinBound(i) [{ affirm i = 0; }] [{ affirm i <= 3; }];\
    \axiom stepWithinBound(i) [{ affirm i < 3; }] [{ affirm (i + 1) <= 3; }];"

testValidateWhile :: Test
testValidateWhile =
    testCaseSeq
        "testValidateWhile"
        [ -- The invariant holds on entry, is preserved, and with the negated condition gives i >= 3
          parseValidProgramHelper
            ( loopAxioms
                ++ "i = 0; rewrite zeroWithinBound i;\
                   \while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { rewrite stepWithinBound i; i = i + 1; };\
                   \affirm i <= 3; affirm i >= 3;"
            )
        , -- Without an invariant the loop still validates, it just proves nothing about i afterwards
          parseValidProgramHelper "i = 0; n = 0; while i < 3 shrinks 3 - i { i = i + 1; n = n + 2; };"
        , -- A loop nested in a function body
          parseValidProgramHelper
            ( loopAxioms
                ++ "fn f(k: Int) -> Int { i = 0; rewrite zeroWithinBound i;\
                   \  while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { rewrite stepWithinBound i; i = i + 1; };\
                   \  return i; };\
                   \return f(1);"
            )
        , parseValidateFailProgramHelper
            ( loopAxioms
                ++ "i = 5; while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { rewrite stepWithinBound i; i = i + 1; };"
            )
            "Loop invariant does not hold on entry"
        , parseValidateFailProgramHelper
            ( loopAxioms
                ++ "i = 0; rewrite zeroWithinBound i; while i < 3 [{ affirm i <= 2; }] shrinks 3 - i { i = i + 1; };"
            )
            "Loop invariant is not preserved"
        , -- Soundness: what was known about i before the loop says nothing about i after it
          parseValidateFailProgramHelper "i = 0; while i < 3 shrinks 3 - i { i = i + 1; }; affirm i = 0;" "Could not prove"
        , -- Soundness: the loop condition does not hold once the loop is done
          parseValidateFailProgramHelper
            ( loopAxioms
                ++ "i = 0; rewrite zeroWithinBound i;\
                   \while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { rewrite stepWithinBound i; i = i + 1; };\
                   \affirm i < 3;"
            )
            "Could not prove"
        , -- A loop whose body returns is validated too
          parseValidProgramHelper "i = 0; while i < 3 shrinks 3 - i { return i; }; return 9;"
        ]

testEarlyReturn :: Test
testEarlyReturn =
    testCaseSeq
        "testEarlyReturn"
        [ -- Evaluation: return ends the program or function where it runs
          parseEvalProgramHelper "return 1; return 2;" (Just (VInt 1))
        , parseEvalProgramHelper "x = 5; if x < 9 { return 1; }; return 2;" (Just (VInt 1))
        , parseEvalProgramHelper "x = 5; if x > 9 { return 1; }; return 2;" (Just (VInt 2))
        , parseEvalProgramHelper "x = 1; { x = 2; return x; }; return 9;" (Just (VInt 2))
        , parseEvalProgramHelper "x = 1; if x < 2 { if x < 3 { return 7; }; }; return 9;" (Just (VInt 7))
        , parseEvalProgramHelper
            "fn f(n: Int) -> Int { if n < 1 { return 0; }; return n + 10; }; return f(0) + f(5);"
            (Just (VInt 15))
        , -- Returning from inside a loop stops the loop
          parseEvalProgramHelper "i = 0; while i < 10 shrinks 10 - i { if i > 2 { return i; }; i = i + 1; }; return 99;" (Just (VInt 3))
        , -- Statements after the return never run
          parseEvalProgramHelper "return 1; x = first([]);" (Just (VInt 1))
        , -- Validation: a guard clause makes the rest of the function safe
          parseValidProgramHelper
            "fn firstOr(lst: List<Int>, d: Int) -> Int { if size(lst) > 0 { } else { return d; }; define s = size(lst); rewrite eqToGtZero s; return first(lst); }; return firstOr([4, 8], 0) + firstOr([], 5);"
        , -- A return inside the taken branch
          parseValidProgramHelper
            "fn firstOr(lst: List<Int>, d: Int) -> Int { if size(lst) > 0 { define s = size(lst); rewrite eqToGtZero s; return first(lst); }; return d; };"
        , -- A chain of guard clauses
          parseValidProgramHelper
            "fn sign(n: Int) -> Int { if n < 0 { return 0 - 1; }; if n > 0 { return 1; }; return 0; }; return sign(3);"
        , -- A program may return on only some paths
          parseValidProgramHelper "x = 1; if x < 2 { return 1; };"
        , -- Every return can establish an output fact
          parseValidProgramHelper
            "fn f(n: Int) -> Int [{ }] [{ affirm return > 0; }] { if n < 6 { y = 1; rewrite eqToGtZero y; return y; }; z = 2; rewrite eqToGtZero z; return z; }; r = f(3); affirm r > 0;"
        , -- Rejected: the guard only helps on the path where it did not return
          parseValidateFailProgramHelper
            "fn f(lst: List<Int>, d: Int) -> Int { if size(lst) > 0 { return d; }; return first(lst); };"
            "Could not prove: size(list) > 0"
        , parseValidateFailProgramHelper
            "fn f(lst: List<Int>, d: Int) -> Int { if size(lst) < 5 { } else { return d; }; return first(lst); };"
            "Could not prove: size(list) > 0"
        , -- Soundness: the return branch's condition is not known afterwards
          parseValidateFailProgramHelper
            "fn f(n: Int) -> Int { if n < 6 { return 1; }; affirm n < 6; return 2; };"
            "Could not prove"
        , -- Soundness: a fact only one return establishes is not an output fact
          parseValidateFailProgramHelper
            "fn f(n: Int) -> Int [{ }] [{ affirm return > 0; }] { if n < 6 { y = 1; rewrite eqToGtZero y; return y; }; return 0; };"
            "Could not prove"
        , -- A function where some path does not return has no return value
          parseValidateFailProgramHelper "fn f(n: Int) -> Int { if n < 6 { return 1; }; }; x = f(1);" "Return value not found"
        , -- Returning from inside a loop stops it
          parseValidProgramHelper "fn f(n: Int) -> Int { i = 0; while i < 3 shrinks 3 - i { if i > n { return i; }; i = i + 1; }; return 0; }; x = f(1);"
        , parseEvalProgramHelper "fn f(n: Int) -> Int { i = 0; while i < 5 shrinks 5 - i { if i > n { return i; }; i = i + 1; }; return 0; }; return f(2) + f(9);" (Just (VInt 3))
        , -- The invariant is checked on the paths that keep looping, and holds for the return too
          parseValidProgramHelper
            ( loopAxioms
                ++ "fn f(n: Int) -> Int [{ }] [{ affirm return <= 3; }] { i = 0; rewrite zeroWithinBound i;\
                   \ while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { if i > n { return i; }; rewrite stepWithinBound i; i = i + 1; };\
                   \ affirm i >= 3; return i; }; x = f(1);"
            )
        , parseValidateFailProgramHelper
            ( loopAxioms
                ++ "fn f(n: Int) -> Int { i = 0; rewrite zeroWithinBound i;\
                   \ while i < 3 [{ affirm i <= 2; }] shrinks 3 - i { if i > n { return i; }; i = i + 1; };\
                   \ return i; };"
            )
            "Loop invariant is not preserved"
        , -- Soundness: the returning path's condition is not known after the loop
          parseValidateFailProgramHelper
            "fn f(n: Int) -> Int { i = 0; while i < 3 shrinks 3 - i { if n > 5 { return 1; }; i = i + 1; }; affirm n > 5; return 0; };"
            "Could not prove"
        , -- Soundness: only the path after the loop knows the loop condition is false
          parseValidateFailProgramHelper
            "fn f(n: Int) -> Int { i = 0; while i < 3 shrinks 3 - i { if n > 5 { return 1; }; i = i + 1; }; affirm i < 3; return 0; };"
            "Could not prove"
        , -- Soundness: a fact only the returning path establishes is not an output fact
          parseValidateFailProgramHelper
            ( loopAxioms
                ++ "fn f(n: Int) -> Int [{ }] [{ affirm return <= 3; }] { i = 0; rewrite zeroWithinBound i;\
                   \ while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { if i > n { return i; }; rewrite stepWithinBound i; i = i + 1; };\
                   \ return 100; };"
            )
            "Could not prove"
        , parseValidateFailProgramHelper "fn f(n: Int) -> Int { i = 0; while i < n shrinks n - i { return i; }; }; x = f(1);" "Return value not found"
        , -- A nested loop that returns
          parseValidProgramHelper
            "fn f(n: Int) -> Int { i = 0; while i < 2 shrinks 2 - i { j = 0; while j < 2 shrinks 2 - j { if j > n { return j; }; j = j + 1; }; i = i + 1; }; return 0; }; x = f(1);"
        ]

testArithmetic :: Test
testArithmetic =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        plus a b = FApp (CTerm (builtinFunct Plus)) [a, b]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        iota = ATerm . Iota
        int = CTerm . VInt
        ctx = Engine.proofContextFromFacts
        engine facts goal = testAssertTrue (Engine.entails goal (ctx facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (ctx facts)))
     in testCaseSeq
            "testArithmetic"
            [ -- Engine: relations follow from known values and from x + c
              engine [FApp eqProof [iota "s", int 3]] (rel Gt (iota "s") (int 0))
            , engine [FApp eqProof [iota "j", plus (iota "i") (int 1)], rel Lt (iota "i") (iota "n")] (rel LtEq (iota "j") (iota "n"))
            , engine [rel Lt (iota "a") (iota "b"), rel Lt (iota "b") (iota "c")] (rel Lt (iota "a") (iota "c"))
            , engine [rel Lt (iota "a") (iota "b")] (rel NotEq (iota "a") (iota "b"))
            , engine [FApp eqProof [iota "x", iota "y"]] (rel LtEq (iota "x") (iota "y"))
            , engine [] (rel GtEq (sizeOf (iota "l")) (int 0))
            , engine [] (rel Lt (int 2) (int 3))
            , -- Engine: nothing follows from too little
              engineNot [rel LtEq (iota "a") (iota "b")] (rel Lt (iota "a") (iota "b"))
            , engineNot [rel Lt (iota "i") (iota "n")] (rel Lt (plus (iota "i") (int 2)) (iota "n"))
            , engineNot [FApp eqProof [iota "s", int 0]] (rel Gt (iota "s") (int 0))
            , engineNot [rel Lt (iota "a") (iota "b")] (rel Lt (iota "b") (iota "a"))
            , engineNot [] (rel Gt (sizeOf (iota "l")) (int 0))
            , engineNot [rel LtEq (iota "a") (iota "b")] (rel NotEq (iota "a") (iota "b"))
            , -- Engine: a contradiction anywhere proves every comparison, also between unrelated terms
              engine [rel Lt (sizeOf (iota "xs")) (int 0)] (rel Lt (iota "a") (iota "b"))
            , engine [rel Lt (iota "p") (iota "q"), rel Lt (iota "q") (iota "p")] (rel Gt (iota "a") (iota "b"))
            , -- != parses, evaluates and validates
              parseEvalProgramHelper "return 3 != 4;" (Just (VBool True))
            , parseEvalProgramHelper "return 3 != 3;" (Just (VBool False))
            , parseEvalProgramHelper "x = 2; if x != 2 { return 1; } else { return 0; };" (Just (VInt 0))
            , parseValidProgramHelper "x = 2; affirm x != 3;"
            , parseValidateFailProgramHelper "x = 2; affirm x != 2;" "Could not prove"
            , parseValidProgramHelper "fn f(n: Int) -> Int { if n != 0 { affirm n != 0; } else { affirm n = 0; }; return 1; }; return f(4);"
            , -- Programs: no manual rewrites for the arithmetic
              parseValidProgramHelper "s = 3; affirm s > 0; affirm s >= 3; affirm s != 0;"
            , parseValidProgramHelper "x = 5; y = x + 1; affirm y > x; affirm y = 6;"
            , parseValidProgramHelper "fn f(l: List<Int>) -> Int { n = size(l); affirm n >= 0; return n; }; return f([1, 2]);"
            , parseValidProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i < n; }] [{ }] { j = i + 1; affirm j <= n; return j; }; return f(1, 2);"
            , parseValidateFailProgramHelper "x = 5; y = x + 1; affirm y > 6;" "Could not prove"
            , parseValidateFailProgramHelper "x = 5; y = x - 1; affirm y > 4;" "Could not prove"
            , parseValidateFailProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i <= n; }] [{ }] { j = i + 1; affirm j <= n; return j; };" "Could not prove"
            , -- The guard of an unreachable branch proves anything inside it
              parseValidProgramHelper "fn f(xs: List<Int>, a: Int, b: Int) -> Int { if size(xs) < 0 { affirm a < b; }; return 0; };"
            , -- A counting loop needs no axioms
              parseValidProgramHelper
                "i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { i = i + 1; }; affirm i = 3;"
            , parseValidateFailProgramHelper
                "i = 0; while i < 3 [{ affirm i <= 2; }] shrinks 3 - i { i = i + 1; };"
                "Loop invariant is not preserved"
            , parseValidateFailProgramHelper
                "i = 0; while i < 3 [{ affirm i >= 1; }] shrinks 3 - i { i = i + 1; };"
                "Loop invariant does not hold on entry"
            ]

-- forall parses into a bound index (BVar) with its guards, and the validator rejects it for now
-- forall facts are instantiated at the elements the program reads
testForallInstantiation :: Test
testForallInstantiation =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getOf l t = FApp (CTerm (builtinFunct Get)) [l, t]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        iota = ATerm . Iota
        int = CTerm . VInt
        allZero l = Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") (sizeOf l)] (rel Eq (getOf l (BVar "j")) (int 0))
        engine facts goal = testAssertTrue (Engine.entails goal (Engine.proofContextFromFacts facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (Engine.proofContextFromFacts facts)))
        inRange i l = [rel GtEq (iota i) (int 0), rel Lt (iota i) (sizeOf (iota l))]
        zeroAt l i = rel Eq (getOf (iota l) (iota i)) (int 0)
        -- reads element i of l under the contract that every element of l is 0
        reader = "fn f(l: List<Int>, i: Int) -> Int [{ affirm forall j in 0..size(l): get(l, j) = 0; rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] "
     in testCaseSeq
            "testForallInstantiation"
            [ -- Engine: an instance is used at the elements in the goal, when its guards hold
              engine (allZero (iota "l") : inRange "i" "l") (zeroAt "l" "i")
            , -- It also reaches elements of an equal list
              engine (allZero (iota "l") : rel Eq (iota "m") (iota "l") : inRange "i" "m") (zeroAt "m" "i")
            , -- and an index known only by its value
              engine [allZero (iota "l"), rel Eq (sizeOf (iota "l")) (int 3), rel Eq (iota "i") (int 2)] (zeroAt "l" "i")
            , -- Two elements, each with its own instance
              engine (allZero (iota "l") : inRange "i" "l" ++ inRange "k" "l") (rel Eq (getOf (iota "l") (iota "i")) (getOf (iota "l") (iota "k")))
            , -- Engine: an index outside the guards, another list, or no get term at all gets nothing
              engineNot (allZero (iota "l") : [rel GtEq (iota "i") (int 0)]) (zeroAt "l" "i")
            , engineNot (allZero (iota "l") : rel Lt (iota "i") (int 0) : [rel Lt (iota "i") (sizeOf (iota "l"))]) (zeroAt "l" "i")
            , engineNot (allZero (iota "l") : inRange "i" "m") (zeroAt "m" "i")
            , engineNot (inRange "i" "l") (zeroAt "l" "i")
            , engineNot (allZero (iota "l") : inRange "i" "l") (rel Eq (getOf (iota "l") (iota "i")) (int 1))
            , -- Programs: the contract's forall gives the element a function reads
              parseValidProgramHelper
                (reader ++ "[{ affirm return = 0; }] { x = get(l, i); return x; };")
            , parseValidProgramHelper
                ( zeroAxiom
                    ++ reader
                    ++ "[{ affirm return = 0; }] { x = get(l, i); return x; };\
                       \a = [0, 0]; rewrite zeros a; r = f(a, 1); affirm r = 0;"
                )
            , -- Without the forall, or with a guard that does not cover the index, nothing is known
              parseValidateFailProgramHelper
                "fn f(l: List<Int>, i: Int) -> Int [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm return = 0; }] { x = get(l, i); return x; };"
                "Could not prove"
            , parseValidateFailProgramHelper
                "fn f(l: List<Int>, i: Int) -> Int [{ affirm forall j in 0..1: get(l, j) = 0; rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm return = 0; }] { x = get(l, i); return x; };"
                "Could not prove"
            , parseValidateFailProgramHelper
                "fn f(l: List<Int>, m: List<Int>, i: Int) -> Int [{ affirm forall j in 0..size(l): get(l, j) = 0; rewrite checkRel i >= 0; rewrite checkRel i < size(m); affirm i >= 0; affirm i < size(m); }] [{ affirm return = 0; }] { x = get(m, i); return x; };"
                "Could not prove"
            , -- get's result is the term get(list, index), also without a forall
              parseValidProgramHelper
                "fn g(l: List<Int>, i: Int) -> Int [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ }] { x = get(l, i); y = get(l, i); affirm x = y; return x; };"
            ]

-- forall goals are proved for an arbitrary index that meets the guards
testForallProof :: Test
testForallProof =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getOf l t = FApp (CTerm (builtinFunct Get)) [l, t]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        iota = ATerm . Iota
        int = CTerm . VInt
        range hi = [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") hi]
        forallJ hi body = Forall "j" (range hi) body
        elementIsZero l = rel Eq (getOf l (BVar "j")) (int 0)
        engine facts goal = testAssertTrue (Engine.entails goal (Engine.proofContextFromFacts facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (Engine.proofContextFromFacts facts)))
     in testCaseSeq
            "testForallProof"
            [ -- Facts about the index alone
              engine [] (forallJ (int 3) (rel Lt (BVar "j") (int 3)))
            , engineNot [] (forallJ (int 3) (rel Lt (BVar "j") (int 2)))
            , engine [rel Eq (iota "n") (int 2)] (forallJ (iota "n") (rel Lt (BVar "j") (int 2)))
            , engineNot [] (forallJ (iota "n") (rel Lt (BVar "j") (int 2)))
            , -- A narrower range than a known forall, when the bound is known to be within it
              engine [forallJ (sizeOf (iota "l")) (elementIsZero (iota "l")), rel LtEq (iota "k") (sizeOf (iota "l"))] (forallJ (iota "k") (elementIsZero (iota "l")))
            , engineNot [forallJ (sizeOf (iota "l")) (elementIsZero (iota "l"))] (forallJ (iota "k") (elementIsZero (iota "l")))
            , -- The same forall about an equal list
              engine [forallJ (sizeOf (iota "l")) (elementIsZero (iota "l")), rel Eq (iota "m") (iota "l")] (forallJ (sizeOf (iota "m")) (elementIsZero (iota "m")))
            , -- Equal elements of two equal lists, and of two lists that are not known to be equal
              engine [rel Eq (iota "m") (iota "l")] (forallJ (sizeOf (iota "l")) (rel Eq (getOf (iota "l") (BVar "j")) (getOf (iota "m") (BVar "j"))))
            , engineNot [] (forallJ (sizeOf (iota "l")) (rel Eq (getOf (iota "l") (BVar "j")) (getOf (iota "m") (BVar "j"))))
            , -- An empty range holds for any body
              engine [] (forallJ (int 0) (rel Eq (int 1) (int 2)))
            , engine [rel LtEq (iota "n") (int 0)] (forallJ (iota "n") (rel Eq (int 1) (int 2)))
            , engineNot [] (forallJ (int 1) (rel Eq (int 1) (int 2)))
            , -- A guard other than a range
              engine [] (Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") (int 3), rel NotEq (BVar "j") (int 1)] (rel NotEq (BVar "j") (int 1)))
            , engineNot [] (Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") (int 3)] (rel NotEq (BVar "j") (int 1)))
            , -- Programs
              parseValidProgramHelper "affirm forall j in 0..3: j >= 0;"
            , parseValidProgramHelper "n = 2; affirm forall j in 0..n: j < 2;"
            , parseValidateFailProgramHelper "n = 3; affirm forall j in 0..n: j < 2;" "Could not prove"
            , parseValidProgramHelper "affirm forall j in 3..3: 1 = 2;"
            , -- Facts the program knows about other variables are used
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n <= 2; }] [{ affirm forall j in 0..n: j < 2; }] { return n; };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n <= 3; }] [{ affirm forall j in 0..n: j < 2; }] { return n; };" "Could not prove"
            , -- A function proves a forall about its result from one about its argument
              parseValidProgramHelper
                "fn id(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] { return l; };"
            , parseValidProgramHelper
                "fn id(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 7; }] [{ affirm forall j in 0..size(return): get(return, j) = 7; }] { return l; };"
            , parseValidateFailProgramHelper
                "fn id(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 1; }] { return l; };"
                "Could not prove"
            ]

-- A list that grew by one: the old elements are kept, and the new one sits at the old size
testForallGrownList :: Test
testForallGrownList =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getOf l t = FApp (CTerm (builtinFunct Get)) [l, t]
        sizeOf t = FApp (CTerm (builtinFunct Size)) [t]
        plus a b = FApp (CTerm (builtinFunct Plus)) [a, b]
        iota = ATerm . Iota
        int = CTerm . VInt
        forallJ hi body = Forall "j" [rel GtEq (BVar "j") (int 0), rel Lt (BVar "j") hi] body
        copiesA l = rel Eq (getOf l (BVar "j")) (getOf (iota "a") (BVar "j"))
        -- out0 copies a below i0, out1 keeps out0 below its size, and has a's element i0 after it
        grown =
            [ forallJ (iota "i0") (copiesA (iota "out0"))
            , forallJ (sizeOf (iota "out0")) (rel Eq (getOf (iota "out1") (BVar "j")) (getOf (iota "out0") (BVar "j")))
            , rel Eq (sizeOf (iota "out0")) (iota "i0")
            , rel Eq (getOf (iota "out1") (sizeOf (iota "out0"))) (getOf (iota "a") (iota "i0"))
            , rel Eq (iota "i1") (plus (iota "i0") (int 1))
            , rel GtEq (iota "i0") (int 0)
            ]
        engine facts goal = testAssertTrue (Engine.entails goal (Engine.proofContextFromFacts facts))
        engineNot facts goal = testAssertTrue (not (Engine.entails goal (Engine.proofContextFromFacts facts)))
     in testCaseSeq
            "testForallGrownList"
            [ -- Old elements come from the old fact, the new one from its own, and the cases are told apart
              engine grown (forallJ (iota "i1") (copiesA (iota "out1")))
            , -- The old range alone still holds for the new list
              engine grown (forallJ (iota "i0") (copiesA (iota "out1")))
            , -- Not past the new element
              engineNot grown (forallJ (plus (iota "i1") (int 1)) (copiesA (iota "out1")))
            , -- Without the new element's fact, or without the old elements', it does not hold
              engineNot (filter (/= (grown !! 3)) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            , engineNot (filter (/= head grown) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            , engineNot (filter (/= (grown !! 1)) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            , -- Without knowing the old size is i0, the new element is not at the end of the range
              engineNot (filter (/= (grown !! 2)) grown) (forallJ (iota "i1") (copiesA (iota "out1")))
            ]

-- forall in loop invariants and the contracts of functions that build lists
testValidationFuel :: Test
testValidationFuel =
    let twice n =
            "fn twice(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; c = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; c = c + 2; }; return c; };"
                ++ "x = twice("
                ++ show (n :: Int)
                ++ "); affirm x = "
                ++ show (2 * n)
                ++ ";"
     in testCaseSeq
            "testValidationFuel"
            [ -- Validation evaluates a call whose arguments are known, so its result is a fact
              parseValidProgramHelper (twice 1000)
            , -- A computation longer than the budget is given up on, so its result is not known
              -- (the program still runs: concrete evaluation has no budget)
              parseValidateFailProgramHelper (twice 50000) "Could not prove: x = 100000"
            , parseEvalProgramHelper (twice 50000 ++ " return x;") (Just (VInt 100000))
            , -- Naming an element with define is how a forall fact gets used at it (LANGUAGE.md, How Validation Works)
              parseValidProgramHelper "fn f(l: List<Int>) -> Int [{ affirm size(l) > 3; affirm forall j in 0..size(l): get(l, j) = 0; }] [{ }] { define v = get(l, 1); affirm v = 0; return 1; };"
            , -- A callee that never ends does not stop validation
              parseValidProgramHelper "fn spin(n: Int) -> Int [{ }] [{ }] ~ { i = 0; while i >= 0 [{ affirm i >= 0; }] ~ { i = i + 1; }; return i; }; x = spin(1);"
            ]

testFunctionCalls :: Test
testFunctionCalls =
    let inc = "fn inc(n: Int) -> Int [{ }] [{ affirm return = (n + 1); }] { return n + 1; };"
        positive = "fn positive(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; };"
     in testCaseSeq
            "testFunctionCalls"
            [ -- A function calls the functions defined before it
              parseEvalProgramHelper (inc ++ "fn twice(n: Int) -> Int [{ }] [{ }] { return inc(inc(n)); }; return twice(3);") (Just (VInt 5))
            , parseValidProgramHelper (inc ++ "fn twice(n: Int) -> Int [{ }] [{ affirm return = (n + 2); }] { return inc(inc(n)); }; x = twice(3); affirm x = 5;")
            , -- Chains of calls and calls with contracts of their own
              parseEvalProgramHelper (inc ++ positive ++ "fn bump(n: Int) -> Int [{ affirm n >= 5; }] [{ affirm return > 5; }] { return positive(inc(n)); }; return bump(5);") (Just (VInt 6))
            , parseValidProgramHelper (inc ++ positive ++ "fn bump(n: Int) -> Int [{ affirm n >= 5; }] [{ affirm return > 5; }] { return positive(inc(n)); };")
            , -- Rejected: the callee's input contract is not met, or the caller's own output contract is not
              parseValidateFailProgramHelper (positive ++ "fn bump(n: Int) -> Int [{ }] [{ }] { return positive(n); };") "Could not prove: n > 0"
            , parseValidateFailProgramHelper (inc ++ "fn twice(n: Int) -> Int [{ }] [{ affirm return = (n + 3); }] { return inc(inc(n)); };") "Could not prove"
            , -- A function cannot call one defined after it, and a name is defined once
              parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { return g(n); }; fn g(n: Int) -> Int [{ }] [{ }] { return n; };" "Undefined variable: g"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { return n; }; fn f(n: Int) -> Int [{ }] [{ }] { return n + 1; };" "Function already defined: f"
            , parseEvalProgramFailHelper "fn f(n: Int) -> Int [{ }] [{ }] { return n; }; fn f(n: Int) -> Int [{ }] [{ }] { return n + 1; };" "Function already defined: f"
            , -- A function defined inside a body is local to it: a later local function cannot call it
              parseValidProgramHelper "fn outer(n: Int) -> Int { fn helper(m: Int) -> Int { return m; }; return helper(n); }; x = outer(1);"
            , parseValidateFailProgramHelper "fn outer(n: Int) -> Int { fn helper(m: Int) -> Int { return m; }; fn user(m: Int) -> Int { return helper(m); }; return user(n); };" "Undefined variable: helper"
            , -- An argument or local variable with the same name hides the function
              parseEvalProgramHelper "fn inc(n: Int) -> Int [{ }] [{ }] { return n + 1; }; fn f(inc: Int) -> Int [{ }] [{ }] { return inc + 1; }; return f(3);" (Just (VInt 4))
            , -- The calls made by a function are not visible to its caller's other statements
              parseValidProgramHelper (inc ++ "fn twice(n: Int) -> Int [{ }] [{ }] { return inc(inc(n)); }; inc2 = 1; affirm inc2 = 1;")
            ]

testPrecedence :: Test
testPrecedence =
    let plus a b = F (Val (builtinFunct Plus)) [a, b]
        times a b = F (Val (builtinFunct Times)) [a, b]
        rel r a b = F (Val (builtinFunct (Rel r))) [a, b]
        int = Val . VInt
     in testCaseSeq
            "testPrecedence"
            [ -- `*` and `/` bind tighter than `+` and `-`, which bind tighter than the relations
              case parseStatementBlock "x = a + 1 < b * 2;" of
                Right parsed -> testAssertEq parsed [Assign "x" (rel Lt (plus (Var "a") (int 1)) (times (Var "b") (int 2)))]
                Left err -> Just (show err)
            , case parseStatementBlock "x = a = b - 1 * 2;" of
                Right parsed -> testAssertEq parsed [Assign "x" (rel Eq (Var "a") (F (Val (builtinFunct Minus)) [Var "b", times (int 1) (int 2)]))]
                Left err -> Just (show err)
            , parseEvalProgramHelper "return 1 + 2 = 3;" (Just (VBool True))
            , parseEvalProgramHelper "return 2 * 3 < 4 + 3;" (Just (VBool True))
            , -- Relations in proofs follow the same levels, so contracts need no parentheses
              parseValidProgramHelper "fn inc(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n + 1; }; x = inc(2); affirm x = 3; affirm x - 1 = 2 * 1;"
            , parseValidateFailProgramHelper "x = 2; affirm x + 1 = 4;" "Could not prove: x + 1 = 4"
            ]

testFirstLast :: Test
testFirstLast =
    let guarded body = "fn f(l: List<Int>) -> Int [{ affirm size(l) > 1; affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm return = 0; }] { return " ++ body ++ "; };"
     in testCaseSeq
            "testFirstLast"
            [ -- first and last are get at the first and the last index
              parseValidProgramHelper "fn f(l: List<Int>) -> Int [{ affirm size(l) > 0; }] [{ affirm return = get(l, 0); }] { return first(l); };"
            , parseValidProgramHelper "fn f(l: List<Int>) -> Int [{ affirm size(l) > 0; }] [{ affirm return = get(l, size(l) - 1); }] { return last(l); };"
            , parseValidProgramHelper "fn f(l: List<Int>) -> Int [{ affirm size(l) = 2; }] [{ affirm return = get(l, 1); }] { return last(l); };"
            , parseValidProgramHelper "l = [4, 5, 6]; affirm first(l) = 4; affirm last(l) = 6;"
            , -- A forall about the elements reaches them
              parseValidProgramHelper (guarded "first(l) + last(l)")
            , -- Rejected: the other end of the list, or an index that is not the last one
              parseValidateFailProgramHelper "fn f(l: List<Int>) -> Int [{ affirm size(l) > 1; }] [{ affirm return = get(l, 0); }] { return last(l); };" "Could not prove: return = get(l, 0)"
            , parseValidateFailProgramHelper "fn f(l: List<Int>) -> Int [{ affirm size(l) > 2; }] [{ affirm return = get(l, 1); }] { return last(l); };" "Could not prove: return = get(l, 1)"
            ]

testRecursion :: Test
testRecursion =
    let upTo = "fn upTo(i: Int, n: Int) -> Int [{ affirm i <= n; }] [{ affirm return = n; }] shrinks n - i { if i < n { return upTo(i + 1, n); } else { return n; }; };"
     in testCaseSeq
            "testRecursion"
            [ -- A function calls itself, in evaluation and in validation
              parseEvalProgramHelper (upTo ++ "return upTo(0, 5);") (Just (VInt 5))
            , parseValidProgramHelper (upTo ++ "x = upTo(0, 5); affirm x = 5;")
            , parseValidProgramHelper (upTo ++ "fn useIt(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n; }] { return upTo(0, n); };")
            , -- The recursive call must meet the input contract
              parseValidateFailProgramHelper "fn down(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return = 0; }] shrinks n { if n < 2 { return 0; } else { return down(n - 3); }; };" "Could not prove: n > 0"
            , -- The body must establish the output contract, which is assumed only for the recursive calls
              parseValidateFailProgramHelper "fn down(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = 0; }] shrinks n { if n < 1 { return 1; } else { return down(n - 1); }; };" "Could not prove: return = 0"
            , -- Recursion over a list, with an affirm that becomes a fact in the last step
              parseValidProgramHelper "fn sumFrom(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i <= size(l); }] [{ }] shrinks size(l) - i { if i < size(l) { return get(l, i) + sumFrom(l, i + 1); } else { return 0; }; };"
            , parseEvalProgramHelper "fn sumFrom(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i <= size(l); }] [{ }] shrinks size(l) - i { if i < size(l) { return get(l, i) + sumFrom(l, i + 1); } else { return 0; }; }; return sumFrom([4, 5, 6], 0);" (Just (VInt 15))
            , parseValidProgramHelper "fn endOf(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); }] [{ affirm return = get(l, size(l) - 1); }] shrinks size(l) - i { if i + 1 < size(l) { return endOf(l, i + 1); } else { affirm i = size(l) - 1; return get(l, i); }; };"
            , parseValidateFailProgramHelper "fn endOf(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); }] [{ affirm return = get(l, size(l) - 1); }] shrinks size(l) - i { if i + 1 < size(l) { return endOf(l, i + 1); } else { return get(l, i); }; };" "Could not prove: return = get(l, size(l) - 1)"
            , -- Partial correctness: a function declared ~ that never returns satisfies any output contract
              parseValidProgramHelper "fn spin(n: Int) -> Int [{ }] [{ affirm return = 0; }] ~ { return spin(n); };"
            , -- A name is still defined once
              parseValidateFailProgramHelper (upTo ++ upTo) "Function already defined: upTo"
            , -- An affirm that is proved becomes a fact: it links i to size(l) - 1 so get(l, i) is get(l, size(l) - 1)
              parseValidProgramHelper "fn g(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); affirm i + 1 >= size(l); }] [{ affirm return = get(l, size(l) - 1); }] { affirm i = size(l) - 1; return get(l, i); };"
            , parseValidateFailProgramHelper "fn g(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); affirm i + 1 >= size(l); }] [{ affirm return = get(l, size(l) - 1); }] { return get(l, i); };" "Could not prove: return = get(l, size(l) - 1)"
            ]

-- x != y is a fact, and c * x for a constant c is related to the terms it is made from by the difference constraints
testRefinedArithmetic :: Test
testRefinedArithmetic =
    let given facts goal = "fn f(i: Int, j: Int, n: Int, m: Int) -> Int [{ " ++ facts ++ " }] [{ }] { affirm " ++ goal ++ "; return 0; };"
        holds facts goal = parseValidProgramHelper (given facts goal)
        fails facts goal = parseValidateFailProgramHelper (given facts goal) ("Could not prove: " ++ goal)
     in testCaseSeq
            "testRefinedArithmetic"
            [ -- x != y with x <= y is x < y, also next to a constant
              holds "affirm i >= -3; affirm i != -3;" "i > -3"
            , holds "affirm i <= n; affirm i != n;" "i < n"
            , holds "affirm i <= n; affirm i != n;" "i + 1 <= n"
            , holds "affirm n >= i; affirm n != i;" "i < n"
            , holds "affirm i < n; affirm i != n;" "i < n"
            , fails "affirm i <= 5; affirm i != 3;" "i < 3"
            , fails "affirm i != n;" "i < n"
            , holds "affirm i != n; affirm i <= n; affirm n <= i;" "j = j + 1"
            , -- A loop that stops at a value other than its bound
              parseValidProgramHelper "i = 5; while i != 0 [{ affirm i >= 0; }] shrinks i { i = i - 1; }; affirm i = 0;"
            , parseValidProgramHelper "i = 5; while i != -3 [{ affirm i >= -3; }] shrinks i + 3 { i = i - 1; };"
            , -- c * x for a positive or negative constant
              holds "affirm n > 0;" "2 * n > 0"
            , holds "affirm n > 0;" "n * 2 > 0"
            , holds "affirm n >= 1;" "3 * n >= 3"
            , holds "affirm n > 2;" "n * 3 > 6"
            , fails "affirm n >= 0;" "2 * n > 0"
            , fails "affirm n >= 1;" "3 * n > 3"
            , holds "affirm n < 0;" "-2 * n > 0"
            , fails "affirm n <= 0;" "-2 * n > 0"
            , holds "affirm n < m;" "2 * n < 2 * m"
            , holds "affirm n < m;" "2 * n < 2 * m - 1"
            , fails "affirm n < m;" "2 * n < 2 * m - 2"
            , holds "affirm n <= m;" "3 * n <= 3 * m"
            , fails "affirm n <= m;" "2 * n < 2 * m"
            , holds "affirm n < m;" "-2 * m < -2 * n"
            , -- Different constants are different terms
              fails "affirm n < m;" "2 * n < 3 * m"
            , -- A variant that is twice a counter
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks 2 * n { if n < 1 { return 0; } else { return f(n - 1); }; }; x = f(3);"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks 2 * n { if n < 1 { return 0; } else { return f(n + 1); }; }; x = f(3);" "Recursive call does not shrink the variant"
            ]

-- for i in lo..hi counts a loop variable, and the validator is given its bounds, its termination and (see
-- testInferredInvariants) what grows in step with it
testForLoops :: Test
testForLoops =
    let sumList = "fn total(a: List<Int>) -> Int { s = 0; for i in 0..size(a) { s = s + get(a, i); }; return s; };"
     in testCaseSeq
            "testForLoops"
            [ -- Evaluation: the range is half open, hi is read once, and the variable is hi afterwards
              parseEvalProgramHelper "n = 0; for i in 0..4 { n = n + i; }; return n;" (Just (VInt 6))
            , parseEvalProgramHelper "n = 0; for i in 3..3 { n = n + 1; }; return n * 10 + i;" (Just (VInt 3))
            , parseEvalProgramHelper "n = 0; for i in 5..2 { n = n + 1; }; return n;" (Just (VInt 0))
            , parseEvalProgramHelper "l = [1, 2]; n = 0; for i in 0..size(l) { l = push(l, 0); n = n + 1; }; return n;" (Just (VInt 2))
            , parseEvalProgramHelper "n = 0; for i in 0..3 { for j in 0..i { n = n + 1; }; }; return n;" (Just (VInt 3))
            , parseEvalProgramHelper "fn f(l: List<Int>) -> Int { for i in 0..size(l) { if get(l, i) > 2 { return i; }; }; return -1; }; return f([1, 5]) + f([1]);" (Just (VInt 0))
            , parseEvalProgramHelper (sumList ++ "return total([1, 2, 3]);") (Just (VInt 6))
            , -- Validation: i is at least lo and below hi inside, so get is in range, and i = hi afterwards
              parseValidProgramHelper sumList
            , parseValidProgramHelper "n = 0; for i in 2..5 { n = n + i; }; affirm i = 5;"
            , parseValidProgramHelper "fn f(a: List<Int>) -> Int [{ affirm size(a) > 0; }] [{ }] { for i in 1..size(a) { x = get(a, i - 1); }; return 0; };"
            , parseValidProgramHelper "fn f(l: List<Int>) -> Int { for i in 0..size(l) { if get(l, i) > 2 { return i; }; }; return -1; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { t = 0; for i in 0..n { for j in 0..i { t = t + 1; }; }; return t; };"
            , -- An invariant can be written as for a while loop, and uses i
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = 0; }] { z = 0; for i in 0..n [{ affirm z = 0; }] { z = z * 1; }; return z; };"
            , -- Refused: reading past the end, writing the variable, and an invariant the body breaks
              parseValidateFailProgramHelper "fn f(a: List<Int>) -> Int { s = 0; for i in 0..size(a) + 1 { s = s + get(a, i); }; return s; };" "Funct input validation failed"
            , parseValidateFailProgramHelper "for i in 0..3 { i = i + 1; };" "Loop invariant is not preserved: Could not prove: i <= (end of for i)"
            , parseValidateFailProgramHelper "z = 0; for i in 0..3 [{ affirm z = 0; }] { z = z + 1; };" "Loop invariant is not preserved: Could not prove: z = 0"
            , parseValidateFailProgramHelper "n = 0; for i in 0..3 { n = n + 1; }; affirm i = 4;" "Could not prove: i = 4"
            ]

-- Loops get the invariants a counter and the lists built beside it satisfy, without the program writing them
testInferredInvariants :: Test
testInferredInvariants =
    let building body = "fn f(a: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(a); }] { out = []; " ++ body ++ " return out; };"
     in testCaseSeq
            "testInferredInvariants"
            [ -- A list that gets an element per iteration has the size of the counter
              parseValidProgramHelper (building "for i in 0..size(a) { out = push(out, 0); };")
            , parseValidProgramHelper (building "i = 0; n = size(a); while i < n [{ affirm i <= n; }] shrinks n - i { out = push(out, get(a, i)); i = i + 1; };")
            , parseValidProgramHelper "out = []; i = 0; while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { out = push(out, i); i = i + 1; }; affirm size(out) = 3;"
            , -- Counters keep their distance, and a lower bound they keep
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = 0; j = 5; while i < n [{ affirm i <= n; }] shrinks n - i { i = i + 1; j = j + 1; }; affirm j = i + 5; return 0; };"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 3; }] { i = 3; while i < n [{ affirm i <= n + 1; }] shrinks n - i { i = i + 2; }; affirm i >= 3; return 0; };"
            , -- set keeps the size
              parseValidProgramHelper "l = [1, 2, 3]; for i in 0..3 { l = set(l, i, 0); }; affirm size(l) = 3;"
            , -- Only what the body keeps is inferred
              parseValidateFailProgramHelper (building "for i in 0..size(a) { out = push(out, 0); out = push(out, 1); };") "Could not prove: size(return) = size(a)"
            , parseValidateFailProgramHelper "out = []; for i in 0..3 { if i > 1 { out = push(out, i); }; }; affirm size(out) = 3;" "Could not prove: size(out) = 3"
            , parseValidateFailProgramHelper "out = []; i = 0; while i < 3 shrinks 3 - i { out = push(out, i); i = i + 2; }; affirm size(out) = 2;" "Could not prove: size(out) = 2"
            , parseValidateFailProgramHelper "i = 0; while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { i = i + 1; }; affirm i = 0;" "Could not prove: i = 0"
            , -- A mistake in the invariant is reported as before
              parseValidateFailProgramHelper "out = []; i = 0; while i < 3 [{ affirm size(out) = 7; }] shrinks 3 - i { out = push(out, i); i = i + 1; };" "Loop invariant does not hold on entry"
            , -- A loop that returns infers nothing, and still validates with what the program says
              parseValidProgramHelper "fn f(a: List<Int>) -> Int { out = []; for i in 0..size(a) { if get(a, i) > 2 { return i; }; out = push(out, 0); }; return -1; };"
            ]

-- Loops and recursive functions say why they end, and code that may not end is declared
testTermination :: Test
testTermination =
    let tree = "enum Tree { Leaf, Branch { left: Tree, right: Tree } };"
        settle = "fn settle(n: Int) -> Int ~ { while n != 1 ~ { n = n - 1; }; return n; };"
     in testCaseSeq
            "testTermination"
            [ -- The clause is parsed before the body, after an invariant, and after the contracts of a function
              case parseStatementBlock "while i < 3 [{ affirm i <= 3; }] shrinks 3 - i { i = i + 1; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right [While _ inv (Just (Shrinks _)) _] -> testAssertEq (length inv) 1
                Right other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock "while i < 3 ~ { i = i + 1; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right [While _ _ (Just MayDiverge) _] -> Nothing
                Right other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock (tree ++ "while t is Tree::Branch shrinks t { t = t; };") of
                Left err -> Just ("Parse error: " ++ show err)
                Right [_, While _ _ (Just (Shrinks _)) _] -> Nothing
                Right other -> Just ("Unexpected parse: " ++ show other)
            , -- A loop has to say how it ends
              parseValidateFailProgramHelper "i = 0; while i < 3 { i = i + 1; };" "Loop must say how it ends"
            , parseValidProgramHelper "i = 0; while i < 3 ~ { i = i + 1; };"
            , -- The variant is at least 0 when an iteration starts, and smaller when it ends
              parseValidProgramHelper "i = 0; while i < 3 shrinks 3 - i { i = i + 1; };"
            , parseValidateFailProgramHelper "i = 0; while i < 3 shrinks 3 - i { };" "Loop variant does not shrink: 3 - i"
            , parseValidateFailProgramHelper "i = 0; while i < 3 [{ affirm i >= 0; }] shrinks i { i = i + 1; };" "Loop variant does not shrink: i"
            , parseValidateFailProgramHelper "fn f(i: Int) -> Int { while i != 0 shrinks i { i = i - 1; }; return i; };" "Loop variant is not bounded below: i"
            , -- Counting down towards a bound that moves, and a body with an early return
              parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 shrinks i { if i = 7 { return 7; }; i = i - 1; }; return i; };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { i = n; while i > 0 shrinks i { if i = 7 { return 7; }; i = i + 1; }; return i; };" "Loop variant does not shrink: i"
            , -- Loops inside loops each have their own variant
              parseValidProgramHelper "i = 0; while i < 3 shrinks 3 - i { j = 0; while j < 2 shrinks 2 - j { j = j + 1; }; i = i + 1; };"
            , -- A difference is compared by its sides
              parseValidProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i <= n; }] [{ }] { affirm n - i >= 0; return 0; };"
            , parseValidProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i < n; }] [{ }] { affirm n - (i + 1) < n - i; return 0; };"
            , parseValidateFailProgramHelper "fn f(i: Int, n: Int) -> Int [{ affirm i < n; }] [{ }] { affirm n - i < 0; return 0; };" "Could not prove: n - i < 0"
            , -- A function that calls itself says what shrinks
              parseValidateFailProgramHelper "fn down(n: Int) -> Int [{ affirm n >= 0; }] { if n < 1 { return 0; } else { return down(n - 1); }; };" "Not guaranteed to terminate: it calls itself"
            , parseValidProgramHelper "fn down(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n < 1 { return 0; } else { return down(n - 1); }; };"
            , parseValidateFailProgramHelper "fn down(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { if n < 1 { return 0; } else { return down(n); }; };" "Recursive call does not shrink the variant: n"
            , parseValidateFailProgramHelper "fn down(n: Int) -> Int shrinks n { if n < 1 { return 0; } else { return down(n - 1); }; };" "Function variant is not bounded below: n"
            , parseValidProgramHelper "fn down(n: Int) -> Int ~ { return down(n); };"
            , -- Recursion over a structure: the call is given a field of the value
              parseValidProgramHelper (tree ++ "fn count(t: Tree) -> Int shrinks t { return match t { Tree::Leaf => 1, Tree::Branch { left: l, right: r } => count(l) + count(r) }; };")
            , parseValidateFailProgramHelper (tree ++ "fn count(t: Tree) -> Int shrinks t { return match t { Tree::Leaf => 1, Tree::Branch { left: l, right: r } => count(l) + count(t) }; };") "Recursive call does not shrink the variant: t"
            , parseValidProgramHelper (tree ++ "fn depth(t: Tree) -> Int { n = 0; while t is Tree::Branch shrinks t { t = (t as Tree::Branch).left; n = n + 1; }; return n; };")
            , parseValidateFailProgramHelper (tree ++ "fn depth(t: Tree) -> Int { n = 0; while t is Tree::Branch shrinks t { n = n + 1; }; return n; };") "Loop variant does not shrink: t"
            , -- Code that may not end makes a function that contains it say so
              parseValidProgramHelper settle
            , parseValidateFailProgramHelper "fn settle(n: Int) -> Int { while n != 1 ~ { n = n - 1; }; return n; };" "Not guaranteed to terminate: a loop is declared ~"
            , parseValidateFailProgramHelper (settle ++ "fn twice(n: Int) -> Int { return settle(n) + 1; };") "Not guaranteed to terminate: it calls a function that is declared ~"
            , parseValidProgramHelper (settle ++ "fn twice(n: Int) -> Int ~ { return settle(n) + 1; };")
            , -- A cycle has to be a function calling itself: a function inside another cannot call the one around it unless both say ~
              parseValidProgramHelper "fn f(n: Int) -> Int ~ { fn g(m: Int) -> Int ~ { return f(m); }; return g(n); };"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int ~ { fn g(m: Int) -> Int { return f(m); }; return g(n); };" "Not guaranteed to terminate: it calls a function that is declared ~"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int { fn g(m: Int) -> Int { return f(m); }; return g(n); };" "Not guaranteed to terminate: it calls itself"
            , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { fn g(m: Int) -> Int [{ affirm m >= 0; }] { return f(m); }; if n < 1 { return 0; } else { return g(n - 1); }; };" "not from a function defined inside it"
            , -- Calling itself through another name is still a call to itself
              parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] { h = f; return h(n); };" "Not guaranteed to terminate: it calls itself"
            , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] shrinks n { h = f; if n < 1 { return 0; } else { return h(n - 1); }; };"
            , -- A function sees only the functions before it, so two cannot call each other
              parseValidateFailProgramHelper "fn a(n: Int) -> Int { return b(n); }; fn b(n: Int) -> Int { return a(n); };" "Undefined variable: b"
            , -- The program itself may call one
              parseValidProgramHelper (settle ++ "x = settle(3);")
            , -- Code that cannot be reached is not counted
              parseValidProgramHelper (settle ++ "fn f(n: Int) -> Int { if n > 0 { if n < 0 { return settle(n); }; }; return n; };")
            , parseValidateFailProgramHelper (settle ++ "fn f(n: Int) -> Int { if n > 0 { if n < 5 { return settle(n); }; }; return n; };") "Not guaranteed to terminate"
            , -- A function defined inside another says for itself
              parseValidProgramHelper (settle ++ "fn outer(n: Int) -> Int { fn inner(m: Int) -> Int ~ { return settle(m); }; return n; };")
            , parseValidateFailProgramHelper (settle ++ "fn outer(n: Int) -> Int ~ { fn inner(m: Int) -> Int { return settle(m); }; return n; };") "Not guaranteed to terminate"
            , -- The type of what shrinks decides what it means: an Int counts down, an enum or struct loses a field
              case parseStatementBlock "i = 0; while i < 3 shrinks 3 - i { i = i + 1; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborate stmts of
                    Ok [_, While _ _ (Just (Counting _)) _] -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , case parseStatementBlock (tree ++ "t = Tree::Leaf; while t is Tree::Branch shrinks t { t = (t as Tree::Branch).left; };") of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborate stmts of
                    Ok [_, _, While _ _ (Just (Parts _)) _] -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , case parseStatementBlock "fn f(n: Int) -> Int shrinks n { return 0; };" of
                Left err -> Just ("Parse error: " ++ show err)
                Right stmts -> case elaborate stmts of
                    Ok [Assign _ (Val (VFunct _ _ _ (NativeFunct _ (Just (Counting _)) _) _))] -> Nothing
                    other -> Just ("Unexpected: " ++ show other)
            , parseValidateFailProgramHelper "x = [1]; while x = x shrinks x { x = x; };" "shrinks needs an Int, an enum or a struct, got List<Int>"
            , parseValidateFailProgramHelper "fn f(b: Bool) -> Int shrinks b { return 0; };" "shrinks needs an Int, an enum or a struct, got Bool"
            , -- Evaluation does not use any of it
              parseEvalProgramHelper "i = 0; while i < 3 shrinks 3 - i { i = i + 1; }; return i;" (Just (VInt 3))
            ]

-- The validator keeps a solver of the visible facts between questions, and uses it only while it holds nothing the
-- state has lost
testSolverCache :: Test
testSolverCache =
    testCaseSeq
        "testSolverCache"
        [ -- A fact assumed in a branch is not visible after the if, though the branch has been validated before the question
          parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { a = 0; affirm n = n; if n > 7 { affirm n > 7; a = 1; } else { a = 2; }; affirm n > 7; return a; };" "Could not prove: n > 7"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ }] [{ }] { a = 0; if n > 7 { affirm n > 7; a = 1; } else { a = 2; }; affirm n = n; return a; };"
        , -- Facts from before the if are still visible after it
          parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 3; }] [{ }] { a = 0; affirm n >= 3; if n > 7 { a = 1; } else { a = 2; }; affirm n > 2; return a; };"
        , -- The same for a loop: what the body assumes is gone after it
          parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { affirm i < n; i = i + 1; }; affirm i < n; return i; };" "Could not prove: i < n"
        , -- Facts about a list built by many calls
          parseValidProgramHelper "l = []; l = push(l, 1); affirm size(l) = 1; l = push(l, 2); affirm size(l) = 2; l = push(l, 3); affirm get(l, 0) = 1; affirm get(l, 2) = 3; affirm size(l) = 3;"
        , parseValidateFailProgramHelper "l = []; l = push(l, 1); affirm size(l) = 1; l = push(l, 2); affirm size(l) = 3;" "Could not prove: size(l) = 3"
        ]

testTypeCheck :: Test
testTypeCheck =
    let typeError source expected =
            case parseStatementBlock source of
                Left err -> Just ("Parse failed: " ++ show err)
                Right stmts -> testAssertErrorContains expected (typeCheck stmts)
        typeOk source =
            case parseStatementBlock source of
                Left err -> Just ("Parse failed: " ++ show err)
                Right stmts -> case typeCheck stmts of
                    Ok () -> Nothing
                    Error e -> Just ("Type check failed: " ++ e)
        parseFails source =
            case parseStatementBlock source of
                Left _ -> Nothing
                Right _ -> Just ("Expected a parse error for: " ++ source)
     in testCaseSeq
            "testTypeCheck"
            [ -- Well typed programs
              typeOk "x = 1; l = [1, 2]; y = size(l) + x; b = y < 3; affirm b = b;"
            , typeOk "fn f(l: List<Int>, i: Int) -> List<Int> { return push(l, get(l, i)); }; r = f([1], 0);"
            , typeOk "fn isBig(n: Int) -> Bool { return n > 9; }; if isBig(10) { x = 1; };"
            , typeOk "fn apply(g: fn(Int) -> Int, n: Int) -> Int { return g(g(n)); }; fn inc(n: Int) -> Int { return n + 1; }; r = apply(inc, 1);"
            , typeOk "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; }; x = f(2);"
            , typeOk "l = []; l = push(l, 1); m = set(l, 0, 5); x = first(m) + last(m);"
            , -- Equality works on any type, ordering only on Int
              typeOk "affirm [1] = [1]; affirm true = true;"
            , typeError "affirm [1] < [2];" "expected Int, got List<Int>"
            , typeError "for i in 0..true { x = 1; };" "expected Int, got Bool"
            , typeError "for i in [1]..3 { x = 1; };" "expected Int, got List<Int>"
            , typeError "while 1 < 2 shrinks true { x = 2; };" "shrinks needs an Int, an enum or a struct, got Bool"
            , -- Builtins
              typeError "x = size(5);" "argument 1 of size: expected List<?>, got Int"
            , typeError "l = [1]; x = push(l, [2]);" "argument 2 of push: expected Int, got List<Int>"
            , typeError "x = set([1], 0, true);" "argument 3 of set: expected Int, got Bool"
            , typeError "x = get([1], [0]);" "argument 2 of get: expected Int, got List<Int>"
            , typeError "x = 1 + [1];" "expected Int, got List<Int>"
            , -- Variables keep their type
              typeError "x = 1; x = [1];" "assignment to x: expected Int, got List<Int>"
            , typeError "x = y;" "Undefined variable: y"
            , typeError "if 1 { x = 2; };" "condition of if: expected Bool, got Int"
            , typeError "while 1 [{ }] { x = 2; };" "condition of while: expected Bool, got Int"
            , -- A variable assigned in a branch is local to it
              typeError "if true { t = 1; }; x = t;" "Undefined variable: t"
            , -- Functions: parameters, return and arity
              typeError "fn f(n: Int) -> Int { l = [1]; return l; };" "returned value: expected Int, got List<Int>"
            , typeError "fn f(n: Int) -> Int { return n; }; x = f([1]);" "argument 1 of f: expected Int, got List<Int>"
            , typeError "fn f(n: Int) -> Int { return n; }; x = f(1, 2);" "f takes 1 arguments, got 2"
            , typeError "fn f(n: Int) -> Bool { return n; };" "returned value: expected Bool, got Int"
            , typeError "x = 1; y = x(2);" "x is not a function"
            , -- Equality is structural, which functions do not have
              typeError "fn f(n: Int) -> Int { return n; }; b = f = f;" "functions cannot be compared"
            , typeError "fn f(n: Int) -> Int { return n; }; fn g(n: Int) -> Int { return n; }; affirm f != g;" "functions cannot be compared"
            , -- Bodies see only their parameters and earlier functions
              typeError "y = 1; fn f(n: Int) -> Int { return y; };" "Undefined variable: y"
            , typeError "fn f(n: Int) -> Int { return g(n); }; fn g(n: Int) -> Int { return n; };" "Undefined variable: g"
            , typeOk "fn f(n: Int) -> Int { return n; }; fn g(n: Int) -> Int { return f(n); };"
            , -- Contracts and proofs are typed too
              typeError "fn f(n: Int) -> Int [{ affirm n; }] [{ }] { return n; };" "affirmed proof: expected Bool, got Int"
            , typeError "fn f(l: List<Int>) -> Int [{ }] [{ affirm return = l; }] { return 1; };" "expected Int, got List<Int>"
            , typeError "fn f(l: List<Int>) -> Int [{ affirm forall j in 0..size(l): get(l, j); }] [{ }] { return 1; };" "body of forall: expected Bool"
            , typeOk "fn f(l: List<Int>) -> Int [{ affirm size(l) > 0; define s = size(l); }] [{ affirm s > 0; }] { return first(l); };"
            , -- Annotations are required
              parseFails "fn f(n) -> Int { return n; };"
            , parseFails "fn f(n: Int) { return n; };"
            , typeError "fn f(n: Float) -> Int { return 1; };" "unknown type Float"
            , -- validate runs the check first
              parseValidateFailProgramHelper "fn f(n: Int) -> List<Int> { return n; }; x = 1;" "returned value: expected List<Int>, got Int"
            ]

testGenericLists :: Test
testGenericLists =
    let ints = VList . map VInt
     in testCaseSeq
            "testGenericLists"
            [ -- Lists of any element type, in evaluation
              parseEvalProgramHelper "return [true, false];" (Just (VList [VBool True, VBool False]))
            , parseEvalProgramHelper "return [[1, 2], [3]];" (Just (VList [ints [1, 2], ints [3]]))
            , parseEvalProgramHelper "return get([[1, 2], [3]], 1);" (Just (ints [3]))
            , parseEvalProgramHelper "return size([[1, 2], [3], []]);" (Just (VInt 3))
            , parseEvalProgramHelper "return push([[1]], [2, 3]);" (Just (VList [ints [1], ints [2, 3]]))
            , parseEvalProgramHelper "return [1, 2] = [1, 2];" (Just (VBool True))
            , parseEvalProgramHelper "return [true] != [false];" (Just (VBool True))
            , parseEvalProgramHelper "return first([true]);" (Just (VBool True))
            , parseEvalProgramHelper "return set([true, true], 1, false);" (Just (VList [VBool True, VBool False]))
            , parseEvalProgramHelper "return [-1, 2];" (Just (ints [-1, 2]))
            , -- Types
              parseValidProgramHelper "fn flags(n: Int) -> List<Bool> { return push([true], n > 0); }; x = flags(1);"
            , -- A builtin is used at its own element type each time
              parseValidProgramHelper "x = push([], push([], 1)); y = push([true], false);"
            , parseValidateFailProgramHelper "e = []; x = push(e, 1); y = push(e, push(e, 1));" "argument 2 of push: expected Int, got List<Int>"
            , parseValidProgramHelper "fn pair(a: Int, b: Int) -> List<List<Int>> { return push(push([], push([], a)), push([], b)); }; x = pair(1, 2);"
            , parseValidateFailProgramHelper "x = [1, true];" "list element: expected Int, got Bool"
            , parseValidateFailProgramHelper "x = [[1], 2];" "list element: expected List<Int>, got Int"
            , parseValidateFailProgramHelper "fn f(l: List<Bool>) -> Int { return first(l); };" "returned value: expected Int, got Bool"
            , parseValidateFailProgramHelper "x = push([true], 1);" "argument 2 of push: expected Bool, got Int"
            , -- Validation: elements of any type are terms, so contracts and foralls work on them
              parseValidProgramHelper "fn f(l: List<Bool>) -> Bool [{ affirm size(l) > 0; }] [{ affirm return = get(l, 0); }] { return first(l); };"
            , parseValidProgramHelper "l = [true, false]; affirm get(l, 1) = false; affirm size(l) = 2;"
            , parseValidProgramHelper "m = [[1, 2], [3]]; affirm size(get(m, 0)) = 2; affirm get(get(m, 0), 1) = 2;"
            , parseValidateFailProgramHelper "l = [true, false]; affirm get(l, 1) = true;" "Could not prove: get(l, 1) = true"
            , parseValidProgramHelper "fn f(m: List<List<Int>>) -> List<List<Int>> [{ affirm size(m) > 0; }] [{ affirm size(return) = size(m) + 1; affirm get(return, size(m)) = get(m, 0); }] { return push(m, first(m)); };"
            , parseValidProgramHelper "fn f(m: List<List<Int>>) -> List<List<Int>> [{ affirm size(m) > 0; affirm forall j in 0..size(m): size(get(m, j)) = 2; }] [{ affirm forall j in 0..size(return): size(get(return, j)) = 2; }] { return push(m, first(m)); };"
            ]

testStructs :: Test
testStructs =
    let node = "struct Node { value: Int, prev: Int, next: Int };"
        point = "struct Point { x: Int, y: Int };"
        ctor name fields = builtinFunct (Ctor name fields)
        field name = builtinFunct (Field Nothing name)
        fieldOf struct name = builtinFunct (Field (Just struct) name)
     in testCaseSeq
            "testStructs"
            [ -- Parsing: a literal is the application of the constructor, in declaration order
              case parseStatementBlock (point ++ "p = Point { y: 2, x: 1 };") of
                Right [_, Assign "p" expr] -> testAssertEq expr (F (Val (ctor "Point" ["x", "y"])) [Val (VInt 1), Val (VInt 2)])
                other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock (point ++ "q = Point { x: 5, ..p };") of
                Right [_, Assign "q" expr] -> testAssertEq expr (F (Val (ctor "Point" ["x", "y"])) [Val (VInt 5), F (Val (fieldOf "Point" "y")) [Var "p"]])
                other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock (point ++ "v = p.x + 1;") of
                Right [_, Assign "v" expr] -> testAssertEq expr (F (Val (builtinFunct Plus)) [F (Val (field "x")) [Var "p"], Val (VInt 1)])
                other -> Just ("Unexpected parse: " ++ show other)
            , parseEvalProgramHelper (point ++ "p = Point { x: 1, y: 2 }; return p.y;") (Just (VInt 2))
            , -- Chains of fields and ranges that use `..`
              parseEvalProgramHelper (point ++ "struct Line { from: Point, to: Point }; l = Line { from: Point { x: 1, y: 2 }, to: Point { x: 3, y: 4 } }; return l.to.x;") (Just (VInt 3))
            , parseValidProgramHelper "fn f(l: List<Int>, n: Int) -> Int [{ affirm forall j in 0..n: j < n; }] [{ }] { return n; };"
            , -- The base of an update has the struct's type, and an update must copy something
              parseValidateFailProgramHelper (point ++ "struct Other { x: Int, y: Int }; p = Point { x: 1, ..Other { x: 2, y: 3 } };") "base of an update of Point: expected Point, got Other"
            , parseValidateFailProgramHelper (point ++ "p = Point { x: 1, ..5 };") "base of an update of Point: expected Point, got Int"
            , parseFailsWith (point ++ "p = Point { x: 1, y: 2, ..p };") "copies nothing"
            , parseFailsWith "struct Int { x: Int };" "builtin type"
            , parseFailsWith "struct List { x: Int };" "builtin type"
            , -- Parse errors
              parseFailsWith (point ++ "p = Point { x: 1 };") "lacks field y"
            , parseFailsWith (point ++ "p = Point { x: 1, y: 2, z: 3 };") "has no field z"
            , parseFailsWith (point ++ "p = Point { x: 1, x: 2, y: 3 };") "repeats a field"
            , parseFailsWith "struct S { a: Int, a: Int };" "repeats a field"
            , -- Evaluation
              parseEvalProgramHelper (point ++ "p = Point { x: 1, y: 2 }; return p;") (Just (VData "Point" [("x", VInt 1), ("y", VInt 2)]))
            , parseEvalProgramHelper (point ++ "p = Point { x: 1, y: 2 }; q = Point { y: 9, ..p }; return q;") (Just (VData "Point" [("x", VInt 1), ("y", VInt 9)]))
            , parseEvalProgramHelper (point ++ "return Point { x: 1, y: 2 } = Point { y: 2, x: 1 };") (Just (VBool True))
            , parseEvalProgramHelper (point ++ "return Point { x: 1, y: 2 } = Point { x: 1, y: 3 };") (Just (VBool False))
            , parseEvalProgramHelper (point ++ "fn sum(p: Point) -> Int { return p.x + p.y; }; return sum(Point { x: 3, y: 4 });") (Just (VInt 7))
            , parseEvalProgramHelper (point ++ "l = push([], Point { x: 1, y: 2 }); return get(l, 0).y;") (Just (VInt 2))
            , -- Type checking
              parseValidateFailProgramHelper (point ++ "p = Point { x: true, y: 2 };") "field x of Point: expected Int, got Bool"
            , parseValidateFailProgramHelper (point ++ "p = Point { x: 1, y: 2 }; z = p.z;") "Point has no field z"
            , parseValidateFailProgramHelper "x = 1; y = x.f;" "is read from a Int"
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Int { return p; };") "returned value: expected Int, got Point"
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Int { return 1; }; x = f(3);") "argument 1 of f: expected Point, got Int"
            , parseValidateFailProgramHelper "fn f(p: Missing) -> Int { return 1; };" "unknown type Missing"
            , parseValidateFailProgramHelper (point ++ point) "Type already defined: Point"
            , parseValidateFailProgramHelper (point ++ "struct Other { x: Int, y: Int }; p = Point { x: 1, y: 2 }; o = Other { x: 1, y: 2 }; affirm p = o;") "expected Point, got Other"
            , parseValidateFailProgramHelper "struct S { a: Missing };" "unknown type Missing"
            , -- Validation: fields of a literal, updates and their frame
              parseValidProgramHelper (point ++ "p = Point { x: 1, y: 2 }; affirm p.x = 1; affirm p.y = 2;")
            , parseValidProgramHelper (point ++ "fn f(p: Point) -> Point [{ }] [{ affirm return.x = 5; affirm return.y = p.y; }] { return Point { x: 5, ..p }; };")
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Point [{ }] [{ affirm return.y = p.x; }] { return Point { x: 5, ..p }; };") "Could not prove: return.y = p.x"
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Point [{ }] [{ affirm return.x = p.x; }] { return Point { x: 5, ..p }; };") "Could not prove: return.x = p.x"
            , parseValidProgramHelper (point ++ "fn f(p: Point, q: Point) -> Int [{ affirm p = q; }] [{ affirm return = 0; }] { affirm p.x = q.x; return 0; };")
            , -- Two constructions that are equal agree field by field
              parseValidProgramHelper (point ++ "fn f(a: Int, b: Int, c: Int, d: Int) -> Int [{ affirm Point { x: a, y: b } = Point { x: c, y: d }; }] [{ }] { affirm a = c; affirm b = d; return 0; };")
            , parseValidateFailProgramHelper (point ++ "fn f(a: Int, b: Int, c: Int, d: Int) -> Int [{ affirm Point { x: a, y: b } = Point { x: c, y: d }; }] [{ }] { affirm a = d; return 0; };") "Could not prove: a = d"
            , parseValidateFailProgramHelper (point ++ "fn f(a: Int, b: Int, c: Int, d: Int) -> Int [{ }] [{ }] { affirm Point { x: a, y: b } = Point { x: c, y: d }; return 0; };") "Could not prove"
            , -- Known values
              parseValidProgramHelper (point ++ "p = Point { x: 1, y: 2 }; q = Point { y: 2, x: 1 }; affirm p = q;")
            , parseValidateFailProgramHelper (point ++ "p = Point { x: 1, y: 2 }; q = Point { x: 1, y: 3 }; affirm p = q;") "Could not prove: p = q"
            , -- Arithmetic reaches the fields
              parseValidProgramHelper (point ++ "fn f(p: Point) -> Int [{ affirm p.x > 0; }] [{ affirm return > 1; }] { return p.x + 1; };")
            , parseValidProgramHelper (node ++ "fn f(n: Node) -> Node [{ affirm n.next < 5; }] [{ affirm return.next < 6; }] { return Node { next: n.next + 1, ..n }; };")
            , -- Lists of structs
              parseValidProgramHelper (node ++ "fn f(nodes: List<Node>, i: Int) -> List<Node> [{ affirm i >= 0; affirm i < size(nodes); }] [{ affirm get(return, i).next = 5; affirm get(return, i).value = get(nodes, i).value; affirm forall j where j >= 0, j < size(nodes), j != i: get(return, j) = get(nodes, j); }] { return set(nodes, i, Node { next: 5, ..get(nodes, i) }); };")
            , parseValidateFailProgramHelper (node ++ "fn f(nodes: List<Node>, i: Int) -> List<Node> [{ affirm i >= 0; affirm i < size(nodes); }] [{ affirm get(return, i).prev = 5; }] { return set(nodes, i, Node { next: 5, ..get(nodes, i) }); };") "Could not prove: get(return, i).prev = 5"
            , parseValidProgramHelper (node ++ "fn f(nodes: List<Node>) -> List<Node> [{ }] [{ affirm size(return) = size(nodes) + 1; affirm get(return, size(nodes)).value = 7; }] { return push(nodes, Node { value: 7, prev: 0, next: 0 }); };")
            , -- Eta is not known: a struct is not equal to a rebuilt copy of its fields
              parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Int [{ }] [{ }] { affirm Point { x: p.x, y: p.y } = p; return 0; };") "Could not prove: Point { x: p.x, y: p.y } = p"
            ]
  where
    parseFailsWith source expected =
        case parseStatementBlock source of
            Left err -> if expected `isInfixOf` show err then Nothing else Just ("Wrong parse error: " ++ show err)
            Right _ -> Just ("Expected a parse error for: " ++ source)

testEnums :: Test
testEnums =
    let shape = "enum Shape { Circle { radius: Int }, Rect { width: Int, height: Int }, Empty };"
        opt = "enum Opt { None, Some { value: Int } };"
        tree = "enum Tree { Leaf, Branch { left: Tree, value: Int, right: Tree } };"
        parseFailsWith source expected =
            case parseStatementBlock source of
                Left err -> if expected `isInfixOf` show err then Nothing else Just ("Wrong parse error: " ++ show err)
                Right _ -> Just ("Expected a parse error for: " ++ source)
     in testCaseSeq
            "testEnums"
            [ -- Values
              parseEvalProgramHelper (shape ++ "return Shape::Circle { radius: 2 };") (Just (VData "Shape::Circle" [("radius", VInt 2)]))
            , parseEvalProgramHelper (shape ++ "return Shape::Empty;") (Just (VData "Shape::Empty" []))
            , parseEvalProgramHelper (shape ++ "return Shape::Empty = Shape::Empty;") (Just (VBool True))
            , parseEvalProgramHelper (shape ++ "return Shape::Empty = Shape::Circle { radius: 1 };") (Just (VBool False))
            , parseEvalProgramHelper (shape ++ "return Shape::Circle { radius: 1 } != Shape::Circle { radius: 2 };") (Just (VBool True))
            , -- is
              parseEvalProgramHelper (shape ++ "s = Shape::Rect { width: 1, height: 2 }; return s is Shape::Rect;") (Just (VBool True))
            , parseEvalProgramHelper (shape ++ "s = Shape::Rect { width: 1, height: 2 }; return s is Shape::Circle;") (Just (VBool False))
            , parseEvalProgramHelper (shape ++ "s = Shape::Empty; if s is Shape::Empty { return 1; } else { return 2; };") (Just (VInt 1))
            , -- match as a statement and after return or =
              parseEvalProgramHelper (shape ++ "s = Shape::Rect { width: 3, height: 4 }; total = 0; match s { Shape::Circle { radius: r } => { total = r; }, Shape::Rect { width: w, height: h } => { total = w * h; }, Shape::Empty => { }, }; return total;") (Just (VInt 12))
            , parseEvalProgramHelper (shape ++ "s = Shape::Circle { radius: 3 }; a = 0; a = match s { Shape::Circle { radius: r } => r * 2, Shape::Rect { width: w } => w, Shape::Empty => 0 }; return a;") (Just (VInt 6))
            , parseEvalProgramHelper (shape ++ "fn area(s: Shape) -> Int { return match s { Shape::Circle { radius: r } => r * r * 3, Shape::Rect { width: w, height: h } => w * h, Shape::Empty => 0 }; }; return area(Shape::Rect { width: 2, height: 5 });") (Just (VInt 10))
            , parseEvalProgramHelper (opt ++ "o = Opt::Some { value: 4 }; return match o { Opt::None => 0, Opt::Some { value: v } => v };") (Just (VInt 4))
            , -- A struct can be matched as the only variant of its type
              parseEvalProgramHelper "struct P { x: Int, y: Int }; p = P { x: 1, y: 2 }; return match p { P { y: b } => b };" (Just (VInt 2))
            , -- Recursive types
              parseEvalProgramHelper (tree ++ "fn sum(t: Tree) -> Int shrinks t { return match t { Tree::Leaf => 0, Tree::Branch { left: l, value: v, right: r } => v + sum(l) + sum(r) }; }; return sum(Tree::Branch { left: Tree::Branch { left: Tree::Leaf, value: 1, right: Tree::Leaf }, value: 2, right: Tree::Leaf });") (Just (VInt 3))
            , -- Parse errors
              parseFailsWith (shape ++ "s = Shape::Empty; match s { Shape::Empty => { } };") "does not cover Shape::Circle Shape::Rect"
            , parseFailsWith (shape ++ "s = Shape::Empty; match s { Shape::Empty => { }, Shape::Empty => { }, Shape::Circle { radius: r } => { }, Shape::Rect { width: w } => { } };") "repeats a variant"
            , parseFailsWith (shape ++ opt ++ "s = Shape::Empty; match s { Shape::Empty => { }, Opt::None => { } };") "arm of another type"
            , parseFailsWith (shape ++ "s = Shape::Empty; match s { Shape::Nope => { } };") "Unknown struct or variant Shape::Nope"
            , parseFailsWith (shape ++ "s = Shape::Circle { radius: 1 }; match s { Shape::Circle { diameter: d } => { }, Shape::Rect { width: w } => { }, Shape::Empty => { } };") "has no field diameter"
            , parseFailsWith (shape ++ "x = Shape::Circle { };") "lacks field radius"
            , parseFailsWith (shape ++ "x = Shape::Circle { radius: 1, ..y };") "copies nothing"
            , parseFailsWith (shape ++ "x = Shape::Empty is Shape::Nope;") "unexpected"
            , parseFailsWith "enum E { };" "has no variants"
            , parseFailsWith "enum E { A, A };" "repeats a variant"
            , parseFailsWith "enum Bool { A };" "builtin type"
            , -- Type checking
              parseValidateFailProgramHelper (shape ++ "x = Shape::Circle { radius: true };") "field radius of Shape::Circle: expected Int, got Bool"
            , parseValidateFailProgramHelper (shape ++ "fn f(s: Shape) -> Int { return s.radius; };") "cast the value to a variant first"
            , parseValidateFailProgramHelper (shape ++ opt ++ "x = Shape::Empty = Opt::None;") "expected Shape, got Opt"
            , parseValidateFailProgramHelper (shape ++ "x = 1 is Shape::Empty;") "expected Shape, got Int"
            , parseValidateFailProgramHelper (shape ++ shape) "Type already defined: Shape"
            , parseValidateFailProgramHelper (shape ++ "fn f(s: Shape) -> Bool { return s; };") "returned value: expected Bool, got Shape"
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Empty; match s { Shape::Circle { radius: r } => { x = r + true; }, Shape::Rect { width: w } => { }, Shape::Empty => { } };") "expected Int, got Bool"
            , -- Validation: the value's variant is known from where it was built
              parseValidProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s is Shape::Circle;")
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s is Shape::Rect;") "Could not prove: s is Shape::Rect"
            , parseValidProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s != Shape::Empty; affirm s != Shape::Circle { radius: 5 };")
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s != Shape::Circle { radius: 4 };") "Could not prove: s != Shape::Circle { radius: 4 }"
            , -- Only the arm of the known variant runs, so the join keeps its facts
              parseValidProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; total = 0; match s { Shape::Circle { radius: r } => { total = r; }, Shape::Rect { width: w, height: h } => { total = w; }, Shape::Empty => { } }; affirm total = 4;")
            , parseValidProgramHelper (shape ++ "s = Shape::Rect { width: 3, height: 5 }; total = 0; total = match s { Shape::Circle { radius: r } => r, Shape::Rect { width: w, height: h } => w + h, Shape::Empty => 0 }; affirm total = 8;")
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; total = 0; match s { Shape::Circle { radius: r } => { total = r; }, Shape::Rect { width: w, height: h } => { total = w; }, Shape::Empty => { } }; affirm total = 5;") "Could not prove: total = 5"
            , -- An unknown value: each arm is checked, and the arms' bindings are fields of the variant
              parseValidProgramHelper (shape ++ "fn area(s: Shape) -> Int [{ }] [{ }] { return match s { Shape::Circle { radius: r } => r, Shape::Rect { width: w, height: h } => w * h, Shape::Empty => 0 }; };")
            , parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ }] [{ affirm return = 1; }] { return match o { Opt::None => 1, Opt::Some { value: v } => 1 }; };")
            , parseValidateFailProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ }] [{ affirm return = 1; }] { return match o { Opt::None => 1, Opt::Some { value: v } => v }; };") "Could not prove: return = 1"
            , parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ affirm return = 7; }] { return match o { Opt::None => 1, Opt::Some { value: v } => 7 }; };")
            , parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ affirm o is Opt::None; }] [{ affirm return = 1; }] { return match o { Opt::None => 1, Opt::Some { value: v } => v }; };")
            , -- Contracts naming a variant
              parseValidProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; x = needsSome(Opt::Some { value: 2 });")
            , parseValidateFailProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; x = needsSome(Opt::None);") "Could not prove: o is Opt::Some"
            , parseValidateFailProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; fn caller(o: Opt) -> Int [{ }] [{ }] { return needsSome(o); };") "Could not prove: o is Opt::Some"
            , parseValidProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; fn caller(o: Opt) -> Int [{ }] [{ }] { if o is Opt::Some { return needsSome(o); } else { return 0; }; };")
            , -- Two variants of one value cannot both hold
              parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ affirm o is Opt::None; affirm o is Opt::Some; }] [{ affirm return = 9; }] { return 1; };")
            , -- What an arm binds or first assigns is local to the arm, whatever the number of variants
              parseValidateFailProgramHelper "struct P { x: Int }; p = P { x: 1 }; match p { P { x: a } => { local = a; } }; return local;" "Undefined variable: local"
            , parseEvalProgramFailHelper "struct P { x: Int }; p = P { x: 1 }; match p { P { x: a } => { local = a; } }; return local;" "Undefined variable: local"
            , parseValidateFailProgramHelper (opt ++ "o = Opt::None; match o { Opt::None => { local = 1; }, Opt::Some { value: v } => { local = v; } }; return local;") "Undefined variable: local"
            , parseValidateFailProgramHelper (opt ++ "o = Opt::None; match o { Opt::None => { }, Opt::Some { value: v } => { } }; return v;") "Undefined variable: v"
            , -- A pattern variable hides a variable of the same name instead of assigning it
              parseEvalProgramHelper (opt ++ "v = 99; o = Opt::Some { value: 4 }; match o { Opt::None => { }, Opt::Some { value: v } => { w = v; } }; return v;") (Just (VInt 99))
            , parseValidProgramHelper (opt ++ "v = 99; o = Opt::Some { value: 4 }; match o { Opt::None => { }, Opt::Some { value: v } => { w = v; } }; affirm v = 99;")
            , parseEvalProgramHelper "struct P { x: Int }; v = 99; p = P { x: 4 }; match p { P { x: v } => { } }; return v;" (Just (VInt 99))
            , parseValidProgramHelper (opt ++ "v = true; o = Opt::Some { value: 4 }; match o { Opt::None => { }, Opt::Some { value: v } => { w = v + 1; } }; affirm v = true;")
            , -- The scrutinee is read once, so a pattern variable named like it does not change later fields
              parseEvalProgramHelper (shape ++ "r = Shape::Rect { width: 3, height: 4 }; t = 0; match r { Shape::Circle { radius: x } => { }, Shape::Rect { width: r, height: h } => { t = r * 10 + h; }, Shape::Empty => { } }; return t;") (Just (VInt 34))
            , parseValidProgramHelper (shape ++ "r = Shape::Rect { width: 3, height: 4 }; t = 0; match r { Shape::Circle { radius: x } => { }, Shape::Rect { width: r, height: h } => { t = r * 10 + h; }, Shape::Empty => { } }; affirm t = 34;")
            , -- Enums in lists
              parseValidProgramHelper (opt ++ "l = push(push([], Opt::None), Opt::Some { value: 2 }); affirm get(l, 0) is Opt::None; affirm size(l) = 2;")
            , -- Recursive types
              parseValidProgramHelper (tree ++ "fn sum(t: Tree) -> Int [{ }] [{ }] shrinks t { return match t { Tree::Leaf => 0, Tree::Branch { left: l, value: v, right: r } => v + sum(l) + sum(r) }; }; x = sum(Tree::Leaf); affirm x = 0;")
            ]

testListProofs :: Test
testListProofs =
    let node = "struct Node { value: Int, prev: Int, next: Int };"
        nonNegative l = "affirm forall i in 0..size(" ++ l ++ "): get(" ++ l ++ ", i) >= 0;"
     in testCaseSeq
            "testListProofs"
            [ -- Case splits on the guards that block a forall: the index set by one update, then another
              parseValidProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = set(l, p, 5); out = set(out, q, 6); return out; };")
            , parseValidateFailProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = set(l, p, 5); out = set(out, q, 0 - 6); return out; };") "Could not prove: forall i in 0..size(return): get(return, i) >= 0"
            , -- The two updates may hit the same element, and the new element at the end is told apart too
              parseValidProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = push(l, 1); out = set(out, p, 5); out = set(out, q, 6); return out; };")
            , parseValidateFailProgramHelper ("fn f(l: List<Int>, p: Int, q: Int) -> List<Int> [{ affirm p >= 0; affirm p < size(l); affirm q >= 0; affirm q < size(l); " ++ nonNegative "l" ++ " }] [{ " ++ nonNegative "return" ++ " }] { out = push(l, 0 - 1); out = set(out, p, 5); out = set(out, q, 6); return out; };") "Could not prove: forall i in 0..size(return): get(return, i) >= 0"
            , -- Struct fields: the links stay in range through a push and two updates
              parseValidProgramHelper (node ++ "fn f(nodes: List<Node>, p: Int, v: Int) -> List<Node> [{ affirm size(nodes) > 0; affirm p >= 0; affirm p < size(nodes); affirm forall i in 0..size(nodes): get(nodes, i).next >= 0; affirm forall i in 0..size(nodes): get(nodes, i).next < size(nodes); }] [{ affirm forall i in 0..size(return): get(return, i).next >= 0; affirm forall i in 0..size(return): get(return, i).next < size(return); }] { q = get(nodes, p).next; n = size(nodes); out = push(nodes, Node { value: v, prev: p, next: q }); out = set(out, p, Node { next: n, ..get(out, p) }); out = set(out, q, Node { prev: n, ..get(out, q) }); return out; };")
            , parseValidateFailProgramHelper (node ++ "fn f(nodes: List<Node>, p: Int, v: Int) -> List<Node> [{ affirm size(nodes) > 0; affirm p >= 0; affirm p < size(nodes); affirm forall i in 0..size(nodes): get(nodes, i).next >= 0; affirm forall i in 0..size(nodes): get(nodes, i).next < size(nodes); }] [{ affirm forall i in 0..size(return): get(return, i).next < size(return); }] { q = get(nodes, p).next; n = size(nodes); out = push(nodes, Node { value: v, prev: p, next: n + 1 }); return out; };") "Could not prove: forall i in 0..size(return): get(return, i).next < size(return)"
            , -- A disequality is the same in both directions
              parseValidProgramHelper "fn f(a: Int, b: Int) -> Int [{ affirm a != b; }] [{ }] { affirm b != a; return 0; };"
            ]

testEnumCast :: Test
testEnumCast =
    let shape = "enum Shape { Circle { radius: Int }, Rect { width: Int, height: Int }, Empty };"
     in testCaseSeq
            "testEnumCast"
            [ -- Casting to a variant lets its fields be read, and is checked by the validator
              parseEvalProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; return (c as Shape::Circle).radius;") (Just (VInt 5))
            , parseEvalProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; return c as Shape::Circle;") (Just (VData "Shape::Circle" [("radius", VInt 5)]))
            , parseValidProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; affirm (c as Shape::Circle).radius = 5;")
            , parseValidProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ affirm s is Shape::Circle; }] [{ affirm return = (s as Shape::Circle).radius; }] { return (s as Shape::Circle).radius; };")
            , parseValidProgramHelper (shape ++ "fn area(s: Shape) -> Int [{ }] [{ }] { if s is Shape::Rect { return (s as Shape::Rect).width * (s as Shape::Rect).height; } else { return 0; }; };")
            , parseEvalProgramHelper (shape ++ "fn area(s: Shape) -> Int { if s is Shape::Rect { return (s as Shape::Rect).width * (s as Shape::Rect).height; } else { return 0; }; }; return area(Shape::Rect { width: 3, height: 4 });") (Just (VInt 12))
            , -- The cast without a proof is rejected
              parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ }] [{ }] { return (s as Shape::Circle).radius; };") "Could not prove: value is Shape::Circle"
            , parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ affirm s is Shape::Rect; }] [{ }] { return (s as Shape::Circle).radius; };") "Could not prove: value is Shape::Circle"
            , parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ }] [{ }] { if s is Shape::Circle { return 0; } else { return (s as Shape::Circle).radius; }; };") "Could not prove: value is Shape::Circle"
            , parseValidateFailProgramHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; k = r as Shape::Circle;") "Could not prove: value is Shape::Circle"
            , -- Running a wrong cast is undefined behaviour: the interpreter does not check it, and reading what is not there is an error
              parseEvalProgramHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; k = r as Shape::Circle; return 1;") (Just (VInt 1))
            , parseEvalProgramFailHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; return (r as Shape::Circle).radius;") "undefined behaviour"
            , -- A field of an enum is not read without a cast, whichever variants have it
              parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int { return s.radius; };") "cast the value to a variant first"
            , parseValidateFailProgramHelper ("enum E { A { size: Int }, B { size: Int } };" ++ "fn f(e: E) -> Int { return e.size; };") "cast the value to a variant first"
            , parseValidProgramHelper ("enum E { A { size: Int }, B { size: Int } };" ++ "fn f(e: E) -> Int [{ affirm e is E::B; }] [{ }] { return (e as E::B).size; };")
            , -- The variant's fields are checked, and the cast value is still a value of the enum
              parseValidateFailProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; k = (c as Shape::Circle).width;") "Shape::Circle has no field width"
            , parseValidateFailProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; b = (c as Shape::Circle).radius = true;") "expected Int, got Bool"
            , parseValidateFailProgramHelper (shape ++ "x = 1; y = x as Shape::Circle;") "expected Shape, got Int"
            , parseValidProgramHelper (shape ++ "fn id(s: Shape) -> Shape { return s; }; c = Shape::Circle { radius: 5 }; d = id(c as Shape::Circle);")
            , parseValidProgramHelper (shape ++ "fn r(c: Shape::Circle) -> Int { return c.radius; }; fn use(s: Shape) -> Int [{ affirm s is Shape::Circle; }] [{ }] { return r(s as Shape::Circle); }; x = use(Shape::Circle { radius: 9 });")
            , parseValidateFailProgramHelper (shape ++ "fn r(c: Shape::Circle) -> Int { return c.radius; }; x = r(Shape::Rect { width: 1, height: 2 });") "expected Shape::Circle, got Shape"
            , -- Updating a variant copies the fields it does not name from the base cast to that variant
              parseValidProgramHelper (shape ++ "fn grow(s: Shape) -> Shape [{ affirm s is Shape::Rect; }] [{ affirm return is Shape::Rect; affirm (return as Shape::Rect).height = (s as Shape::Rect).height; affirm (return as Shape::Rect).width = 10; }] { return Shape::Rect { width: 10, ..s }; };")
            , parseValidateFailProgramHelper (shape ++ "fn grow(s: Shape) -> Shape [{ }] [{ }] { return Shape::Rect { width: 10, ..s }; };") "Could not prove: value is Shape::Rect"
            , parseValidateFailProgramHelper (shape ++ "fn grow(s: Shape) -> Shape [{ affirm s is Shape::Rect; }] [{ affirm (return as Shape::Rect).height = 5; }] { return Shape::Rect { width: 10, ..s }; };") "Could not prove: (return as Shape::Rect).height = 5"
            , parseEvalProgramHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; return Shape::Rect { width: 7, ..r };") (Just (VData "Shape::Rect" [("width", VInt 7), ("height", VInt 2)]))
            , -- Structs read their fields directly
              parseEvalProgramHelper ("struct P { radius: Int };" ++ shape ++ "p = P { radius: 4 }; return p.radius;") (Just (VInt 4))
            ]

testCrlf :: Test
testCrlf =
    testCaseSeq
        "testCrlf"
        [ -- Programs checked out with Windows line endings parse the same, comments included
          parseEvalProgramHelper "x = 1; // note\r\n\r\nl = [1,\r\n 2];\r\nif x < 2 {\r\n  x = 3;\r\n};\r\nreturn x;\r\n" (Just (VInt 3))
        ]

testMulDivNegative :: Test
testMulDivNegative =
    testCaseSeq
        "testMulDivNegative"
        [ -- Evaluation: `*` and `/` bind tighter than the other infix operators, and `/` rounds down
          parseEvalProgramHelper "return 2 + 3 * 4;" (Just (VInt 14))
        , parseEvalProgramHelper "return 2 * 3 + 4 * 5 - 6 / 4;" (Just (VInt 25))
        , parseEvalProgramHelper "return 7 / 2 * 2;" (Just (VInt 6))
        , parseEvalProgramHelper "return (0 - 7) / 2;" (Just (VInt (-4)))
        , parseEvalProgramHelper "return -7 / 2;" (Just (VInt (-4)))
        , parseEvalProgramHelper "return 3 - -2;" (Just (VInt 5))
        , parseEvalProgramHelper "x = 4; return x-1;" (Just (VInt 3))
        , parseEvalProgramHelper "l = [-1, 2, -3]; return get(l, 2);" (Just (VInt (-3)))
        , parseEvalProgramFailHelper "return 1 / 0;" "Division by zero"
        , -- Validation: constants fold, `* 1` and `/ 1` keep their operand, other products are opaque
          parseValidProgramHelper "x = 3; y = x * 4; affirm y = 12; z = y / 5; affirm z = 2;"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n * 1; }; x = f(3);"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return = 0; }] { return n * 0; }; x = f(3);"
        , parseValidProgramHelper "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n * 2; }; x = f(3);"
        , parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return > 0; }] { return n * 2; }; x = f(3);" "Could not prove: return > 0"
        , parseValidateFailProgramHelper "x = 3; y = x + -1; affirm y = 3;" "Could not prove: y = 3"
        , -- Division needs a divisor known to be non-zero
          parseValidProgramHelper "fn f(a: Int, b: Int) -> Int [{ affirm b != 0; }] [{ }] { return a / b; }; x = f(8, 2);"
        , parseValidProgramHelper "fn f(a: Int, b: Int) -> Int [{ affirm b < 0; }] [{ }] { return a / b; }; x = f(8, -2);"
        , parseValidateFailProgramHelper "fn f(a: Int, b: Int) -> Int [{ }] [{ }] { return a / b; }; x = f(8, 2);" "Relation lacks a proof"
        , parseValidateFailProgramHelper "x = 3 / 0;" "Relation does not hold"
        , -- Proofs print with the same precedence
          parseValidateFailProgramHelper "x = 2; affirm x * (x + 1) = 5;" "Could not prove: x * (x + 1) = 5"
        ]

testPrettyProofs :: Test
testPrettyProofs =
    testCaseSeq
        "testPrettyProofs"
        [ -- Failed assertions are reported in source syntax rather than as a raw AST
          parseValidateFailProgramHelper "x = 1; affirm x < 4; affirm x = 2;" "Could not prove: x = 2"
        , parseValidateFailProgramHelper "l = [1, 2]; affirm size(l) + 1 = 4;" "Could not prove: size(l) + 1 = 4"
        , parseValidateFailProgramHelper "x = 1; affirm x - (1 - 1) != 1;" "Could not prove: x - (1 - 1) != 1"
        , parseValidateFailProgramHelper "l = [1, 2]; affirm forall j in 0..size(l): get(l, j) = 0;" "Could not prove: forall j in 0..size(l): get(l, j) = 0"
        , parseValidateFailProgramHelper "l = [1, 2]; affirm forall j where j > 0: get(l, j) = 0;" "Could not prove: forall j where j > 0: get(l, j) = 0"
        , case parseStatementBlock "l = [1]; affirm 1 = 2;" of
            Right stmts -> case validate stmts of
                Error e | "FApp" `isInfixOf` e || "VFunct" `isInfixOf` e -> Just $ "Raw AST in error: " ++ e
                _ -> Nothing
            Left err -> Just (show err)
        ]

testForallLoops :: Test
testForallLoops =
    let copyLoop invariant element = loopWith "get(a, j)" invariant element
        -- the output contract says every element of the result is `claim`
        loopWith claim invariant element =
            "fn copy(a: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(a); affirm forall j in 0..size(a): get(return, j) = " ++ claim ++ "; }] {\
            \  n = size(a); i = 0; out = [];\
            \  while i < n [{ affirm i >= 0; affirm i <= n; affirm size(out) = i; "
                ++ invariant
                ++ " }] shrinks n - i { out = push(out, "
                ++ element
                ++ "); i = i + 1; };\
                   \  return out; };"
        copyInvariant = "affirm forall j in 0..i: get(out, j) = get(a, j);"
     in testCaseSeq
            "testForallLoops"
            [ -- A list built element by element: the invariant covers the elements so far
              parseValidProgramHelper (copyLoop copyInvariant "get(a, i)")
            , parseValidProgramHelper (loopWith "(get(a, j) + 1)" "affirm forall j in 0..i: get(out, j) = (get(a, j) + 1);" "get(a, i) + 1")
            , -- Rejected: the element pushed is not the one the invariant claims
              parseValidateFailProgramHelper (copyLoop copyInvariant "get(a, i) + 1") "Loop invariant is not preserved"
            , parseValidateFailProgramHelper (loopWith "(get(a, j) + 1)" "affirm forall j in 0..i: get(out, j) = (get(a, j) + 1);" "get(a, i)") "Loop invariant is not preserved"
            , -- Rejected: the invariant covers one element too many on entry
              parseValidateFailProgramHelper (copyLoop "affirm forall j in 0..(i + 1): get(out, j) = get(a, j);" "get(a, i)") "Loop invariant does not hold on entry"
            , -- Without the forall in the invariant the output contract's forall cannot be proved
              parseValidateFailProgramHelper (copyLoop "" "get(a, i)") "Could not prove"
            , -- A call nested in an argument keeps its link to the caller's variables
              parseValidProgramHelper
                "fn g(l: List<Int>, i: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); }] [{ }] { y = push(l, get(l, i)); affirm get(y, size(l)) = get(l, i); return y; };"
            , parseValidateFailProgramHelper
                "fn g(l: List<Int>, i: Int, k: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); affirm k >= 0; affirm k < size(l); }] [{ }] { y = push(l, get(l, i)); affirm get(y, size(l)) = get(l, k); return y; };"
                "Could not prove"
            , parseValidProgramHelper
                "fn g(l: List<Int>, i: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); }] [{ }] { y = push(l, get(l, i) + 1); affirm get(y, size(l)) = (get(l, i) + 1); return y; };"
            , -- The elementwise contract reaches the caller
              parseValidProgramHelper
                ( copyLoop copyInvariant "get(a, i)"
                    ++ "b = [4, 5, 6]; c = copy(b); affirm get(c, 1) = get(b, 1); affirm forall j in 0..size(b): get(c, j) = get(b, j);"
                )
            ]

zeroAxiom :: String
zeroAxiom = "axiom zeros(l) [{ }] [{ affirm forall j in 0..size(l): get(l, j) = 0; }];"

testForallSyntax :: Test
testForallSyntax =
    let rel r a b = FApp (CTerm (builtinFunct (Rel r))) [a, b]
        getProof l t = FApp (CTerm (builtinFunct Get)) [l, t]
        parseAffirm source expected =
            case parseStatementBlock source of
                Left err -> Just $ "Parse failed: " ++ show err
                Right stmts -> testAssertEq stmts [ValidationStatement (ProofAssert expected)]
        parseFails source =
            case parseStatementBlock source of
                Left _ -> Nothing
                Right stmts -> Just $ "Expected a parse error, got: " ++ show stmts
        body = rel Eq (getProof (ATerm "l") (BVar "j")) (CTerm (VInt 0))
     in testCaseSeq
            "testForallSyntax"
            [ -- The range form is shorthand for a lower and an upper guard
              parseAffirm
                "affirm forall j in 0..n: get(l, j) = 0;"
                (Forall "j" [rel GtEq (BVar "j") (CTerm (VInt 0)), rel Lt (BVar "j") (ATerm "n")] body)
            , parseAffirm
                "affirm forall j where j >= 0, j < n: get(l, j) = 0;"
                (Forall "j" [rel GtEq (BVar "j") (CTerm (VInt 0)), rel Lt (BVar "j") (ATerm "n")] body)
            , -- The range bounds may be expressions, and the guards may use any relation
              parseAffirm
                "affirm forall j in 0..(n + 1): get(l, j) = 0;"
                ( Forall
                    "j"
                    [ rel GtEq (BVar "j") (CTerm (VInt 0))
                    , rel Lt (BVar "j") (FApp (CTerm (builtinFunct Plus)) [ATerm "n", CTerm (VInt 1)])
                    ]
                    body
                )
            , parseAffirm
                "affirm forall j where j != 2: get(l, j) = 0;"
                (Forall "j" [rel NotEq (BVar "j") (CTerm (VInt 2))] body)
            , -- Only the index is bound: other names stay ordinary variables
              parseAffirm
                "affirm forall k where k < j: get(l, k) = j;"
                ( Forall
                    "k"
                    [rel Lt (BVar "k") (ATerm "j")]
                    (rel Eq (getProof (ATerm "l") (BVar "k")) (ATerm "j"))
                )
            , -- It is allowed in contracts and invariants too
              case parseStatementBlock "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] { return l; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right _ -> Nothing
            , case parseStatementBlock "i = 0; while i < 3 [{ affirm forall j in 0..i: j < 3; }] { i = i + 1; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right _ -> Nothing
            , -- Malformed or unsupported forms
              parseFails "affirm forall j in 0..n get(l, j) = 0;"
            , parseFails "affirm forall j: get(l, j) = 0;"
            , parseFails "affirm forall in 0..n: 1 = 1;"
            , parseFails "affirm forall j in 0..n: forall k in 0..n: get(l, j) = get(l, k);"
            , -- A name that merely starts with forall is still an ordinary variable
              case parseStatementBlock "forallx = 1;" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right stmts -> testAssertEq stmts [Assign "forallx" (Val (VInt 1))]
            , -- Evaluation ignores validation statements, so a program with forall still runs
              parseEvalProgramHelper "affirm forall j in 0..2: j < 2; return 5;" (Just (VInt 5))
            , -- A forall that holds for every index in its range is accepted, and one that does not is rejected
              parseValidProgramHelper "affirm forall j in 0..3: j < 3;"
            , parseValidateFailProgramHelper "affirm forall j in 0..3: j < 2;" "Could not prove"
            , parseValidProgramHelper "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm forall j in 0..2: j < 2; }] { return l; };"
            , parseValidateFailProgramHelper "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm forall j in 0..3: j < 2; }] { return l; };" "Could not prove"
            , parseValidProgramHelper "i = 0; while i < 3 [{ affirm forall j in 0..i: j < 3; }] shrinks 3 - i { i = i + 1; };"
            , parseValidateFailProgramHelper "i = 0; while i < 3 [{ affirm forall j in 0..i: j < 2; }] shrinks 3 - i { i = i + 1; };" "Loop invariant is not preserved"
            , -- A forall assumed by an axiom is kept as a fact, and is entailed again when it is the same forall
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..size(a): get(a, j) = 0;")
            , -- The rule's argument is substituted into the forall
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; b = [0]; rewrite zeros a; rewrite zeros b; affirm forall j in 0..size(b): get(b, j) = 0;")
            , parseValidateFailProgramHelper (zeroAxiom ++ "a = [0, 0]; b = [0]; rewrite zeros a; affirm forall j in 0..size(b): get(b, j) = 0;") "Could not prove"
            , -- A range the fact does not cover, or another body, is not proved
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..1: get(a, j) = 0;")
            , parseValidateFailProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..3: get(a, j) = 0;") "Could not prove"
            , parseValidateFailProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall j in 0..size(a): get(a, j) = 1;") "Could not prove"
            , -- The name of the index does not matter
              parseValidProgramHelper (zeroAxiom ++ "a = [0, 0]; rewrite zeros a; affirm forall k in 0..size(a): get(a, k) = 0;")
            , -- Through a function: the input contract is checked at the call, and the output reaches the caller
              parseValidProgramHelper
                ( zeroAxiom
                    ++ "fn same(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] { return l; };\
                       \a = [0, 0]; rewrite zeros a; r = same(a); affirm forall j in 0..size(r): get(r, j) = 0;"
                )
            , parseValidateFailProgramHelper
                ( zeroAxiom
                    ++ "fn same(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ }] { return l; };\
                       \a = [0, 0]; r = same(a);"
                )
                "Could not prove"
            , -- A forall is not a rule argument
              parseValidateFailProgramHelper (zeroAxiom ++ "rewrite zeros forall j in 0..2: j < 2;") "cannot take a forall"
            , parseValidProgramHelper "x = 1; affirm x = 1;"
            ]

testLists :: Test
testLists =
    testCaseSeq
        "testLists"
        [ -- Evaluation
          parseEvalProgramHelper "return get([5, 6, 7], 0);" (Just (VInt 5))
        , parseEvalProgramHelper "a = [5, 6, 7]; i = 1 + 1; return get(a, i);" (Just (VInt 7))
        , parseEvalProgramHelper "return push([1, 2], 3);" (Just (VList [VInt 1, VInt 2, VInt 3]))
        , parseEvalProgramHelper "return push([], 4);" (Just (VList [VInt 4]))
        , parseEvalProgramHelper "return get(push(push([], 4), 9), 1);" (Just (VInt 9))
        , parseEvalProgramHelper "a = [1]; b = push(a, 2); return size(a) + size(b);" (Just (VInt 3))
        , parseEvalFailStmtHelper "{ return get([5], 1); }" "Get index out of range"
        , parseEvalFailStmtHelper "{ return get([5], 0 - 1); }" "Get index out of range"
        , parseEvalFailStmtHelper "{ return push(1, 2); }" "Push only valid"
        , parseEvalFailStmtHelper "{ return get(1, 0); }" "Get only valid"
        , parseEvalProgramHelper "return set([1, 2, 3], 1, 20);" (Just (VList [VInt 1, VInt 20, VInt 3]))
        , parseEvalProgramHelper "return set([1, 2, 3], 0, 9);" (Just (VList [VInt 9, VInt 2, VInt 3]))
        , parseEvalProgramHelper "return set([1, 2, 3], 2, 9);" (Just (VList [VInt 1, VInt 2, VInt 9]))
        , parseEvalProgramHelper "a = [1, 2, 3]; b = set(a, 0, 9); return first(a) + first(b);" (Just (VInt 10))
        , parseEvalProgramHelper "return set(push([1], 2), 1, 5);" (Just (VList [VInt 1, VInt 5]))
        , parseEvalFailStmtHelper "{ return set([5], 1, 0); }" "Set index out of range"
        , parseEvalFailStmtHelper "{ return set([5], 0 - 1, 0); }" "Set index out of range"
        , parseEvalFailStmtHelper "{ return set([], 0, 0); }" "Set index out of range"
        , parseEvalFailStmtHelper "{ return set(1, 0, 0); }" "Set only valid"
        , -- Frame facts: push's contract keeps the old elements, and nothing else is known
          parseValidProgramHelper "a = [1, 2]; b = push(a, 3); affirm get(b, 1) = get(a, 1);"
        , parseValidateFailProgramHelper "a = [1, 2]; b = push(a, 3); affirm get(b, 2) = get(a, 1);" "Could not prove"
        , -- Validation: a concrete list and index need no proof from the caller
          parseValidProgramHelper "a = [5, 6, 7]; x = get(a, 2); affirm x = 7;"
        , parseValidProgramHelper "a = push(push([], 1), 2); n = size(a); affirm n = 2;"
        , -- A symbolic index must be shown by the function's contract
          parseValidProgramHelper
            "fn at(l: List<Int>, i: Int) -> Int [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ }] { return get(l, i); }; return at([4, 5], 1);"
        , -- push's output contract reaches a caller that only knows the list symbolically
          parseValidProgramHelper
            "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = (size(l) + 1); }] { return push(l, 5); };"
        , parseValidProgramHelper
            "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = (size(l) + 1); }] { r = push(l, 5); return r; };"
        , -- set: a concrete list and index need no proof, and the result is as long as the input
          parseValidProgramHelper "a = [5, 6, 7]; b = set(a, 2, 0); affirm size(b) = size(a);"
        , parseValidProgramHelper
            "fn f(l: List<Int>, i: Int) -> List<Int> [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm size(return) = size(l); }] { return set(l, i, 5); };"
        , -- Element facts: set leaves x at the index and push leaves x at the old size
          parseValidProgramHelper "a = [1, 2, 3]; i = 1; b = set(a, i, 20); affirm get(b, i) = 20;"
        , parseValidProgramHelper "a = [1, 2, 3]; i = 1; v = 20; b = set(a, i, v); affirm get(b, i) = v;"
        , parseValidProgramHelper "l = [4, 5]; x = 9; r = push(l, x); define n = size(l); affirm get(r, n) = x;"
        , parseValidProgramHelper "l = [4, 5]; r = push(l, 9); define n = size(l); affirm get(r, n) = 9;"
        , parseValidProgramHelper
            "fn f(l: List<Int>, i: Int, x: Int) -> List<Int> [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm get(return, i) = x; }] { return set(l, i, x); }; r = f([1, 2, 3], 1, 7); affirm get(r, 1) = 7;"
        , parseValidProgramHelper
            "fn g(l: List<Int>, x: Int) -> List<Int> [{ }] [{ affirm get(return, size(l)) = x; }] { return push(l, x); };"
        , parseValidateFailProgramHelper "a = [1, 2, 3]; i = 1; b = set(a, i, 20); affirm get(b, i) = 21;" "Could not prove"
        , parseValidateFailProgramHelper "a = [1, 2, 3]; b = set(a, 1, 20); affirm get(b, 0) = 20;" "Could not prove"
        , -- set's contract keeps the other elements without a rule, and not the one it wrote
          parseValidProgramHelper "a = [1, 2, 3]; b = set(a, 1, 20); affirm get(b, 0) = get(a, 0); affirm get(b, 2) = get(a, 2);"
        , parseValidateFailProgramHelper "a = [1, 2, 3]; b = set(a, 1, 20); affirm get(b, 1) = get(a, 1);" "Could not prove"
        , -- With a symbolic list the elements are kept for any index in range, and only those
          parseValidProgramHelper
            "fn f(l: List<Int>, i: Int, j: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); affirm j >= 0; affirm j < size(l); affirm j != i; }] [{ affirm get(return, j) = get(l, j); }] { return set(l, i, 0); };"
        , parseValidateFailProgramHelper
            "fn f(l: List<Int>, i: Int, j: Int) -> List<Int> [{ affirm i >= 0; affirm i < size(l); affirm j >= 0; affirm j < size(l); }] [{ affirm get(return, j) = get(l, j); }] { return set(l, i, 0); };"
            "Could not prove"
        , parseValidProgramHelper
            "fn f(l: List<Int>, j: Int) -> List<Int> [{ affirm j >= 0; affirm j < size(l); }] [{ affirm get(return, j) = get(l, j); }] { return push(l, 7); };"
        , parseValidateFailProgramHelper
            "fn f(l: List<Int>, j: Int) -> List<Int> [{ affirm j >= 0; affirm j <= size(l); }] [{ affirm get(return, j) = get(l, j); }] { return push(l, 7); };"
            "Could not prove"
        , parseValidateFailProgramHelper "l = [4, 5]; r = push(l, 9); define n = size(l); affirm get(r, n) = 8;" "Could not prove"
        , parseValidateFailProgramHelper
            "fn f(l: List<Int>, i: Int, x: Int) -> List<Int> [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm get(return, i) = get(l, i); }] { return set(l, i, x); };"
            "Could not prove"
        , -- Rejected: out of range, unproven, or a wrong size claim
          parseValidateFailProgramHelper "a = [5, 6, 7]; b = set(a, 3, 0);" "Relation does not hold"
        , parseValidateFailProgramHelper "a = [5, 6, 7]; b = set(a, 0 - 1, 0);" "Relation does not hold"
        , parseValidateFailProgramHelper "fn f(l: List<Int>, i: Int) -> List<Int> { return set(l, i, 0); };" "Relation lacks a proof"
        , parseValidateFailProgramHelper
            "fn f(l: List<Int>, i: Int) -> List<Int> [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ affirm size(return) = (size(l) + 1); }] { return set(l, i, 5); };"
            "Could not prove"
        , -- get and the rest of the rejected cases
          parseValidateFailProgramHelper "a = [5, 6, 7]; x = get(a, 3);" "Relation does not hold"
        , parseValidateFailProgramHelper "a = [5, 6, 7]; x = get(a, 0 - 1);" "Relation does not hold"
        , parseValidateFailProgramHelper "a = []; x = get(a, 0);" "Relation does not hold"
        , parseValidateFailProgramHelper "fn at(l: List<Int>, i: Int) -> Int { return get(l, i); };" "Relation lacks a proof"
        , parseValidateFailProgramHelper
            "fn at(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; }] [{ }] { return get(l, i); };"
            "Relation lacks a proof"
        , parseValidateFailProgramHelper
            "fn f(l: List<Int>) -> List<Int> [{ }] [{ affirm size(return) = size(l); }] { return push(l, 5); };"
            "Could not prove"
        , parseValidateFailProgramHelper
            "fn f(l: List<Int>) -> List<Int> { r = push(l, 5); affirm size(r) = size(l); return r; };"
            "Could not prove"
        , -- checkRel: adds a relation only when it holds, and refuses anything else
          parseValidProgramHelper "x = 2; rewrite checkRel x < 3; affirm x < 3;"
        , parseValidateFailProgramHelper "x = 5; rewrite checkRel x < 3;" "Relation does not hold"
        , parseValidateFailProgramHelper "fn f(x: Int) -> Int { rewrite checkRel x < 3; return 1; };" "Relation lacks a proof"
        , parseValidateFailProgramHelper "x = 5; rewrite checkRel x;" "requires a relation"
        ]

testControlFlow :: Test
testControlFlow =
    TestList
        "testControlFlow"
        [testParseIf, testEvalIf, testValidateIf, testParseWhile, testEvalWhile, testValidateWhile, testEarlyReturn]

-- Run tests
-- A function over integers only
nativeInts :: Int -> [Statement] -> FunctBody
nativeInts n = NativeFunct (Signature (replicate n TInt) TInt) Nothing

main :: IO ()
main = do
    summary <-
        foldr combineSummaries (testSummary 0 0)
            <$> mapM
                (runTest [])
                [ testParse
                , testEvaluateFullContext
                , testParseEval
                , testValidateWithExpectedMatch
                , testValidateWithExpectedMismatch
                , testValidationFail
                , testUserRewriteValidation
                , testProofEngine
                , testParseVal
                , testParseValFail
                , testCrashRegression
                , testExamples
                , testCli
                , testControlFlow
                , testLists
                , testArithmetic
                , testForallSyntax
                , testForallInstantiation
                , testForallProof
                , testForallGrownList
                , testForallLoops
                , testPrettyProofs
                , testMulDivNegative
                , testCrlf
                , testEnumCast
                , testListProofs
                , testEnums
                , testStructs
                , testGenericLists
                , testTypeCheck
                , testRecursion
                , testSolverCache
                , testTermination
                , testRefinedArithmetic
                , testForLoops
                , testInferredInvariants
                , testPrecedence
                , testFirstLast
                , testFunctionCalls
                , testValidationFuel
                ]
    putStrLn $
        "Summary: "
            ++ show (summaryPassed summary)
            ++ " passed, "
            ++ show (summaryFailed summary)
            ++ " failed"
    when (summaryFailed summary > 0) exitFailure
