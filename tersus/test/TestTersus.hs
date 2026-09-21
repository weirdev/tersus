module TestTersus (main) where

import qualified Control.Exception as Exception
import Control.Exception (SomeException, displayException, try)
import Control.Monad (when)
import qualified Data.Map as Map
import System.Exit (exitFailure)

import Cli
import Parse
import Proof
import qualified ProofEngine as Engine
import ProofHelpers
import StdLib
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
                        [ Assign "x" (F (Var "size") [Val (VIntList [5])])
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
        , case parseStatementBlock "x = [1, // one\n 2];\nfn f(a) [{ // in\n affirm a = 1; // out\n}] { // body\n return a; };" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertTrue (length parsed == 2)
        , case parseStatementBlock "x = 5; // y = 6;\n" of
            Left err -> Just $ "Parse failed: " ++ show err
            Right parsed -> testAssertEq parsed [Assign "x" (Val (VInt 5))]
        , case parseStatementBlock "x = 5 / 2" of
            Left _ -> Nothing
            Right parsed -> Just $ "Expected parse failure for a single slash, got: " ++ show parsed
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
        [ evalFCHelper [Assign "x" (F (Var "size") [Val (VIntList [5])])] [("x", VInt 1)]
        , evalFCHelper
            [ Assign "x" (F (Var "size") [Val (VIntList [5])])
            , Assign "y" (F (Val (builtinFunct Minus)) [Val (VInt 1), Val (VInt 1)])
            ]
            [("x", VInt 1), ("y", VInt 0)]
        , evalFCHelper
            [ Assign "f" (Val (VFunct [] [] [] (NativeFunct [Return (Val (VInt 3))]) []))
            , Assign "result" (F (Var "f") [])
            ]
            [("result", VInt 3), ("f", VFunct [] [] [] (NativeFunct [Return (Val (VInt 3))]) [])]
        , evalFCHelper
            [ Assign "f" (Val (VFunct [] [] [] (NativeFunct [Assign "y" (Val (VInt 2)), Return (Var "y")]) []))
            , Assign "result" (F (Var "f") [])
            ]
            [("result", VInt 2), ("f", VFunct [] [] [] (NativeFunct [Assign "y" (Val (VInt 2)), Return (Var "y")]) [])]
        , evalFCHelper
            [ Assign "id" (Val (VFunct ["v"] [] [] (NativeFunct [Return (Var "v")]) []))
            , Assign "result" (F (Var "id") [Val (VInt 7)])
            ]
            [("result", VInt 7), ("id", VFunct ["v"] [] [] (NativeFunct [Return (Var "v")]) [])]
        , evalFCHelper
            [ Assign "add" (Val (VFunct ["l", "r"] [] [] (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "l", Var "r"])]) []))
            , Assign "result" (F (Var "add") [Val (VInt 7), Val (VInt 13)])
            ]
            [("result", VInt 20), ("add", VFunct ["l", "r"] [] [] (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "l", Var "r"])]) [])]
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
        \  fn add1(i) {\
        \    return i + 1;\
        \  };\
        \  return add1;\
        \}"
        (VFunct ["i"] [] [] (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "i", Val (VInt 1)])]) [])

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
            [ Assign "x" (F (Val (builtinFunct Size)) [Val (VIntList [5])])
            ]
            [FApp eqVarProof [ATerm "x", CTerm (VInt 1)]]
        , validateWEMatchHelper
            [ Assign "x" (Val (VIntList [5, 4]))
            , Assign "y" (F (Val (builtinFunct Size)) [Var "x"])
            ]
            [ FApp eqVarProof [ATerm "x", CTerm (VIntList [5, 4])]
            , FApp eqVarProof [ATerm "y", CTerm (VInt 2)]
            ]
        , validateWEMatchHelper
            [ Assign "x" (F (Val (builtinFunct Size)) [Val (VIntList [5])])
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
            [ FApp eqVarProof [ATerm "x", CTerm (VInt 5)]
            , FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "x", CTerm (VInt 6)]
            ]
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
                    [Val (VIntList [5])]
                )
            ]
            [FApp eqVarProof [ATerm "y", CTerm (VInt 1)]]
        , validateWEMismatchHelper
            [ Assign "x" (Val (VIntList [5, 4]))
            , Assign "y" (F (Val (builtinFunct Size)) [Var "x"])
            ]
            [ FApp eqVarProof [ATerm "x", CTerm (VIntList [5, 4])]
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
                [ FApp eqProof [ATerm iotaList, CTerm (VIntList [1, 2])]
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
     in testAssertEq (Engine.entails goal context, Engine.entails ltGoal context) (True, False)

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
        \  fn add1(i) {\
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
                    (NativeFunct [Return (F (Val (builtinFunct Plus)) [Var "i", Val (VInt 1)])])
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
        \  fn sumFirstLast(lst) [{\
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
        \  fn getFirst(y) [{\
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
        \  fn add1(i) [{}] [{\
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
        \  fn getFirstWithSize(lst) [{\
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
        \  fn bad(lst) [{\
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
        \  fn bad(i) [{}] [{\
        \    affirm return = i;\
        \  }] {\
        \    return i + 1;\
        \  };\
        \}"

testParseValMissingExportedProofValidationFail :: TestResult
testParseValMissingExportedProofValidationFail =
    parseValFailStmtHelper
        "{\
        \  fn bad(lst) [{\
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
        "First requires a non-empty IntList"

testParseEvalLastEmptyFail :: TestResult
testParseEvalLastEmptyFail =
    parseEvalFailStmtHelper
        "{\
        \  return last([]);\
        \}"
        "Last requires a non-empty IntList"

testParseEvalFirstWrongTypeFail :: TestResult
testParseEvalFirstWrongTypeFail =
    parseEvalFailStmtHelper
        "{\
        \  return first(1);\
        \}"
        "First only valid for IntList"

-- The LANGUAGE.md "Argument Passing" example: the callee's reassignment of a parameter
-- must not reach the caller's variable, in evaluation or after validation.
argPassingSource :: String
argPassingSource =
    "fn reset(xs) { xs = []; return size(xs); };\
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
        \  fn f(a) { return a; };\
        \  return f(1, 2);\
        \}"
        "expected 1 arguments, got 2"

testParseEvalUdfMissingArgsFail :: TestResult
testParseEvalUdfMissingArgsFail =
    parseEvalFailStmtHelper
        "{\
        \  fn f(a, b) { return a; };\
        \  return f(1);\
        \}"
        "expected 2 arguments, got 1"

testParseValUdfExtraArgsFail :: TestResult
testParseValUdfExtraArgsFail =
    parseValFailStmtHelper
        "{\
        \  fn f(a) { return a; };\
        \  return f(1, 2);\
        \}"

testParseValUdfMissingArgsFail :: TestResult
testParseValUdfMissingArgsFail =
    parseValFailStmtHelper
        "{\
        \  fn f(a, b) { return a; };\
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
        , testExampleFile "examples/loops.tersus" (ExpectReturn (VInt 30))
        , testExampleFile "examples/early_return.tersus" (ExpectReturn (VInt 104))
        , testExampleFile "examples/loop_return.tersus" (ExpectReturn (VInt 7))
        , testExampleFile "examples/parallel_sum.tersus" (ExpectReturn (VIntList [11, 22, 33]))
        , testExampleFile "examples/build_list.tersus" (ExpectReturn (VIntList [2, 4, 6]))
        , testExampleFile "examples/rejected/get_out_of_range.tersus" (ExpectRejected "Relation does not hold")
        , testExampleFile "examples/rejected/get_unproven_index.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/parallel_length.tersus" (ExpectRejected "Relation lacks a proof")
        , testExampleFile "examples/rejected/push_size.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/invariant_entry.tersus" (ExpectRejected "Loop invariant does not hold on entry")
        , testExampleFile "examples/rejected/invariant_preserved.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/loop_stale_fact.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/loop_return_invariant.tersus" (ExpectRejected "Loop invariant is not preserved")
        , testExampleFile "examples/rejected/loop_missing_return.tersus" (ExpectRejected "Return value not found")
        , testExampleFile "examples/rejected/unguarded_access.tersus" (ExpectRejected "lacks concrete definition")
        , testExampleFile "examples/rejected/branch_fact.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/guard_condition.tersus" (ExpectRejected "lacks concrete definition")
        , testExampleFile "examples/rejected/missing_return.tersus" (ExpectRejected "Return value not found")
        , testExampleFile "examples/rejected/affirm.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/first_of_empty.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/unmet_contract.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/missing_contract.tersus" (ExpectRejected "lacks concrete definition")
        , testExampleFile "examples/rejected/output_contract.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/bad_proof_rule.tersus" (ExpectRejected "Assertion failed")
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
        (map renderValue [VInt 5, VIntList [], VIntList [1, 2], VBool True, VBool False])
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
            "fn firstOr(lst, d) {\
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
            "fn f(n) {\
            \  y = 0;\
            \  if n < 6 { y = 1; rewrite eqToGtZero y; } else { y = 2; rewrite eqToGtZero y; };\
            \  affirm y > 0;\
            \  return y;\
            \};"
        , -- The same guard without enough information is rejected
          parseValidateFailProgramHelper
            "fn firstOr(lst, d) {\
            \  r = d;\
            \  if size(lst) > 1 {\
            \    r = first(lst);\
            \  };\
            \  return r;\
            \};\
            \return firstOr([4, 8], 0);"
            "lacks concrete definition"
        , -- A fact only one branch establishes does not survive the join
          parseValidateFailProgramHelper
            "fn f(n) {\
            \  y = 0;\
            \  if n < 6 { y = 1; rewrite eqToGtZero y; } else { y = 2; };\
            \  affirm y > 0;\
            \};"
            "Assertion failed"
        , -- Soundness: the condition only holds inside its branch
          parseValidateFailProgramHelper
            "fn f(n) {\
            \  y = 0;\
            \  if n < 6 { y = 1; } else { y = 2; };\
            \  affirm n < 6;\
            \};"
            "Assertion failed"
        , -- Soundness: a copy made under the condition must not carry the condition out
          parseValidateFailProgramHelper
            "fn f(n) {\
            \  y = 0;\
            \  if n < 6 { y = n; } else { y = 0; };\
            \  affirm y < 6;\
            \};"
            "Assertion failed"
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
                Right parsed -> testAssertEq parsed [While lt3 [] [inc]]
            , case parseStatementBlock "while i < 3 [{ affirm i <= 3; }] { i = i + 1; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right parsed -> testAssertEq parsed [While lt3 [leProof] [inc]]
            , -- The condition may call functions, and the invariant may hold several statements
              case parseStatementBlock "while size(xs) > 0 [{ define s = size(xs); affirm s > 0; }] { xs = [1]; };" of
                Left err -> Just $ "Parse failed: " ++ show err
                Right [While _ inv _] -> testAssertEq (length inv) 2
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
                   \while i < 3 [{ affirm i <= 3; }] { rewrite stepWithinBound i; i = i + 1; };\
                   \affirm i <= 3; affirm i >= 3;"
            )
        , -- Without an invariant the loop still validates, it just proves nothing about i afterwards
          parseValidProgramHelper "i = 0; n = 0; while i < 3 { i = i + 1; n = n + 2; };"
        , -- A loop nested in a function body
          parseValidProgramHelper
            ( loopAxioms
                ++ "fn f(k) { i = 0; rewrite zeroWithinBound i;\
                   \  while i < 3 [{ affirm i <= 3; }] { rewrite stepWithinBound i; i = i + 1; };\
                   \  return i; };\
                   \return f(1);"
            )
        , parseValidateFailProgramHelper
            ( loopAxioms
                ++ "i = 5; while i < 3 [{ affirm i <= 3; }] { rewrite stepWithinBound i; i = i + 1; };"
            )
            "Loop invariant does not hold on entry"
        , parseValidateFailProgramHelper
            ( loopAxioms
                ++ "i = 0; rewrite zeroWithinBound i; while i < 3 [{ affirm i <= 3; }] { i = i + 1; };"
            )
            "Loop invariant is not preserved"
        , -- Soundness: what was known about i before the loop says nothing about i after it
          parseValidateFailProgramHelper "i = 0; while i < 3 { i = i + 1; }; affirm i = 0;" "Assertion failed"
        , -- Soundness: the loop condition does not hold once the loop is done
          parseValidateFailProgramHelper
            ( loopAxioms
                ++ "i = 0; rewrite zeroWithinBound i;\
                   \while i < 3 [{ affirm i <= 3; }] { rewrite stepWithinBound i; i = i + 1; };\
                   \affirm i < 3;"
            )
            "Assertion failed"
        , -- A loop whose body returns is validated too
          parseValidProgramHelper "i = 0; while i < 3 { return i; }; return 9;"
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
            "fn f(n) { if n < 1 { return 0; }; return n + 10; }; return f(0) + f(5);"
            (Just (VInt 15))
        , -- Returning from inside a loop stops the loop
          parseEvalProgramHelper "i = 0; while i < 10 { if i > 2 { return i; }; i = i + 1; }; return 99;" (Just (VInt 3))
        , -- Statements after the return never run
          parseEvalProgramHelper "return 1; x = first([]);" (Just (VInt 1))
        , -- Validation: a guard clause makes the rest of the function safe
          parseValidProgramHelper
            "fn firstOr(lst, d) { if size(lst) > 0 { } else { return d; }; define s = size(lst); rewrite eqToGtZero s; return first(lst); }; return firstOr([4, 8], 0) + firstOr([], 5);"
        , -- A return inside the taken branch
          parseValidProgramHelper
            "fn firstOr(lst, d) { if size(lst) > 0 { define s = size(lst); rewrite eqToGtZero s; return first(lst); }; return d; };"
        , -- A chain of guard clauses
          parseValidProgramHelper
            "fn sign(n) { if n < 0 { return 0 - 1; }; if n > 0 { return 1; }; return 0; }; return sign(3);"
        , -- A program may return on only some paths
          parseValidProgramHelper "x = 1; if x < 2 { return 1; };"
        , -- Every return can establish an output fact
          parseValidProgramHelper
            "fn f(n) [{ }] [{ affirm return > 0; }] { if n < 6 { y = 1; rewrite eqToGtZero y; return y; }; z = 2; rewrite eqToGtZero z; return z; }; r = f(3); affirm r > 0;"
        , -- Rejected: the guard only helps on the path where it did not return
          parseValidateFailProgramHelper
            "fn f(lst, d) { if size(lst) > 0 { return d; }; return first(lst); };"
            "lacks concrete definition"
        , parseValidateFailProgramHelper
            "fn f(lst, d) { if size(lst) > 1 { } else { return d; }; return first(lst); };"
            "lacks concrete definition"
        , -- Soundness: the return branch's condition is not known afterwards
          parseValidateFailProgramHelper
            "fn f(n) { if n < 6 { return 1; }; affirm n < 6; return 2; };"
            "Assertion failed"
        , -- Soundness: a fact only one return establishes is not an output fact
          parseValidateFailProgramHelper
            "fn f(n) [{ }] [{ affirm return > 0; }] { if n < 6 { y = 1; rewrite eqToGtZero y; return y; }; return 0; };"
            "Assertion failed"
        , -- A function where some path does not return has no return value
          parseValidateFailProgramHelper "fn f(n) { if n < 6 { return 1; }; }; x = f(1);" "Return value not found"
        , -- Returning from inside a loop stops it
          parseValidProgramHelper "fn f(n) { i = 0; while i < 3 { if i > n { return i; }; i = i + 1; }; return 0; }; x = f(1);"
        , parseEvalProgramHelper "fn f(n) { i = 0; while i < 5 { if i > n { return i; }; i = i + 1; }; return 0; }; return f(2) + f(9);" (Just (VInt 3))
        , -- The invariant is checked on the paths that keep looping, and holds for the return too
          parseValidProgramHelper
            ( loopAxioms
                ++ "fn f(n) [{ }] [{ affirm return <= 3; }] { i = 0; rewrite zeroWithinBound i;\
                   \ while i < 3 [{ affirm i <= 3; }] { if i > n { return i; }; rewrite stepWithinBound i; i = i + 1; };\
                   \ affirm i >= 3; return i; }; x = f(1);"
            )
        , parseValidateFailProgramHelper
            ( loopAxioms
                ++ "fn f(n) { i = 0; rewrite zeroWithinBound i;\
                   \ while i < 3 [{ affirm i <= 3; }] { if i > n { return i; }; i = i + 1; };\
                   \ return i; };"
            )
            "Loop invariant is not preserved"
        , -- Soundness: the returning path's condition is not known after the loop
          parseValidateFailProgramHelper
            "fn f(n) { i = 0; while i < 3 { if n > 5 { return 1; }; i = i + 1; }; affirm n > 5; return 0; };"
            "Assertion failed"
        , -- Soundness: only the path after the loop knows the loop condition is false
          parseValidateFailProgramHelper
            "fn f(n) { i = 0; while i < 3 { if n > 5 { return 1; }; i = i + 1; }; affirm i < 3; return 0; };"
            "Assertion failed"
        , -- Soundness: a fact only the returning path establishes is not an output fact
          parseValidateFailProgramHelper
            ( loopAxioms
                ++ "fn f(n) [{ }] [{ affirm return <= 3; }] { i = 0; rewrite zeroWithinBound i;\
                   \ while i < 3 [{ affirm i <= 3; }] { if i > n { return i; }; rewrite stepWithinBound i; i = i + 1; };\
                   \ return 100; };"
            )
            "Assertion failed"
        , parseValidateFailProgramHelper "fn f(n) { i = 0; while i < n { return i; }; }; x = f(1);" "Return value not found"
        , -- A nested loop that returns
          parseValidProgramHelper
            "fn f(n) { i = 0; while i < 2 { j = 0; while j < 2 { if j > n { return j; }; j = j + 1; }; i = i + 1; }; return 0; }; x = f(1);"
        ]

testLists :: Test
testLists =
    testCaseSeq
        "testLists"
        [ -- Evaluation
          parseEvalProgramHelper "return get([5, 6, 7], 0);" (Just (VInt 5))
        , parseEvalProgramHelper "a = [5, 6, 7]; i = 1 + 1; return get(a, i);" (Just (VInt 7))
        , parseEvalProgramHelper "return push([1, 2], 3);" (Just (VIntList [1, 2, 3]))
        , parseEvalProgramHelper "return push([], 4);" (Just (VIntList [4]))
        , parseEvalProgramHelper "return get(push(push([], 4), 9), 1);" (Just (VInt 9))
        , parseEvalProgramHelper "a = [1]; b = push(a, 2); return size(a) + size(b);" (Just (VInt 3))
        , parseEvalFailStmtHelper "{ return get([5], 1); }" "Get index out of range"
        , parseEvalFailStmtHelper "{ return get([5], 0 - 1); }" "Get index out of range"
        , parseEvalFailStmtHelper "{ return push([1], [2]); }" "Push only valid"
        , parseEvalFailStmtHelper "{ return get(1, 0); }" "Get only valid"
        , -- Validation: a concrete list and index need no proof from the caller
          parseValidProgramHelper "a = [5, 6, 7]; x = get(a, 2); affirm x = 7;"
        , parseValidProgramHelper "a = push(push([], 1), 2); n = size(a); affirm n = 2;"
        , -- A symbolic index must be shown by the function's contract
          parseValidProgramHelper
            "fn at(l, i) [{ rewrite checkRel i >= 0; rewrite checkRel i < size(l); affirm i >= 0; affirm i < size(l); }] [{ }] { return get(l, i); }; return at([4, 5], 1);"
        , -- push's output contract reaches a caller that only knows the list symbolically
          parseValidProgramHelper
            "fn f(l) [{ }] [{ affirm size(return) = (size(l) + 1); }] { return push(l, 5); };"
        , parseValidProgramHelper
            "fn f(l) [{ }] [{ affirm size(return) = (size(l) + 1); }] { r = push(l, 5); return r; };"
        , -- Rejected: out of range, unproven, or a wrong size claim
          parseValidateFailProgramHelper "a = [5, 6, 7]; x = get(a, 3);" "Relation does not hold"
        , parseValidateFailProgramHelper "a = [5, 6, 7]; x = get(a, 0 - 1);" "Relation does not hold"
        , parseValidateFailProgramHelper "a = []; x = get(a, 0);" "Relation does not hold"
        , parseValidateFailProgramHelper "fn at(l, i) { return get(l, i); };" "Relation lacks a proof"
        , parseValidateFailProgramHelper
            "fn at(l, i) [{ affirm i >= 0; }] [{ }] { return get(l, i); };"
            "Relation lacks a proof"
        , parseValidateFailProgramHelper
            "fn f(l) [{ }] [{ affirm size(return) = size(l); }] { return push(l, 5); };"
            "Assertion failed"
        , parseValidateFailProgramHelper
            "fn f(l) { r = push(l, 5); affirm size(r) = size(l); return r; };"
            "Assertion failed"
        , -- checkRel: adds a relation only when it holds, and refuses anything else
          parseValidProgramHelper "x = 2; rewrite checkRel x < 3; affirm x < 3;"
        , parseValidateFailProgramHelper "x = 5; rewrite checkRel x < 3;" "Relation does not hold"
        , parseValidateFailProgramHelper "fn f(x) { rewrite checkRel x < 3; return 1; };" "Relation lacks a proof"
        , parseValidateFailProgramHelper "x = 5; rewrite checkRel x;" "requires a relation"
        ]

testControlFlow :: Test
testControlFlow =
    TestList
        "testControlFlow"
        [testParseIf, testEvalIf, testValidateIf, testParseWhile, testEvalWhile, testValidateWhile, testEarlyReturn]

-- Run tests
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
                ]
    putStrLn $
        "Summary: "
            ++ show (summaryPassed summary)
            ++ " passed, "
            ++ show (summaryFailed summary)
            ++ " failed"
    when (summaryFailed summary > 0) exitFailure
