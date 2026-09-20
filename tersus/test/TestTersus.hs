module TestTersus (main) where

import qualified Control.Exception as Exception
import Control.Exception (SomeException, displayException, try)
import Control.Monad (when)
import qualified Data.Map as Map
import System.Exit (exitFailure)

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

testParse :: Test
testParse =
    TestList
        "testParse"
        [ testParseSimpleAssign
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

testProofEngine :: Test
testProofEngine =
    testCaseSeq
        "testProofEngine"
        [ testProofEngineInsertDedupes
        , testProofEngineEntailsDenseEqualitiesTerminates
        , testProofEngineEntailsEquivalentTerms
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

testCrashRegression :: Test
testCrashRegression =
    testCaseSeq
        "testCrashRegression"
        [ testParseEvalFirstEmptyFail
        , testParseEvalLastEmptyFail
        , testParseEvalFirstWrongTypeFail
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
        , testExampleFile "examples/rejected/affirm.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/first_of_empty.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/unmet_contract.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/missing_contract.tersus" (ExpectRejected "lacks concrete definition")
        , testExampleFile "examples/rejected/output_contract.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/bad_proof_rule.tersus" (ExpectRejected "Assertion failed")
        , testExampleFile "examples/rejected/axiom_input.tersus" (ExpectRejected "is not greater than 0")
        , testExampleFile "examples/rejected/unknown_rule.tersus" (ExpectRejected "Unknown rewrite rule")
        ]

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
                ]
    putStrLn $
        "Summary: "
            ++ show (summaryPassed summary)
            ++ " passed, "
            ++ show (summaryFailed summary)
            ++ " failed"
    when (summaryFailed summary > 0) exitFailure
