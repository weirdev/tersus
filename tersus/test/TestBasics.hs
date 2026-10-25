module TestBasics
    ( testParse
    , testParseEval
    , testCrashRegression
    , testFunctionCalls
    , testPrecedence
    , testFirstLast
    , testCrlf
    , testLists
    , testControlFlow
    ) where

import qualified Data.Map as Map
import Parse
import MirEval (fromMirValue)
import Pipeline (runStatements, validateStatements)
import StdLib
import TersusTypes
import Utils
import TestHarness

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

-- A function in a proof is a function of the program: a name that is not one is refused when the program is validated
testParseInvalidProofBuiltin :: Test
testParseInvalidProofBuiltin =
    testCase "testParseInvalidProofBuiltin" $
        parseValidateFailProgramHelper "x = 1; affirm bogus(x); return 0;" "Variable not found in proof map: bogus"

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
evalExprHelper :: Expression -> Value -> TestResult
evalExprHelper expr expected =
    case runStatements [Return expr] of
        Ok (Just val) -> testAssertEq (fromMirValue val) expected
        Ok Nothing -> Just "No value returned"
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
            Right (Block stmts) ->
                case runStatements stmts of
                    Ok (Just val) -> testAssertEq (fromMirValue val) expected
                    Ok Nothing -> Just "No value returned"
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
        (VFnRef "add1")

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
        \  fn getFirst(y: List<Int>) -> Int {\
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

parseEvalFailStmtHelper :: String -> String -> TestResult
parseEvalFailStmtHelper stmtStr expectedError =
    case parseStatement stmtStr of
        Left err -> Just $ "Parse failed: " ++ show err
        Right (Block stmts) ->
            testAssertErrorContains
                expectedError
                (runStatements stmts)
        Right _ -> Just "Not a block statement"

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
        "argument 1 of first: expected List<?>, got Int"

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
            case (validateStatements stmts, runStatements stmts) of
                (Error e, _) -> Just $ "Validation failed with error: " ++ e
                (_, Error e) -> Just $ "Evaluation failed with error: " ++ e
                (Ok _, Ok ret) -> testAssertEq (fmap fromMirValue ret) (Just (VInt 3))

testParseEvalUdfExtraArgsFail :: TestResult
testParseEvalUdfExtraArgsFail =
    parseEvalFailStmtHelper
        "{\
        \  fn f(a: List<Int>) -> List<Int> { return a; };\
        \  return f(1, 2);\
        \}"
        "f takes 1 arguments, got 2"

testParseEvalUdfMissingArgsFail :: TestResult
testParseEvalUdfMissingArgsFail =
    parseEvalFailStmtHelper
        "{\
        \  fn f(a: Int, b: Int) -> Int { return a; };\
        \  return f(1);\
        \}"
        "f takes 2 arguments, got 1"

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
        , parseEvalProgramFailHelper "if 5 { x = 1; };" "condition of if: expected Bool, got Int"
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
        , parseEvalProgramFailHelper "while 5 { x = 1; };" "condition of while: expected Bool, got Int"
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

testFunctionCalls :: Test
testFunctionCalls =
    let inc = "fn inc(n: Int) -> Int [{ }] [{ affirm return = (n + 1); }] { return n + 1; };"
        positive = "fn positive(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; affirm return = n; }] { return n; };"
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

testCrlf :: Test
testCrlf =
    testCaseSeq
        "testCrlf"
        [ -- Programs checked out with Windows line endings parse the same, comments included
          parseEvalProgramHelper "x = 1; // note\r\n\r\nl = [1,\r\n 2];\r\nif x < 2 {\r\n  x = 3;\r\n};\r\nreturn x;\r\n" (Just (VInt 3))
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
        , parseEvalFailStmtHelper "{ return push(1, 2); }" "argument 1 of push: expected List<?>, got Int"
        , parseEvalFailStmtHelper "{ return get(1, 0); }" "argument 1 of get: expected List<?>, got Int"
        , parseEvalProgramHelper "return set([1, 2, 3], 1, 20);" (Just (VList [VInt 1, VInt 20, VInt 3]))
        , parseEvalProgramHelper "return set([1, 2, 3], 0, 9);" (Just (VList [VInt 9, VInt 2, VInt 3]))
        , parseEvalProgramHelper "return set([1, 2, 3], 2, 9);" (Just (VList [VInt 1, VInt 2, VInt 9]))
        , parseEvalProgramHelper "a = [1, 2, 3]; b = set(a, 0, 9); return first(a) + first(b);" (Just (VInt 10))
        , parseEvalProgramHelper "return set(push([1], 2), 1, 5);" (Just (VList [VInt 1, VInt 5]))
        , parseEvalFailStmtHelper "{ return set([5], 1, 0); }" "Set index out of range"
        , parseEvalFailStmtHelper "{ return set([5], 0 - 1, 0); }" "Set index out of range"
        , parseEvalFailStmtHelper "{ return set([], 0, 0); }" "Set index out of range"
        , parseEvalFailStmtHelper "{ return set(1, 0, 0); }" "argument 1 of set: expected List<?>, got Int"
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
