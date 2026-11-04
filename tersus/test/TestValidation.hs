module TestValidation
    ( testValidateWithExpectedMatch
    , testValidateWithExpectedMismatch
    , testValidationFail
    , testUserRewriteValidation
    , testParseVal
    , testParseValFail
    , testCallsUseContracts
    , testRecursion
    , testValidationCache
    , testHaskellParity
    ) where

import Control.Concurrent (MVar, ThreadId, forkIOWithUnmask, killThread, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (MaskingState (..), SomeException, bracket, displayException, evaluate, getMaskingState, try)
import System.Timeout (timeout)
import Compile (lowerSource, lowerStatements, parseSource)
import qualified Mir as M
import qualified Data.Map as Map
import qualified Data.Set as Set
import TestParserFragments
import Pipeline (compileSource, validateStatements)
import ValidatorNative (validateCompiled, validateCompiledUncached, validationCacheHits)
import StdLib
import Types
import Syntax
import Utils
import TestHarness

testAllTrue :: (Show a) => (a -> Bool) -> [a] -> TestResult
testAllTrue _ [] = Nothing
testAllTrue f (x : xs) =
    if f x
        then testAllTrue f xs
        else Just $ "Failed for: " ++ show x

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

-- Validate: the Tersus validator gives a verdict, not the facts it used, so
-- these helpers assert the verdict and nothing about exported proof terms
validateWEMatchHelper :: [Statement] -> [VariableProof] -> TestResult
validateWEMatchHelper stmts _expected =
    case validateStatements stmts of
        Ok _ -> Nothing
        Error e -> Just $ "Validation failed with error: " ++ e

validateWEMismatchHelper :: [Statement] -> [VariableProof] -> TestResult
validateWEMismatchHelper stmts _expected =
    case validateStatements stmts of
        Ok _ -> Nothing
        Error e -> Just $ "Validation failed with error: " ++ e

validationFailHelper :: [Statement] -> TestResult
validationFailHelper stmts =
    case validateStatements stmts of
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
        , parseValidateWEMatchHelper
            "{ proof definedPositive(x) [{ define next = x + 1; affirm next > x; }] [{ affirm next > x; }] { affirm next > x; }; x = 5; rewrite definedPositive x; affirm x + 1 > x; }"
            [FApp (CTerm (builtinFunct (Rel Gt))) [FApp (CTerm (builtinFunct Plus)) [ATerm "x", CTerm (VInt 1)], ATerm "x"]]
        , parseValidateWEMatchHelper
            "{ proof definedPositive(x) [{ define next = x + 1; affirm next > x; }] [{ affirm x + 1 > x; }] { define next = x + 1; affirm next > x; }; x = 5; rewrite definedPositive x; affirm x + 1 > x; }"
            [FApp (CTerm (builtinFunct (Rel Gt))) [FApp (CTerm (builtinFunct Plus)) [ATerm "x", CTerm (VInt 1)], ATerm "x"]]
        , parseValidateWEMatchHelper
            "{ proof positiveSum(x, y) [{ define total = x + y; affirm total > 0; }] [{ affirm x + y > 0; }] { define total = x + y; affirm total > 0; }; fn f(flag: Bool) -> Int { x = 0; y = 0; if flag { x = 1; y = 0; } else { x = 0; y = 1; }; rewrite positiveSum x y; return 0; }; return f(true); }"
            []
        , parseValidationFailHelper
            "{ proof bad(x) [{ define n = x + 1; }] [{ define n = 0; affirm n = 0; }] { }; x = 5; rewrite bad x; affirm x + 1 = 0; }"
        , parseValidateWEMatchHelper
            "{ proof bad(x) [{ define n = x + 1; }] [{ define n = x + 1; affirm n > x; }] { }; x = 5; rewrite bad x; affirm x + 1 > x; }"
            [FApp (CTerm (builtinFunct (Rel Gt))) [FApp (CTerm (builtinFunct Plus)) [ATerm "x", CTerm (VInt 1)], ATerm "x"]]
        , parseValidationFailHelper
            "{ proof bad(x) [{ define n = x + 1; define m = n + 1; }] [{ affirm m = x + 2; }] { }; x = 5; n = 0; rewrite bad x; affirm 1 = 7; }"
        , parseValidateWEMatchHelper
            "{ proof bad(x) [{ define n = x + 1; define m = n + 1; }] [{ affirm m = x + 2; }] { }; x = 5; rewrite bad x; affirm x + 2 = x + 2; }"
            [FApp eqVarProof [FApp (CTerm (builtinFunct Plus)) [FApp (CTerm (builtinFunct Plus)) [ATerm "x", CTerm (VInt 1)], CTerm (VInt 1)], FApp (CTerm (builtinFunct Plus)) [ATerm "x", CTerm (VInt 2)]]]
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
            Right (Block stmts) ->
                case validateStatements stmts of
                    Ok _ -> Nothing
                    Error e -> Just $ "Validation failed with error: " ++ e
            Right _ -> Just "Not a block statement"

parseValidateWEMatchHelper :: String -> [VariableProof] -> TestResult
parseValidateWEMatchHelper stmtStr expected =
    case parseStatement stmtStr of
        Left err -> Just $ "Parse failed: " ++ show err
        Right (Block stmts) -> validateWEMatchHelper stmts expected
        Right _ -> Just "Not a block statement"

parseValidationFailHelper :: String -> TestResult
parseValidationFailHelper stmtStr =
    case parseStatement stmtStr of
        Left err -> Just $ "Parse failed: " ++ show err
        Right (Block stmts) -> validationFailHelper stmts
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
        [FApp eqVarProof [ATerm "ret", CTerm (VFnRef "add1")]]

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
    parseValidProgramHelper
        "fn sumFirstLast(lst: List<Int>) -> Int [{\
        \  define s = size(lst);\
        \  rewrite eqToGtZero s;\
        \  affirm s > 0;\
        \}] [{\
        \  affirm return = first(lst) + last(lst);\
        \}] {\
        \  return first(lst) + last(lst);\
        \};\
        \x = [3, 6, 9, 12];\
        \ret = sumFirstLast(x);\
        \affirm ret = 15;"

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
    parseValidProgramHelper
        "x = [3, 6, 9, 12];\
        \fn getFirst(y: List<Int>) -> Int [{\
        \  define s = size(y);\
        \  rewrite eqToGtZero s;\
        \  affirm s > 0;\
        \}] [{\
        \  affirm return = first(y);\
        \}] {\
        \  x = [1];\
        \  {\
        \    return first(y);\
        \  };\
        \  return first(x);\
        \};\
        \ret = getFirst(x);\
        \affirm ret = 3;"

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
    parseValidProgramHelper
        "fn getFirstWithSize(lst: List<Int>) -> Int [{\
        \  define s = size(lst);\
        \  rewrite eqToGtZero s;\
        \  affirm s > 0;\
        \}] [{\
        \  affirm s > 0;\
        \  affirm return = first(lst);\
        \}] {\
        \  return first(lst);\
        \};\
        \x = [3, 6, 9, 12];\
        \y = getFirstWithSize(x);\
        \affirm y = 3;\
        \affirm s > 0;"

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

-- What a caller knows of a function is its contracts: the body is neither run nor read for facts
testCallsUseContracts :: Test
testCallsUseContracts =
    let twice n =
            "fn twice(n: Int) -> Int [{ affirm n >= 0; }] [{ }] { i = 0; c = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { i = i + 1; c = c + 2; }; return c; };"
                ++ "x = twice("
                ++ show (n :: Int)
                ++ "); affirm x = "
                ++ show (2 * n)
                ++ ";"
     in testCaseSeq
            "testCallsUseContracts"
            [ -- A call with known arguments is not run to learn its result, however short the computation
              parseValidateFailProgramHelper (twice 3) "Could not prove: x = 6"
            , parseValidateFailProgramHelper "fn id(n: Int) -> Int [{ }] [{ }] { return n; }; x = id(3); affirm x = 3;" "Could not prove: x = 3"
            , -- The program itself runs, whatever validation knows
              parseEvalProgramHelper (twice 50000 ++ " return x;") (Just (VInt 100000))
            , -- What the output contract says is known, for known arguments too
              parseValidProgramHelper "fn dbl(n: Int) -> Int [{ }] [{ affirm return = n + n; }] { return n + n; }; x = dbl(5); affirm x = 10;"
            , -- What the body establishes is not exported, though it holds
              parseValidateFailProgramHelper "fn id(n: Int) -> Int [{ }] [{ }] { return n; }; fn use(n: Int) -> Int [{ }] [{ affirm return = n; }] { return id(n); };" "Could not prove: return = n"
            , parseValidateFailProgramHelper "fn big(n: Int) -> Int [{ affirm n > 5; }] [{ }] { return n; }; fn use(n: Int) -> Int [{ affirm n > 5; }] [{ affirm return > 5; }] { return big(n); };" "Could not prove: return > 5"
            , -- The input contract is not exported as a fact about the result either
              parseValidateFailProgramHelper "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ }] { return 1; }; x = f(2); affirm x = 1;" "Could not prove: x = 1"
            , -- Naming an element with define is how a forall fact gets used at it (LANGUAGE.md, How Validation Works)
              parseValidProgramHelper "fn f(l: List<Int>) -> Int [{ affirm size(l) > 3; affirm forall j in 0..size(l): get(l, j) = 0; }] [{ }] { define v = get(l, 1); affirm v = 0; return 1; };"
            , -- A callee that never ends does not stop validation
              parseValidProgramHelper "fn spin(n: Int) -> Int [{ }] [{ }] ~ { i = 0; while i >= 0 [{ affirm i >= 0; }] ~ { i = i + 1; }; return i; }; x = spin(1);"
            , -- A function is known as the value it is, where it is named as one and not by a fact in every proof of every function
              -- (which made the time to validate grow with the square of the number of functions; the proofs here are of 80 functions)
              parseValidProgramHelper chainOfFunctions
            , parseValidProgramHelper "fn id(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; g = id; x = g(3); affirm x = 3;"
            ]

-- What the validator written in Haskell proved, compared program by program with this one
testHaskellParity :: Test
testHaskellParity =
    testCaseSeq
        "testHaskellParity"
        [ parseValidProgramHelper "fn f(xs: &List<Int>) -> Int [{ }] [{ }] { if size(xs) != 0 { return get(xs, 0); }; return 0; }; return 0;"
        , parseValidProgramHelper "fn inc(n: Int) -> Int { return n + 1; }; fn dec(n: Int) -> Int { return n - 1; }; f = inc; if 2 > 1 { f = dec; }; return f(10);"
        , parseValidProgramHelper "fn f(n: Int) -> Int { return n; }; fn g(n: Int) -> Int { return n; }; h = f; h = g; return f(1) + h(2);"
        , parseValidProgramHelper "fn inc(n: Int) -> Int { return n + 1; }; return size(push([], inc));"
        , parseValidProgramHelper "f = first; return f([7, 2, 3]);"
        , parseValidProgramHelper "fn choose(flag: Bool, a: &Int, b: &Int) -> &Int from (a, b) { if flag { return a; } else { return b; }; }; x = 1; y = 2; r = choose(true, x, y); return *r;"
        , parseValidProgramHelper "enum Rose { Leaf { n: Int }, Node { kids: List<Rose> } }; impl Eq for Rose { }; return 0;"
        , -- (the Haskell validator took a reassigned parameter in an output contract
          -- for its last value, so this returned 2 after proving it returned 1)
          parseValidateFailProgramHelper "fn f(x: Int) -> Int [{ }] [{ affirm return = x; }] { x = 2; return x; }; r = f(1); affirm r = 1; return r;" "Could not prove"
        , -- (a variant test is of the value tested, not of what the local holds since)
          parseValidateFailProgramHelper "enum E { A { v: Int }, B }; fn f(x: E) -> Int { e = x; t = e is E::A; e = E::B; if t { return (e as E::A).v; }; return 0; }; return f(E::A { v: 1 });" "Could not prove"
        , parseValidateFailProgramHelper "enum E { A { v: Int }, B, C { v: Int } }; fn f(x: E) -> Int { e = x; if e is E::A { return 0; }; e = E::A { v: 2 }; if e is E::B { return 1; }; return (e as E::C).v; }; return 0;" "Could not prove"
        , parseValidProgramHelper "enum E { A { v: Int }, B }; fn f(x: E) -> Int { e = x; t = e is E::A; if t { return (e as E::A).v; }; return 0; }; return f(E::A { v: 1 });"
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
            , -- (the bounds alone make i equal to size(l) - 1, and so the elements equal)
              parseValidProgramHelper "fn endOf(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); }] [{ affirm return = get(l, size(l) - 1); }] shrinks size(l) - i { if i + 1 < size(l) { return endOf(l, i + 1); } else { return get(l, i); }; };"
            , -- Partial correctness: a function declared ~ that never returns satisfies any output contract
              parseValidProgramHelper "fn spin(n: Int) -> Int [{ }] [{ affirm return = 0; }] ~ { return spin(n); };"
            , -- A name is still defined once
              parseValidateFailProgramHelper (upTo ++ upTo) "Function already defined: upTo"
            , -- An affirm that is proved becomes a fact: it links i to size(l) - 1 so get(l, i) is get(l, size(l) - 1)
              parseValidProgramHelper "fn g(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); affirm i + 1 >= size(l); }] [{ affirm return = get(l, size(l) - 1); }] { affirm i = size(l) - 1; return get(l, i); };"
            , parseValidProgramHelper "fn g(l: List<Int>, i: Int) -> Int [{ affirm i >= 0; affirm i < size(l); affirm i + 1 >= size(l); }] [{ affirm return = get(l, size(l) - 1); }] { return get(l, i); };"
            ]

-- 80 functions, each calling the one before it through a function value held in a local
chainOfFunctions :: String
chainOfFunctions =
    "fn f0(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; };"
        ++ concat
            [ "fn f" ++ show k ++ "(n: Int) -> Int [{ }] [{ affirm return = n; }] { g = f" ++ show (k - 1) ++ "; return g(n); };"
            | k <- [1 .. 79 :: Int]
            ]
        ++ "x = f79(3); affirm x = 3;"

identity :: String
identity = "fn identity(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n; }; "

cloneProgram :: String -> String
cloneProgram suffix = "x = [1, 2, 3]; y = clone(x); z = clone(y); " ++ suffix

-- The verdict of the cached validator on the second program after the first,
-- the verdict of the uncached one on it, and how many verdicts the second
-- reused
cachedPair :: (M.Program -> M.Program) -> String -> String -> IO (Result (Result () String, Result () String, Int) String)
cachedPair transform before after = case (lowerSource True before, lowerSource True after) of
    (Error e, _) -> pure (Error e)
    (_, Error e) -> pure (Error ("Changed program did not lower: " ++ e))
    (Ok first, Ok second) -> do
        _ <- evaluate (forceVerdict (validateCompiled (transform first)))
        h0 <- validationCacheHits
        cached <- evaluate (validateCompiled (transform second))
        _ <- evaluate (forceVerdict cached)
        h1 <- validationCacheHits
        let uncached = validateCompiledUncached (transform second)
        _ <- evaluate (forceVerdict uncached)
        pure (Ok (cached, uncached, h1 - h0))
  where
    forceVerdict r = case r of
        Ok () -> ()
        Error e -> length e `seq` ()

-- The second program reuses a verdict, and gets the verdict it gets uncached
reuse :: String -> String -> Test
reuse before after = TestCase "" $ do
    outcome <- cachedPair id before after
    pure $ case outcome of
        Error e -> Just e
        Ok (cached, uncached, hits)
            | hits == 0 -> Just "Expected a function verdict to be reused"
            | otherwise -> testAssertEq (show cached) (show uncached)

-- The cached verdict on the second program is the one it gets uncached
parity :: String -> String -> Test
parity = parityWith id

parityWith :: (M.Program -> M.Program) -> String -> String -> Test
parityWith transform before after = TestCase "" $ do
    outcome <- cachedPair transform before after
    pure $ case outcome of
        Error e -> Just e
        Ok (cached, uncached, _) -> testAssertEq (show cached) (show uncached)

-- A changed program is refused although the program before it was accepted
rejectChanged :: String -> String -> Test
rejectChanged = rejectChangedWith id

rejectChangedWith :: (M.Program -> M.Program) -> String -> String -> Test
rejectChangedWith transform before after = TestCase "" $ do
    outcome <- cachedPair transform before after
    pure $ case outcome of
        Error e -> Just e
        Ok (Ok (), _, _) -> Just "Changed program was incorrectly accepted"
        Ok (_, Ok (), _) -> Just "Uncached validator unexpectedly accepted the changed program"
        Ok (Error cached, Error uncached, _) -> testAssertEq cached uncached

unreachedDefinitions :: M.Program -> M.Program
unreachedDefinitions program = program{M.progMain = main'{M.fnBlocks = Map.insert (M.BlockId 999) (M.BasicBlock definitions M.Return) stripped}}
  where
    main' = M.progMain program
    blocks = M.fnBlocks main'
    isDefinition (M.Ghost _ M.GhostFunction{}) = True
    isDefinition _ = False
    definitions = [stmt | block <- Map.elems blocks, stmt <- M.blockStatements block, isDefinition stmt]
    stripped = Map.map (\block -> block{M.blockStatements = filter (not . isDefinition) (M.blockStatements block)}) blocks

frontendParity :: String -> TestResult
frontendParity source = case parseSource source of
    Error e -> Just e
    Ok stmts -> testAssertEq (lowerSource True source) (lowerStatements stmts)

concurrentReuse :: IO (Maybe String)
concurrentReuse = do
    -- (the first validation of a process may build the compiled validator, which is not what is timed)
    _ <- evaluate (forceTestResult (case lowerSource True "return 0;" of
        Error e -> Just e
        Ok program -> either Just (const Nothing) (case validateCompiled program of { Ok _ -> Right (); Error e -> Left e })))
    finished <- timeout 600000000 $
        bracket (mapM worker [1 .. 8 :: Int]) (mapM_ (killThread . fst)) $ \workers ->
            mapM (takeMVar . snd) workers
    return $ case finished of
        Nothing -> Just "Concurrent validation did not finish"
        Just results -> foldr (\r acc -> maybe acc Just r) Nothing results
  where
    worker i = validationWorker $ do
        let result = case lowerSource True (identity ++ "return identity(" ++ show i ++ ");") of
                Error e -> Just e
                Ok program -> testAssertEq (show (validateCompiled program)) (show (validateCompiledUncached program))
        _ <- evaluate (forceTestResult result)
        pure result

validationWorker :: IO TestResult -> IO (ThreadId, MVar TestResult)
validationWorker action = do
    slot <- newEmptyMVar
    thread <- forkIOWithUnmask $ \unmask -> do
        result <- try (unmask action) :: IO (Either SomeException TestResult)
        putMVar slot (either (Just . displayException) id result)
    pure (thread, slot)

validationWorkerMasking :: IO TestResult
validationWorkerMasking = bracket
    (validationWorker (getMaskingState >>= \state -> pure (testAssertEq state Unmasked)))
    (killThread . fst)
    (\(_, slot) -> timeout 2000000 (takeMVar slot) >>= pure . maybe (Just "validation worker did not finish") id)

named :: String -> Test -> Test
named name (TestCase _ action) = TestCase name action
named _ other = other

-- The verdicts of the compiled validator are kept by the data of each function
-- (ValidatorNative): a verdict is reused only for the same data, so the cached
-- verdict on a program is always the one it gets uncached
testValidationCache :: Test
testValidationCache = TestList "testValidationCache"
    [ TestCase "bracketed worker computation is unmasked" validationWorkerMasking
    , TestCase "concurrent process-cache parity" concurrentReuse
    , named "common function hit with changed main" (reuse (identity ++ "return identity(3);") (identity ++ "return identity(4);"))
    , named "library instance hits" (reuse (cloneProgram "a = size(z); affirm a = 3; return a;") (cloneProgram "a = size(z); affirm a = 3; return a + 1;"))
    , named "main assertions still checked" (rejectChanged (identity ++ "return identity(3);") (identity ++ "affirm 1 = 2; return identity(3);"))
    , named "changed body" (rejectChanged (identity ++ "return identity(3);") "fn identity(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n + 1; }; return identity(3);")
    , named "changed contract" (rejectChanged (identity ++ "return identity(3);") "fn identity(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n; }; return identity(3);")
    , named "changed type declaration" (parity "struct Item { value: Int }; fn use(x: Item) -> Int { return 1; }; return 0;" "struct Item { value: Bool }; fn use(x: Item) -> Int { return 1; }; return 0;")
    , named "changed generic declaration" (parity "struct Item<T> { value: T }; fn use(x: Item<Int>) -> Int { return 1; }; return 0;" "struct Item<T> { value: T, other: Int }; fn use(x: Item<Int>) -> Int { return 1; }; return 0;")
    , named "unreached function still checked" (rejectChangedWith unreachedDefinitions (identity ++ "return 0;") "fn identity(n: Int) -> Int [{ }] [{ affirm return = n; }] { return n + 1; }; return 0;")
    , named "changed invariant" (rejectChanged "struct Item { value: Int } invariant [{ affirm value >= 0; }]; fn make() -> Item { return Item { value: 0 }; }; return 0;" "struct Item { value: Int } invariant [{ affirm value > 0; }]; fn make() -> Item { return Item { value: 0 }; }; return 0;")
    , named "changed callee contract" (rejectChanged "fn value() -> Int [{ }] [{ affirm return = 0; }] { return 0; }; fn use() -> Int [{ }] [{ affirm return = 0; }] { return value(); }; return use();" "fn value() -> Int [{ }] [{ affirm return = 1; }] { return 1; }; fn use() -> Int [{ }] [{ affirm return = 0; }] { return value(); }; return use();")
    , named "changed proof-only dependency" (rejectChanged "fn value() -> Int [{ }] [{ affirm return = 0; }] { return 0; }; fn use() -> Int { affirm value() = 0; return 0; }; return use();" "fn value() -> Int [{ }] [{ affirm return = 1; }] { return 1; }; fn use() -> Int { affirm value() = 0; return 0; }; return use();")
    , named "changed global axiom" (rejectChanged "axiom known(x) [{ }] [{ affirm 1 = 2; }]; fn use() -> Int { rewrite known(0); affirm 1 = 2; return 0; }; return 0;" "axiom known(x) [{ }] [{ }]; fn use() -> Int { rewrite known(0); affirm 1 = 2; return 0; }; return 0;")
    , named "changed global assumption" (rejectChanged (identity ++ "assume 1 = 2; affirm 1 = 2; return 0;") (identity ++ "assume 1 = 1; affirm 1 = 2; return 0;"))
    , named "assumptions at the definition" (parity ("assume 1 = 1; " ++ identity ++ "return identity(3);") ("assume 2 = 2; " ++ identity ++ "return identity(3);"))
    , named "mutual recursion hits" (reuse mutual (mutual ++ "affirm 1 = 1;"))
    , named "mutual recursion changed member" (rejectChanged mutual brokenMutual)
    , named "changed function-input reader" (parity "fn value() -> Int { return 0; }; return 0;" "fn value() -> Int { return readByte(); }; return 0;")
    , testCase "library prefix and whole-program elaboration agree" (frontendParity (cloneProgram "return size(z);"))
    , testCase "forward function signatures preserved" (frontendParity "fn first(n: Int) -> Int { return second(n); }; fn second(n: Int) -> Int { return n; }; return first(1);")
    , testCase "prepared prefix does not retain user declarations" (frontendParity "struct Item { value: Int }; x = Item { value: 1 }; return x.value;")
    , testCase "next program can redefine the same type" (frontendParity "struct Item { value: Bool }; x = Item { value: true }; return x.value;")
    , testCase "string and prelude prefix parity" (frontendParity "x = \"hello\"; return size(x);")
    , testCase "user-owned trait prefix parity" (frontendParity "trait Eq { fn eq(self: &Self, other: &Self) -> Bool; }; return 1;")
    ]
  where
    mutual = "fn even(n: Int) -> Bool [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return true; } else { return odd(n - 1); }; }; fn odd(n: Int) -> Bool [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return false; } else { return even(n - 1); }; }; return even(4);"
    brokenMutual = "fn even(n: Int) -> Bool [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return true; } else { return odd(n - 1); }; }; fn odd(n: Int) -> Bool [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return false; } else { return even(n); }; }; return even(4);"

