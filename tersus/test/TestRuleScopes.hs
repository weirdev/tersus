module TestRuleScopes (testRuleScopes) where

import Data.List (isInfixOf)

import Compile (lowerSource)
import qualified MirEval
import qualified MirValidate
import ProofState (emptyValidationCache)
import TestHarness
import Utils

testRuleScopes :: Test
testRuleScopes = TestList "testRuleScopes" $
    [testCase name (checked source expected) | (name, source, expected) <- cases]
        ++ [testCase "input-capture counterexample really divides by zero without validation" runtimeOracle]
  where
    checked source expected = case lowerSource True source of
        Error e -> Just ("Lowering failed: " ++ e)
        Ok program ->
            let results = [mapResult (const ()) (MirValidate.validateProgramUncached program), mapResult (const ()) (MirValidate.validateProgramWithCache emptyValidationCache program)]
                matches (Ok ()) = expected == Nothing
                matches (Error e) = maybe False (`isInfixOf` e) expected
             in if all matches results then Nothing else Just ("Expected " ++ show expected ++ ", got " ++ show results)
    runtimeOracle = case lowerSource True inputCapture of
        Error e -> Just e
        Ok program -> testAssertErrorContains "Division by zero" (MirEval.runProgram program)

inputCapture :: String
inputCapture = "proof positive(x) [{ define i = 1; affirm x > 0; }] [{ affirm x > 0; }] { }; i = 0; rewrite positive i; return 1 / i;"

cases :: [(String, String, Maybe String)]
cases =
    [ ("caller argument is captured before an input local", inputCapture, Just "Could not prove")
    , ("alpha-renaming the private input does not change rejection", "proof positive(x) [{ define private = 1; affirm x > 0; }] [{ affirm x > 0; }] { }; i = 0; rewrite positive i; return 1 / i;", Just "Could not prove")
    , ("a valid colliding argument still passes", "proof positive(x) [{ define i = 1; affirm x > 0; }] [{ affirm x > 0; }] { }; i = 2; rewrite positive i; return 4 / i;", Nothing)
    , ("private input and formal names denote different values", "proof local(x) [{ define x = 1; affirm x > 0; }] [{ affirm x > 0; }] { }; i = 0; rewrite local i; return 1 / i;", Just "input validation failed")
    , ("a formal-shadowing local does not change the caller", "proof local(x) [{ define x = 1; affirm x > 0; }] [{ affirm x > 0; }] { }; i = 0; rewrite local i; affirm i = 0; return i;", Nothing)
    , ("output-only local cannot bind an existing caller variable", "proof bad(x) [{ }] [{ define n = 0; affirm n = 0; }] { }; define n = 6; rewrite bad 5; affirm 6 = 0; return 0;", Just "Could not prove: 6 = 0")
    , ("output-only local is not a caller-visible binding", "proof bad(x) [{ }] [{ define n = 0; affirm n = 0; }] { }; rewrite bad 5; affirm n = 0; return 0;", Just "Variable not found in proof map: n")
    , ("output-only local preserves an existing caller variable", "proof bad(x) [{ }] [{ define n = 0; affirm n = 0; }] { }; define n = 6; rewrite bad 5; affirm n = 6; return 0;", Nothing)
    , ("output local can shadow a formal without changing the actual", "proof local(x) [{ }] [{ define x = 0; affirm x = 0; }] { }; define x = 6; rewrite local x; affirm x = 6; return 0;", Nothing)
    , ("saved input-local version survives output rebinding", "proof snapshot(x) [{ define n = x + 1; define saved = n; }] [{ define n = 0; affirm n = 0; affirm saved = x + 1; }] { }; define n = 6; rewrite snapshot 5; affirm n = 6; return 0;", Nothing)
    , ("axiom input local cannot disguise a reader actual", functions ++ "axiom ax(f) [{ define g = pure; }] [{ affirm forall j in 0..2: f(j) = f(j); }]; g = reader; rewrite ax g; return 0;", Just "reads the input")
    , ("axiom input local does not replace a legal actual", functions ++ "axiom ax(f) [{ define g = reader; }] [{ affirm forall j in 0..2: f(j) = f(j); }]; g = pure; rewrite ax g; return 0;", Nothing)
    , ("axiom output local does not capture a caller proof variable", "axiom ax(x) [{ }] [{ define n = 0; affirm n = 0; }]; define n = 6; rewrite ax 5; affirm 6 = 0; return 0;", Just "Could not prove: 6 = 0")
    , ("axiom truth about the captured actual remains trusted", "axiom ax(x) [{ define i = 1; }] [{ affirm x > 100; }]; i = 0; rewrite ax i; affirm i > 100; return 0;", Nothing)
    , ("nested rule scope restores its immediate caller", "proof inner(x) [{ define n = 0; }] [{ affirm x = x; }] { }; proof outer(x) [{ define n = 1; }] [{ affirm n = 1; }] { rewrite inner x; affirm n = 1; }; define n = 6; rewrite outer 5; affirm n = 6; return 0;", Nothing)
    , ("nested function contract cannot overwrite caller proof names", namedContract ++ "fn outer(x: Int) -> Int [{ define n = 1; }] [{ affirm return = x; }] { y = identity(x); affirm n = 1; return y; }; return outer(5);", Nothing)
    , ("function contract locals are not published as caller bindings", namedContract ++ "define n = 6; value = identity(5); affirm n = 6; return value;", Nothing)
    , ("rule uses its lexical function binding, not a caller shadow", "fn observe(i: Int) -> Int [{ }] [{ affirm return = 0; }] { return 0; }; fn reader(i: Int) -> Int { return readByte(); }; proof fixed(x) [{ affirm observe(x) = 0; }] [{ affirm observe(x) = 0; }] { }; define observe = reader; rewrite fixed 0; return 0;", Nothing)
    , ("body-only rebinding cannot redefine a public output", "proof bad(x) [{ }] [{ affirm x = 0; }] { define x = 0; }; rewrite bad 6; affirm 6 = 0; return 0;", Just "private body binding")
    ]

functions :: String
functions = "fn pure(i: Int) -> Int [{ }] [{ affirm return = i; }] { return i; }; fn reader(i: Int) -> Int { return readByte(); }; "

namedContract :: String
namedContract = "fn identity(x: Int) -> Int [{ }] [{ define n = 0; affirm return = x; }] { return x; }; "
