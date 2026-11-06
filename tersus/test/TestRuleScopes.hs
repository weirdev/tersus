module TestRuleScopes (testRuleScopes) where

import Data.List (isInfixOf)

import Compile (lowerSource)
import qualified MirEval
import qualified ValidatorNative
import qualified Mir as M
import Syntax
import qualified Modules as Mod
import qualified Pipeline as Package
import TestHarness
import Utils

testRuleScopes :: Test
testRuleScopes = TestList "testRuleScopes" $
    [testCase name (checked source (natively name expected)) | (name, source, expected) <- cases]
        ++ [testCase "input-capture counterexample really divides by zero without validation" runtimeOracle]
        ++ [TestCase "unchanged contracts example exports its boundary definition" $ do
                source <- readFile "examples/contracts.tersus"
                pure (checked source Nothing)]
        ++ [testCase "function references use the same canonical term as MIR constants" (checked "fn forward(x: Int) -> Int [{ }] [{ affirm return=x; }] { return x; }; define alias=forward; affirm alias(7)=forward(7); return 0;" Nothing)]
        ++ [testCase name (packageChecked rules main unmodeled) | (name, rules, main, _) <- packageCases]
        ++ [testCase ("paired validators: " ++ name) (checked (rules ++ main) unmodeled) | (name, rules, main, _) <- packageCases, not ("lexical helper" `isInfixOf` name)]
  where
    checked source expected = case lowerSource True source of
        Error e -> Just ("Lowering failed: " ++ e)
        Ok program ->
            let results = [ValidatorNative.validateCompiledUncached program, ValidatorNative.validateCompiled program]
                matches (Ok ()) = expected == Nothing
                matches (Error e) = maybe False (`isInfixOf` e) expected
             in if all matches results then Nothing else Just ("Expected " ++ show expected ++ ", got " ++ show results)
    runtimeOracle = case lowerSource True inputCapture of
        Error e -> Just e
        Ok program -> testAssertErrorContains "Division by zero" (MirEval.runProgram program)

-- The validator written in Tersus does not model yet a proof rule over a function value, a builtin as a
-- value, or a name a rule application keeps to itself: it refuses those programs, so none of them proves
-- what the expectation beside it rejects.
unmodeled :: Maybe String
unmodeled = Just "does not model yet"

natively :: String -> Maybe String -> Maybe String
natively name expected = case lookup name nativeOutcomes of
    Just outcome -> outcome
    Nothing -> expected

nativeOutcomes :: [(String, Maybe String)]
nativeOutcomes =
    [ ("private input and formal names denote different values", Just "Could not prove")
    , ("output-only local is not a caller-visible binding", unmodeled)
    , ("axiom input local cannot disguise a reader actual", unmodeled)
    , ("axiom input local does not replace a legal actual", unmodeled)
    , ("a new function definition name stays private inside a rule application", unmodeled)
    , ("a builtin-valued boundary alias retains size", unmodeled)
    , ("a builtin alias chain survives a global-name collision", unmodeled)
    , ("a builtin-valued alias cannot prove an incorrect size", unmodeled)
    , ("a checked builtin alias retains get preconditions", unmodeled)
    , ("body-only rebinding cannot redefine a public output", Just "Could not prove: x = 0")
    ]

packageChecked :: String -> String -> Maybe String -> TestResult
packageChecked rules main expected =
    let files = [("app/package.tersus", ""), ("app/rules/rules.tersus", rules), ("app/main.tersus", "import app::rules { reflex }; " ++ main)]
        compiled = case Mod.loadFromEntry (Mod.resolverFromFiles files) "app/main.tersus" of
            Left err -> Error err
            Right (Mod.PackageResult package) -> Package.compileModulesValidated package
            Right _ -> Error "Expected a package"
     in case compiled of
        Ok _ | expected == Nothing -> Nothing
        Error err | maybe False (`isInfixOf` err) expected -> Nothing
        _ -> Just ("Expected " ++ show expected ++ ", got " ++ show (mapResult (const ()) compiled))

packageCases :: [(String, String, String, Maybe String)]
packageCases =
    [ ("an imported rule calls a function whose output names its own helper", reflex, helper ++ wrapped ++ "rewrite reflex wrapped 5; return 0;", Nothing)
    , ("callee globals survive a colliding caller proof name", reflex, helper ++ wrapped ++ "fn other(x: Int) -> Int [{ }] [{ affirm return = x + 100; }] { return x + 100; }; define helper = other; rewrite reflex wrapped 5; affirm helper(5) = 105; return 0;", Nothing)
    , ("callee globals survive a colliding rule-private name", "proof reflex(f, x) [{ define helper = 99; }] [{ affirm f(x) = f(x); }] { };", helper ++ wrapped ++ "rewrite reflex wrapped 5; return 0;", Nothing)
    , ("callee input contracts retain their helper in an imported rule", reflex, helper ++ "fn wrapped(x: Int) -> Int [{ affirm helper(x) > 0; }] [{ affirm return = x; }] { return x; }; rewrite reflex wrapped 5; return 0;", Nothing)
    , ("closed callee input contracts still reject invalid actuals", reflex, helper ++ "fn wrapped(x: Int) -> Int [{ affirm helper(x) > 0; }] [{ affirm return = x; }] { return x; }; rewrite reflex wrapped 0; return 0;", Just "input validation failed")
    , ("a formal name does not become the callee's global helper", reflex, helper ++ "fn wrapped(helper: Int) -> Int [{ affirm helper > 0; }] [{ affirm return = helper; }] { return helper; }; rewrite reflex wrapped 5; return 0;", Nothing)
    , ("a contract-local input definition can shadow a global helper", reflex, helper ++ "fn wrapped(x: Int) -> Int [{ define helper = x; affirm helper > 0; }] [{ affirm return = helper; }] { return x; }; rewrite reflex wrapped 5; return 0;", Nothing)
    , ("a contract-local output definition can shadow a global helper", reflex, helper ++ "fn wrapped(x: Int) -> Int [{ }] [{ define helper = x; affirm return = helper; }] { return x; }; rewrite reflex wrapped 5; return 0;", Nothing)
    , ("a forall binder can shadow the callee's helper name", reflex, helper ++ "fn wrapped(x: Int) -> Int [{ }] [{ affirm forall helper in 0..x: helper < x; affirm return = x; }] { return x; }; rewrite reflex wrapped 5; return 0;", Nothing)
    , ("a contract-local function alias retains canonical identity", reflex, helper ++ "fn wrapped(x: Int) -> Int [{ define alias = helper; affirm alias(x) > 0; }] [{ affirm return = x; }] { return x; }; rewrite reflex wrapped 5; return 0;", Nothing)
    , ("an imported rule keeps its own lexical helper, not the caller's", "fn helper(x: Int) -> Int [{ }] [{ affirm return = x + 10; }] { return x + 10; }; proof reflex(f, x) [{ }] [{ affirm helper(x) = x + 10; affirm f(x) = f(x); }] { };", "fn helper(x: Int) -> Int [{ }] [{ affirm return = x + 100; }] { return x + 100; }; fn wrapped(x: Int) -> Int [{ }] [{ affirm return = helper(x); }] { return x + 100; }; rewrite reflex wrapped 5; affirm helper(5) = 105; return 0;", Nothing)
    , ("closing globals does not admit an input-reading helper", reflex, "fn helper(x: Int) -> Int { return readByte(); }; fn wrapped(x: Int) -> Int [{ }] [{ affirm return = helper(x); }] { return x; }; rewrite reflex wrapped 5; return 0;", Just "reads the input")
    ]
  where
    reflex = "proof reflex(f, x) [{ }] [{ affirm f(x) = f(x); }] { };"
    helper = "fn helper(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; };"
    wrapped = "fn wrapped(x: Int) -> Int [{ }] [{ affirm return = helper(x); }] { return x; };"

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
    , ("function contract locals do not replace existing caller bindings", namedContract ++ "define n = 6; value = identity(5); affirm n = 6; return value;", Nothing)
    , ("rule uses its lexical function binding, not a caller shadow", "fn observe(i: Int) -> Int [{ }] [{ affirm return = 0; }] { return 0; }; fn reader(i: Int) -> Int { return readByte(); }; proof fixed(x) [{ affirm observe(x) = 0; }] [{ affirm observe(x) = 0; }] { }; define observe = reader; rewrite fixed 0; return 0;", Nothing)
    , ("absent function boundary definition is published", namedContract ++ "value = identity(5); affirm n = 0; return value;", Nothing)
    , ("existing code local retains precedence over a function boundary definition", namedContract ++ "n = 6; value = identity(5); affirm n = 6; return value;", Nothing)
    , ("a function boundary name cannot shadow a global function", "fn n() -> Int [{ }] [{ affirm return = 6; }] { return 6; }; " ++ namedContract ++ "value = identity(5); affirm n() = 6; return value;", Nothing)
    , ("function boundary collision cannot manufacture false caller facts", namedContract ++ "define n = 6; value = identity(5); affirm 6 = 0; return 0;", Just "Could not prove: 6 = 0")
    , ("existing function parameter retains precedence over a nested boundary definition", namedContract ++ "fn outer(n: Int) -> Int [{ }] [{ affirm return = n; }] { value = identity(5); affirm value = 5; return n; }; return outer(6);", Nothing)
    , ("a new function definition name stays private inside a rule application", namedContract ++ "proof call(x) [{ affirm identity(x) = x; }] [{ affirm x = x; }] { }; rewrite call 5; affirm n = 0; return 0;", Just "Variable not found in proof map: n")
    , ("an existing rule-local proof definition survives a nested function contract", namedContract ++ "proof call(x) [{ define n = 6; affirm identity(x) = x; affirm n = 6; }] [{ affirm n = 6; }] { }; define n = 7; rewrite call 5; affirm n = 7; return 0;", Nothing)
    , ("global function collision cannot bind a boundary constant to the function", "fn n() -> Int [{ }] [{ affirm return = 6; }] { return 6; }; " ++ namedContract ++ "value = identity(5); affirm 6 = 0; return 0;", Just "Could not prove: 6 = 0")
    , ("a noncolliding output function alias retains its function", boundaryAliases "selected" ++ "value = f(0); affirm alias(0) = 2; return 0;", Nothing)
    , ("two output function aliases survive a caller-global collision", boundaryAliases "helper1" ++ "value = f(0); affirm alias(0) = 2; affirm helper1(0) = 1; return 0;", Nothing)
    , ("a colliding output alias cannot acquire the caller's other function", boundaryAliases "helper1" ++ "value = f(0); affirm alias(0) = 1; return 0;", Just "Could not prove: alias(0) = 1")
    , ("a builtin-valued boundary alias retains size", builtinAliases "selected" ++ "value = measure([1, 2]); affirm alias([1, 2]) = 2; return 0;", Nothing)
    , ("a builtin alias chain survives a global-name collision", builtinAliases "size" ++ "value = measure([1, 2]); affirm alias([1, 2]) = 2; return 0;", Nothing)
    , ("a builtin-valued alias cannot prove an incorrect size", builtinAliases "size" ++ "value = measure([1, 2]); affirm alias([1, 2]) = 1; return 0;", Just "Could not prove")
    , ("a checked builtin alias retains get preconditions", "fn firstValue(xs: &List<Int>) -> Int [{ affirm size(xs) > 0; }] [{ define alias = get; affirm return = alias(xs, 0); }] { return get(xs, 0); }; value = firstValue([1, 2]); affirm alias([1, 2], 2) = alias([1, 2], 2); return 0;", Just "input validation failed")
    , ("body-only rebinding cannot redefine a public output", "proof bad(x) [{ }] [{ affirm x = 0; }] { define x = 0; }; rewrite bad 6; affirm 6 = 0; return 0;", Just "private body binding")
    ]

builtinAliases :: String -> String
builtinAliases name = "fn measure(xs: &List<Int>) -> Int [{ }] [{ define " ++ name ++ " = size; define alias = " ++ name ++ "; affirm return = alias(xs); }] { return size(xs); }; "

boundaryAliases :: String -> String
boundaryAliases name = "fn helper1(x: Int) -> Int [{ }] [{ affirm return = x + 1; }] { return x + 1; }; fn helper2(x: Int) -> Int [{ }] [{ affirm return = x + 2; }] { return x + 2; }; fn f(x: Int) -> Int [{ }] [{ define " ++ name ++ " = helper2; define alias = " ++ name ++ "; affirm return = alias(x); }] { return x + 2; }; "

functions :: String
functions = "fn pure(i: Int) -> Int [{ }] [{ affirm return = i; }] { return i; }; fn reader(i: Int) -> Int { return readByte(); }; "

namedContract :: String
namedContract = "fn identity(x: Int) -> Int [{ }] [{ define n = 0; affirm return = x; }] { return x; }; "
