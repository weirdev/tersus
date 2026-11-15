module TestClosures (testClosures) where

import qualified MirEval
import Syntax
import TestHarness
import Utils (Result (..), bindResult)

-- Phase 1 of the closures plan: Fn/FnMut/FnOnce bounds, minted traits, function objects.
-- Plan: ~/notes/users/wweirather/.claude/plans/tersus-closures-master-plan.md (Phase 1)
testClosures :: Test
testClosures =
    let adder = "struct Adder { n: Int }; impl Fn(x: Int) -> Int for Adder { fn call(self: &Self, x: Int) -> Int { return x + self.n; }; }; "
        counter = "struct Counter { count: Int }; impl FnMut() -> Int for Counter { fn call(self: &mut Self) -> Int { (*self).count = (*self).count + 1; return (*self).count; }; }; "
        runs src expected = parseEvalProgramHelper src (Just (VInt expected))
        valid src = parseValidProgramHelper src
        rejected src expected = parseValidateFailProgramHelper src expected
     in TestList
            "testClosures"
            [ testCase "a function object through an Fn bound, called as f(x)" (runs (adder ++ "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; a = Adder { n: 10 }; return apply(&a, 5);") 15)
            , testCase "a function object through an Fn bound, called as f.call(x)" (runs (adder ++ "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f.call(x); }; a = Adder { n: 10 }; return apply(&a, 5);") 15)
            , testCase "unnamed parameters in a shape" (runs (adder ++ "fn apply<F: Fn(Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; a = Adder { n: 1 }; return apply(&a, 5);") 6)
            , testCase "a shape over a type parameter" (runs ("struct First<T> { item: T }; impl<T> Fn(a: T) -> T for First<T> { fn call(self: &Self, a: T) -> T { return a; }; }; fn applyAt<T, F: Fn(T) -> T>(f: &F, x: T) -> T { return f(x); }; f = First<Int> { item: 7 }; return applyAt(&f, 41);") 41)
            , testCase "lent parameters in a shape" (runs ("struct Sum { n: Int }; impl Fn(a: &Int) -> Int for Sum { fn call(self: &Self, a: &Int) -> Int { return (*a) + self.n; }; }; fn useIt<F: Fn(a: &Int) -> Int>(f: &F, x: &Int) -> Int { return f(x); }; s = Sum { n: 3 }; x = 4; return useIt(&s, &x);") 7)
            , testCase "an FnMut function object updates through &mut Self" (runs (counter ++ "fn twice<F: FnMut() -> Int>(f: &mut F) -> Int { a = f(); b = f(); return a * 10 + b; }; c = Counter { count: 0 }; r = twice(&mut c); return r * 100 + c.count;") 1202)
            , testCase "an FnOnce function object is called by value" (runs ("struct Once { n: Int }; impl FnOnce(x: Int) -> Int for Once { fn call(self: Self, x: Int) -> Int { return x + self.n; }; }; fn useOnce<F: FnOnce(x: Int) -> Int>(f: F, x: Int) -> Int { return f(x); }; o = Once { n: 2 }; return useOnce(o, 40);") 42)
            , testCase "the same shape in two bounds is one trait" (runs (adder ++ "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; fn apply2<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return apply(f, x) + 1; }; a = Adder { n: 10 }; return apply2(&a, 5);") 16)
            , testCase "a contract in the bound is met by the impl" (runs ("struct Inc { n: Int }; impl Fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] for Inc { fn call(self: &Self, x: Int) -> Int [{ }] [{ affirm return > x; }] { return x + 1; }; }; fn useIt<F: Fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }]>(f: &F, x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] { return f(x); }; i = Inc { n: 0 }; return useIt(&i, 5);") 6)
            , testCase "a contract in the bound is not met by the impl" (rejected ("struct Bad { n: Int }; impl Fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] for Bad { fn call(self: &Self, x: Int) -> Int [{ }] [{ }] { return x; }; }; return 0;") "does not meet")
            , testCase "an FnMut object does not meet an Fn bound" (rejected (counter ++ "fn apply<F: Fn() -> Int>(f: &F) -> Int { return f(); }; c = Counter { count: 0 }; return apply(&c);") "Fn(...)")
            , testCase "a type with no function impl does not meet an Fn bound" (rejected ("struct Plain { n: Int }; fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; p = Plain { n: 1 }; return apply(&p, 5);") "Fn(...)")
            , testCase "a shape with no result type is a parse error" (pipelineRejected "fn apply<F: Fn(x: Int)>(f: &F, x: Int) -> Int { return x; }; return 0;" "expected (")
            , testCase "a bound shape that is never called still checks" (valid (adder ++ "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return x; }; return 0;"))
            , TestCase "a function object across modules" $ do
                program <-
                    programFromFiles
                        "app/main.tersus"
                        [ ("app/package.tersus", "")
                        , ("app/main.tersus", "import app::apply; struct Adder { n: Int }; impl Fn(x: Int) -> Int for Adder { fn call(self: &Self, x: Int) -> Int { return x + self.n; }; }; a = Adder { n: 10 }; return apply::apply(&a, 5);")
                        , ("app/apply.tersus", "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); };")
                        ]
                pure (testAssertEq (program `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 15))))
            ]
