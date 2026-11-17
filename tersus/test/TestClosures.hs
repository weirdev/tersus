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
            , testCase "a named function satisfies an Fn bound" (runs ("fn double(x: Int) -> Int { return x * 2; }; fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; return apply(double, 21);") 42)
            , testCase "a named function satisfies a shape over a type parameter" (runs ("fn idInt(x: Int) -> Int { return x; }; fn applyAt<T, F: Fn(T) -> T>(f: &F, x: T) -> T { return f(x); }; return applyAt(idInt, 41);") 41)
            , testCase "a named function whose contract does not meet the bound is refused" (rejected ("fn inc(x: Int) -> Int [{ }] [{ }] { return x + 1; }; fn useIt<F: Fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }]>(f: &F, x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] { return f(x); }; return useIt(inc, 5);") "does not meet")
            , testCase "a generic impl shape meets a bound that names its parameter differently" (runs ("struct First<U> { item: U }; impl<U> Fn(U) -> U for First<U> { fn call(self: &Self, a: U) -> U { return a; }; }; fn applyAt<T, F: Fn(T) -> T>(f: &F, x: T) -> T { return f(x); }; f = First<Int> { item: 7 }; return applyAt(&f, 41);") 41)
            , testCase "a shape over Int does not take a type parameter named I" (runs (adder ++ "fn choose<I, F: Fn(Int) -> Int>(f: &F, v: I, x: Int) -> Int { return f(x); }; a = Adder { n: 10 }; return choose(&a, 3, 5);") 15)
            , testCase "a function object over a named type" (runs ("struct Wrap { n: Int }; struct M { n: Int }; impl Fn(Wrap) -> Int for M { fn call(self: &Self, w: Wrap) -> Int { return w.n; }; }; fn useIt<F: Fn(Wrap) -> Int>(f: &F, w: Wrap) -> Int { return f(w); }; m = M { n: 0 }; return useIt(&m, Wrap { n: 7 });") 7)
            , testCase "whitespace inside a contract string is part of the shape" (runs ("struct String { bytes: List<Byte> }; impl Eq for String { }; impl Clone for String { }; struct Spaced { n: Int }; impl Fn(x: String) -> Int [{ affirm x = \"a b\"; }] [{ }] for Spaced { fn call(self: &Self, x: String) -> Int [{ }] [{ }] { return 1; }; }; struct Joined { n: Int }; impl Fn(x: String) -> Int [{ affirm x = \"ab\"; }] [{ }] for Joined { fn call(self: &Self, x: String) -> Int [{ }] [{ }] { return 2; }; }; fn useSpaced<F: Fn(x: String) -> Int [{ affirm x = \"a b\"; }] [{ }]>(f: &F) -> Int { return f(\"a b\"); }; fn useJoined<F: Fn(x: String) -> Int [{ affirm x = \"ab\"; }] [{ }]>(f: &F) -> Int { return f(\"ab\"); }; s = Spaced { n: 0 }; j = Joined { n: 0 }; return useSpaced(&s) * 10 + useJoined(&j);") 12)
            , TestCase "a function object across modules" $ do
                program <-
                    programFromFiles
                        "app/main.tersus"
                        [ ("app/package.tersus", "")
                        , ("app/main.tersus", "import app::apply; struct Adder { n: Int }; impl Fn(x: Int) -> Int for Adder { fn call(self: &Self, x: Int) -> Int { return x + self.n; }; }; a = Adder { n: 10 }; return apply::apply(&a, 5);")
                        , ("app/apply.tersus", "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); };")
                        ]
                pure (testAssertEq (program `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 15))))
            , TestList
                "closures"
                [ testCase "a closure reads a Copy capture, copied at creation" (runs "n = 10; f = fn(x: Int) -> Int => x + n; return f(5);") 15)
                , testCase "a copied capture does not see a later update" (runs "n = 1; f = fn(x: Int) -> Int => x + n; n = 100; return f(1);") 2)
                , testCase "a closure borrows a read-only list capture" (runs "xs = push(push([], 1), 2); f = fn() -> Int => size(xs); return f() * 10 + size(xs);") 22)
                , testCase "a closure that updates a capture is called directly" (runs "count = 0; f = fn() -> Int { count = count + 1; return count; }; a = f(); b = f(); return a * 100 + b * 10 + count;") 122)
                , testCase "an updating closure through an FnMut bound" (runs "fn twice<F: FnMut() -> Int>(f: &mut F) -> Int { a = f(); b = f(); return a * 10 + b; }; count = 0; c = fn() -> Int { count = count + 1; return count; }; return twice(&mut c) * 100 + count;") 1202)
                , testCase "a read-only closure meets an FnMut bound" (runs "fn twice<F: FnMut() -> Int>(f: &mut F) -> Int { a = f(); b = f(); return a * 10 + b; }; n = 1; c = fn() -> Int => n; return twice(&mut c);") 11)
                , testCase "types are inferred from the bound" (runs "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; return apply(fn(x) => x * 2, 21);") 42)
                , testCase "a type is inferred from the other arguments and the result" (runs "fn applyAt<T, F: Fn(T) -> T>(f: &F, x: T) -> T { return f(x); }; return applyAt(fn(x) => x, 41);") 41)
                , testCase "a closure argument is checked after the other arguments" (runs "fn apply2<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; return apply2(fn(x) => x + 1, 41);") 42)
                , testCase "an expression body and a block body agree" (runs "f = fn(x: Int) -> Int => x + 1; g = fn(x: Int) -> Int { return x + 1; }; return f(10) * 100 + g(10);") 1111)
                , testCase "a missing parameter type with no bound is an error" (rejected "f = fn(x) => x; return 0;") "write the type of x: nothing here says what this closure takes")
                , testCase "an updating closure does not meet an Fn bound" (rejected "fn apply<F: Fn() -> Int>(f: &F) -> Int { return f(); }; count = 0; c = fn() -> Int { count = count + 1; return count; }; return apply(&c);") "is FnMut and cannot be given where Fn(...) is wanted")
                , testCase "an updating closure given directly does not meet an Fn bound" (rejected "fn apply<F: Fn() -> Int>(f: &F) -> Int { return f(); }; count = 0; return apply(fn() -> Int { count = count + 1; return count; });") "updates count, so it is FnMut")
                , testCase "a closure moves a captured list out, as FnOnce" (runs "fn useOnce<F: FnOnce() -> List<Int>>(f: F) -> Int { ys = f(); return size(ys); }; xs = push(push([], 1), 2); f = fn() -> List<Int> => xs; return useOnce(f);") 2)
                , testCase "a moving closure does not meet an Fn bound" (rejected "fn apply<F: Fn() -> List<Int>>(f: &F) -> Int { ys = f(); return size(ys); }; xs = push([], 1); return apply(fn() -> List<Int> => xs);") "moves xs out, so it is FnOnce")
                , testCase "move captures by value, and an update changes the closure's own copy" (runs "n = 1; f = move fn() -> Int { n = n + 1; return n; }; a = f(); return a * 10 + n;") 21)
                , testCase "move captures a list by value" (runs "xs = push(push([], 1), 2); f = move fn() -> Int => size(xs); return f();") 2)
                , testCase "a capture-only clause is the closure's invariant" (runs "n = 5; step = fn(x: Int) -> Int [{ affirm n > 0; }] [{ affirm return > x; }] => x + n; return step(1);") 6)
                , testCase "the invariant is proved where the closure is made" (rejected "n = 0 - 5; step = fn(x: Int) -> Int [{ affirm n > 0; }] [{ affirm return > x; }] => x + n; return step(1);") "Could not prove")
                , testCase "a closure meets two bounds with two impls over one body" (runs "fn asFn<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; fn asOnce<F: FnOnce(x: Int) -> Int>(f: F, x: Int) -> Int { return f(x); }; f = fn(x: Int) -> Int => x + 1; return asFn(&f, 10) * 100 + asOnce(f, 10);") 1111)
                , testCase "a borrowed capture goes through a bound" (runs "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; xs = push(push([], 1), 2); f = fn(x: Int) -> Int => x + size(xs); return apply(&f, 10);") 12)
                , testCase "a closure over a type parameter of the enclosing function" (runs "fn countOf<T>(xs: &List<T>, n: Int) -> Int { f = fn() -> Int => size(xs) + n; return f(); }; return countOf(push(push([], 1), 2), 10);") 12)
                , TestCase "a closure across modules" $ do
                    program <-
                        programFromFiles
                            "app/main.tersus"
                            [ ("app/package.tersus", "")
                            , ("app/main.tersus", "import app::apply; n = 10; f = fn(x) => x + n; return apply::apply(f, 5);")
                            , ("app/apply.tersus", "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); };")
                            ]
                    pure (testAssertEq (program `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 15))))
                ]
            ]
