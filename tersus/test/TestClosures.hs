module TestClosures (testClosures, closureAdder, closureCounter, closureModuleFiles) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Mir
import qualified MirEval
import Pipeline (compileSource)
import Syntax
import TestHarness
import TestNative (nativeMirCase)
import Utils (Result (..), bindResult, mapResult)

-- Phase 1 of the closures plan: Fn/FnMut/FnOnce bounds, minted traits, function objects.
-- Plan: ~/notes/users/wweirather/.claude/plans/tersus-closures-master-plan.md (Phase 1)
testClosures :: Test
testClosures =
    let adder = closureAdder
        counter = closureCounter
        runs src expected = parseEvalProgramHelper src (Just (VInt expected))
        valid src = parseValidProgramHelper src
        rejected src expected = parseValidateFailProgramHelper src expected
        checked src result = testAssertEq (compileSource src `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt result)))
        rejects src expected = testAssertErrorContains expected (compileSource src)
        increment = "fn step(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n + 1; }] { return n + 1; }; "
        positiveStep = "fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }]"
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
                        closureModuleFiles
                pure (testAssertEq (program `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 15))))
            , testCase "boxed closure calls use the declared result contract" (checked ("let f: Closure<" ++ positiveStep ++ "> = fn(x: Int) -> Int [{ }] [{ affirm return > x; }] => x + 1; y = f(41); affirm y > 41; return y;") 42)
            , testCase "boxing does not infer a postcondition from the closure body" (rejects ("let f: Closure<" ++ positiveStep ++ "> = fn(x: Int) -> Int => x + 1; return 0;") "Could not prove")
            , testCase "a boxed call must prove the type's input contract" (rejects ("let f: Closure<" ++ positiveStep ++ "> = fn(x: Int) -> Int [{ }] [{ affirm return > x; }] => x + 1; return f(0);") "Could not prove")
            , testCase "a mutable boxed closure retains its owned state across calls" (checked "count = 0; let f: ClosureMut<fn() -> Int> = move fn() -> Int { count = count + 1; return count; }; a = f(); b = f(); return a * 10 + b;" 12)
            , testCase "boxed calls with separate contracts do not introduce a spurious cycle" (checked "fn good() -> Int [{ }] [{ affirm return = 42; }] { return 42; };\nfn invoke(f: &Closure<fn() -> Int [{ }] [{ affirm return = 42; }]>) -> Int { return f(); };\nfn second() -> Int [{ }] [{ affirm return = 2; }] {\n    let f: Closure<fn() -> Int [{ }] [{ affirm return = 42; }]> = good;\n    n = invoke(&f);\n    return 2;\n};\nlet g: Closure<fn() -> Int [{ }] [{ affirm return = 2; }]> = second;\nreturn g() + 40;\n" 42)
            , testCase "an indirect cycle through a boxed closure is refused" (rejects "fn invoke(f: &Closure<fn() -> Int>) -> Int { return f(); };\nfn cycle() -> Int {\n    let f: Closure<fn() -> Int> = cycle;\n    return invoke(&f);\n};\nreturn 0;\n" "potential recursion through a function value")
            , testCase "mutable boxed calls give fresh results even with identical arguments" (rejects "n = 0;\nlet f: ClosureMut<fn() -> Int> = move fn() -> Int {\n    n = n + 1;\n    return n;\n};\na = f();\nb = f();\naffirm a = b;\nreturn b;\n" "Could not prove: a = b")
            , testCase "boxing refuses a potentially diverging callable" (rejects "fn spin() -> Int [{ }] [{ }] ~ { return spin(); };\nlet f: Closure<fn() -> Int> = spin;\nreturn 0;\n" "a boxed closure cannot use a potentially diverging callable")
            , testCase "a boxed element view cannot survive replacement of its owner" (rejects "fn make(n: Int) -> Closure<fn() -> Int> { return move fn() -> Int => n; };\nlet xs: List<Closure<fn() -> Int>> = [make(42)];\npart = get(xs, 0);\nxs = set(xs, 0, make(7));\nreturn part();\n" "still looks at xs[0]")
            , TestCase "an Fn bound in a module of its own" $ do
                program <-
                    programFromFiles
                        "app/main.tersus"
                        [ ("app/package.tersus", "")
                        , ("app/main.tersus", "import app::lib { apply }; struct Adder { n: Int }; impl Fn(x: Int) -> Int for Adder { fn call(self: &Self, x: Int) -> Int { return x + self.n; }; }; a = Adder { n: 10 }; return apply(&a, 5);")
                        , ("app/lib/lib.tersus", "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); };")
                        ]
                pure (testAssertEq (program `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 15))))
            , TestList
                "closures"
                [ testCase "a closure reads a Copy capture, copied at creation" (runs "n = 10; f = fn(x: Int) -> Int => x + n; return f(5);" 15)
                , testCase "a copied capture does not see a later update" (runs "n = 1; f = fn(x: Int) -> Int => x + n; n = 100; return f(1);" 2)
                , testCase "a closure borrows a read-only list capture" (runs "xs = push(push([], 1), 2); f = fn() -> Int => size(xs); return f() * 10 + size(xs);" 22)
                , testCase "a closure that updates a capture is called directly" (runs "count = 0; f = fn() -> Int { count = count + 1; return count; }; a = f(); return a * 10 + count;" 11)
                , testCase "an updating closure called directly twice, checked" (valid "count = 0; f = fn() -> Int { count = count + 1; return count; }; a = f(); b = f(); return a * 100 + b * 10 + count;")
                , testCase "an updating closure through an FnMut bound" (runs "fn once<F: FnMut() -> Int>(f: &mut F) -> Int { return f(); }; count = 0; c = fn() -> Int { count = count + 1; return count; }; return once(&mut c) * 10 + count;" 11)
                , testCase "an updating closure through an FnMut bound twice, checked" (valid "fn twice<F: FnMut() -> Int>(f: &mut F) -> Int { a = f(); b = f(); return a * 10 + b; }; count = 0; c = fn() -> Int { count = count + 1; return count; }; return twice(&mut c) * 100 + count;")
                , testCase "a read-only closure meets an FnMut bound" (runs "fn twice<F: FnMut() -> Int>(f: &mut F) -> Int { a = f(); b = f(); return a * 10 + b; }; n = 1; c = fn() -> Int => n; return twice(&mut c);" 11)
                , testCase "types are inferred from the bound" (runs "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; return apply(fn(x) => x * 2, 21);" 42)
                , testCase "a type is inferred from the other arguments and the result" (runs "fn applyAt<T, F: Fn(T) -> T>(f: &F, x: T) -> T { return f(x); }; return applyAt(fn(x) => x, 41);" 41)
                , testCase "a closure argument is checked after the other arguments" (runs "fn apply2<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; return apply2(fn(x) => x + 1, 41);" 42)
                , testCase "an expression body and a block body agree" (runs "f = fn(x: Int) -> Int => x + 1; g = fn(x: Int) -> Int { return x + 1; }; return f(10) * 100 + g(10);" 1111)
                , testCase "a missing parameter type with no bound is an error" (rejected "f = fn(x) -> Int => x; return 0;" "write the type of x: nothing here says what this closure takes")
                , testCase "an updating closure does not meet an Fn bound" (rejected "fn apply<F: Fn() -> Int>(f: &F) -> Int { return f(); }; count = 0; c = fn() -> Int { count = count + 1; return count; }; return apply(&c);" "is FnMut and cannot be given where Fn(...) is wanted")
                , testCase "an updating closure given directly does not meet an Fn bound" (rejected "fn apply<F: Fn() -> Int>(f: &F) -> Int { return f(); }; count = 0; return apply(fn() -> Int { count = count + 1; return count; });" "updates count, so it is FnMut")
                , testCase "a closure moves a captured list out, as FnOnce" (runs "fn useOnce<F: FnOnce() -> List<Int>>(f: F) -> Int { ys = f(); return size(ys); }; xs = push(push([], 1), 2); f = fn() -> List<Int> => xs; return useOnce(f);" 2)
                , testCase "a moving closure does not meet an Fn bound" (rejected "fn apply<F: Fn() -> List<Int>>(f: &F) -> Int { ys = f(); return size(ys); }; xs = push([], 1); return apply(fn() -> List<Int> => xs);" "moves xs out, so it is FnOnce")
                , testCase "move captures by value, and an update changes the closure's own copy" (runs "n = 1; f = move fn() -> Int { n = n + 1; return n; }; a = f(); return a * 10 + n;" 21)
                , testCase "move captures a list by value" (runs "xs = push(push([], 1), 2); f = move fn() -> Int => size(xs); return f();" 2)
                , testCase "a capture-only clause is the closure's invariant" (runs "n = 5; step = fn(x: Int) -> Int [{ affirm n > 0; }] [{ affirm return > x; }] => x + n; return step(1);" 6)
                , testCase "the invariant is proved where the closure is made" (rejected "n = 0 - 5; step = fn(x: Int) -> Int [{ affirm n > 0; }] [{ affirm return > x; }] => x + n; return step(1);" "Could not prove")
                , testCase "a closure meets two bounds with two impls over one body" (runs "fn asFn<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; fn asOnce<F: FnOnce(x: Int) -> Int>(f: F, x: Int) -> Int { return f(x); }; f = fn(x: Int) -> Int => x + 1; return asFn(&f, 10) * 100 + asOnce(f, 10);" 1111)
                , testCase "a borrowed capture goes through a bound" (runs "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; xs = push(push([], 1), 2); f = fn(x: Int) -> Int => x + size(xs); return apply(&f, 10);" 12)
                , testCase "a let-bound variable is captured" (runs "let n = 10; f = fn() -> Int => n; return f();" 10)
                , testCase "a closure in a method reads the receiver" (runs "struct P { n: Int }; impl P { fn get(self: &Self) -> Int { f = fn() -> Int => self.n; return f(); }; }; p = P { n: 7 }; return p.get();" 7)
                , testCase "a parameter named fn is a variable, not a closure" (runs "struct P { items: List<Int> }; fn count(fn: &P) -> Int { return size(fn.items); }; p = P { items: push(push([], 1), 2) }; return count(&p);" 2)
                , testCase "a variable named fn used bare" (runs "fn len(fn: &List<Int>) -> Int { return size(fn); }; xs = push(push([], 7), 8); return len(&xs);" 2)
                , testCase "a closure at the top calls a function of the program" (valid "fn inc(n: Int) -> Int { return n + 1; }; fn once<U, F: FnOnce() -> U>(f: F) -> U { return f(); }; return once(fn() -> Int => inc(1));")
                , testCase "a closure at the top calls a function of the program, run" (runs "fn inc(n: Int) -> Int { return n + 1; }; fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; g = fn(x: Int) -> Int => inc(x) * 10; return apply(&g, 1);" 20)
                , testCase "a closure's call of a function is checked against its contract" (rejected "fn positive(n: Int) -> Int [{ affirm n > 0; }] [{ }] { return n; }; f = fn() -> Int => positive(0); return f();" "Could not prove: n > 0")
                , testCase "a closure's contract follows from a function's" (valid "fn double(n: Int) -> Int [{ }] [{ affirm return = n * 2; }] { return n * 2; }; f = move fn(x: Int) -> Int [{ }] [{ affirm return = x * 2; }] => double(x); return f(3);")
                , testCase "a closure in a function calls a function of the program" (valid "fn inc(n: Int) -> Int { return n + 1; }; fn go() -> Int { f = fn() -> Int => inc(1); return f(); }; return go();")
                , testCase "map with a closure that calls a function of the program" (valid "fn double(x: Int) -> Int { return x * 2; }; xs = push(push([], 1), 2); ys = map(xs, fn(x) => double(x) + 1); return size(ys);")
                , testCase "a local holding a function is still captured" (runs "fn inc(n: Int) -> Int { return n + 1; }; g = inc; f = fn() -> Int => g(1); return f();" 2)
                , testCase "a closure that may not end is written with ~" (valid "fn spin(n: Int) -> Int [{ }] [{ }] ~ { return spin(n); }; fn once<U, F: FnOnce() -> U>(f: F) -> U { return f(); }; fn go() -> Int [{ }] [{ }] ~ { return once(fn() -> Int ~ => spin(0)); }; return 0;")
                , testCase "a ~ closure makes the copy that calls it ~, so a caller that ends is refused" (rejected "fn spin(n: Int) -> Int [{ }] [{ }] ~ { return spin(n); }; fn once<U, F: FnOnce() -> U>(f: F) -> U { return f(); }; fn go() -> Int [{ }] [{ }] { return once(fn() -> Int ~ => spin(0)); }; return 0;" "it may diverge, and go may not")
                , testCase "a ~ closure called directly from a function that ends is refused" (rejected "fn spin(n: Int) -> Int [{ }] [{ }] ~ { return spin(n); }; fn once<U, F: FnOnce() -> U>(f: F) -> U { return f(); }; fn go() -> Int [{ }] [{ }] { f = fn() -> Int ~ => spin(0); return f(); }; return 0;" "may diverge")
                , testCase "a closure that calls a ~ function has to be ~" (rejected "fn spin(n: Int) -> Int [{ }] [{ }] ~ { return spin(n); }; fn once<U, F: FnOnce() -> U>(f: F) -> U { return f(); }; fn go() -> Int [{ }] [{ }] ~ { return once(fn() -> Int => spin(0)); }; return 0;" "may diverge")
                , testCase "a ~ closure runs" (runs "n = 1; f = fn() -> Int ~ => n + 1; return f();" 2)
                , testCase "a ~ closure with contracts" (runs "n = 1; f = fn(x: Int) -> Int [{ affirm n > 0; }] [{ }] ~ => x + n; return f(2);" 3)
                , testCase "the clone of a ~ closure ends" (valid "fn go() -> Int [{ }] [{ }] { n = 1; f = fn() -> Int ~ => n; g = f.clone(); return 0; }; return go();")
                , testCase "a ~ impl through a bound makes the copy ~" (rejected "trait Step { fn step(self: &Self) -> Int [{ }] [{ }]; }; struct Spin { n: Int }; impl Step for Spin { fn step(self: &Self) -> Int [{ }] [{ }] ~ { return self.step(); }; }; fn go<S: Step>(s: &S) -> Int [{ }] [{ }] { return s.step(); }; fn f() -> Int [{ }] [{ }] { s = Spin { n: 0 }; return go(&s); }; return 0;" "it may diverge, and f may not")
                , testCase "a closure given to a function with bounds named like a permission builtin" (runs "fn start<F: FnOnce() -> Int>(f: F) -> Int { return f(); }; return start(fn() -> Int => 3);" 3)
                , testCase "a closure forwarded by a function with bounds named like a permission builtin" (valid "fn once<U, F: FnOnce() -> U>(f: F) -> U { return f(); }; fn count<V, F: FnOnce() -> V>(f: F) -> V { return once(f); }; n = 2; return count(fn() -> Int => n);")
                , testCase "a closure over a type parameter of the enclosing function" (runs "fn countOf<T>(xs: &List<T>, n: Int) -> Int { f = fn() -> Int => size(xs) + n; return f(); }; return countOf(push(push([], 1), 2), 10);" 12)
                , TestCase "many functions with lets and fn parameters" $ do
                    let defs = concat [ "fn f" ++ show i ++ "(fn: &List<Int>) -> Int { let a = size(fn); let b = a + " ++ show i ++ "; return b; }; " | i <- [1 .. 40 :: Integer] ]
                        calls = concat [ "f" ++ show i ++ "(&xs) + " | i <- [1 .. 40 :: Integer] ]
                        src = defs ++ "xs = push(push([], 1), 2); return " ++ calls ++ "0;"
                        expected = sum [ 2 + i | i <- [1 .. 40 :: Integer] ]
                    pure (runs src expected)
                , TestCase "a closure across modules" $ do
                    program <-
                        programFromFiles
                            "app/main.tersus"
                            [ ("app/package.tersus", "")
                            , ("app/main.tersus", "import app::apply; n = 10; return apply::apply(fn(x) => x + n, 5);")
                            , ("app/apply.tersus", "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); };")
                            ]
                    pure (testAssertEq (program `bindResult` MirEval.runProgram) (Ok (Just (MirEval.MInt 15))))
                ]
            , TestList
                "thin function contracts"
                [ testCase "a let shadow does not turn the outer contracted call into a function-value call"
                    (checked (increment ++ "{ let step = 7; step = step + 1; affirm step = 8; }; return step(41);") 42)
                , testCase "an assignment in another function does not reassign the contracted function"
                    (checked (increment ++ "fn local(step: Int) -> Int { if step > 0 { step = step + 1; }; return step; }; ignored = local(40); return step(41);") 42)
                , testCase "assigning the actual function binding in a nested block changes the call target"
                    (checked "fn step(x: Int) -> Int { return x + 1; }; fn twice(x: Int) -> Int { return x * 2; }; if 1 > 0 { step = twice; }; return step(21);" 42)
                , testCase "an assignment can initialize the binding before its function declaration"
                    (checked "fn twice(x: Int) -> Int { return x * 2; }; step = twice; n = step(10); fn step(x: Int) -> Int { return x + 2; }; return n + step(20);" 42)
                , testCase "conversion checks weaker precondition and stronger postcondition with positional names"
                    (checked (increment ++ "let f: " ++ positiveStep ++ " = step; r = f(41); affirm r > 41; return r;") 42)
                , testCase "different argument names and positions are preserved at call"
                    (checked ("fn sub(a: Int, b: Int) -> Int [{ affirm a > b; }] [{ affirm return = a - b; }] { return a - b; }; let f: fn(x: Int, y: Int) -> Int [{ affirm x > y; }] [{ affirm return = x - y; }] = sub; r = f(43, 1); affirm r = 42; return r;") 42)
                , testCase "an indirect call must meet the declared precondition"
                    (rejects (increment ++ "let f: " ++ positiveStep ++ " = step; return f(0);") "x > 0")
                , testCase "a stronger advertised result is refused at conversion, even without a call"
                    (rejects (increment ++ "let f: fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x + 5; }] = step; return 0;") "function conversion")
                , testCase "the caller cannot use the known named target's stronger postcondition"
                    (rejects (increment ++ "let f: fn(x: Int) -> Int [{ affirm x > 0; }] [{ }] = step; r = f(41); affirm r > 41; return r;") "r > 41")
                , testCase "implicit inference cannot discard a needed precondition"
                    (rejects (increment ++ "let f = step; return 0;") "function conversion")
                , testCase "an uncontracted parameter cannot receive a preconditioned function"
                    (rejects (increment ++ "fn ignore(f: fn(Int) -> Int) -> Int { return 0; }; return ignore(step);") "function conversion")
                , testCase "a return cannot discard a needed precondition"
                    (rejects (increment ++ "fn give() -> fn(Int) -> Int { return step; }; return 0;") "function conversion")
                , testCase "field construction cannot discard a needed precondition"
                    (rejects (increment ++ "struct Holder { f: fn(Int) -> Int }; h = Holder { f: step }; return 0;") "function conversion")
                , testCase "list inference cannot discard a needed precondition"
                    (rejects (increment ++ "xs = push([], step); return 0;") "function conversion")
                , testCase "branch selection cannot discard a needed precondition"
                    (rejects (increment ++ "fn id(x: Int) -> Int { return x; }; f = if argCount() > 1 { step } else { id }; return 0;") "function conversion")
                , testCase "an indirect result is unknown across multiple ordinary targets"
                    (checked "fn a(x: Int) -> Int { return x + 1; }; fn b(x: Int) -> Int { return x + 2; }; f = a; if 1 > 0 { f = b; }; return f(40);" 42)
                , testCase "a declared contract survives return and concrete field storage"
                    (checked (increment ++ "struct Holder { f: " ++ positiveStep ++ " }; fn give() -> (" ++ positiveStep ++ ") { return step; }; h = Holder { f: give() }; f = h.f; r = f(41); affirm r > 41; return r;") 42)
                , testCase "a plain function value meets Fn"
                    (checked "fn inc(x: Int) -> Int { return x + 1; }; fn use<F: Fn(Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; g = inc; return use(g, 41);" 42)
                , testCase "a function value meets a contracted Fn bound by proof"
                    (checked (increment ++ "fn use<F: Fn(arg: Int) -> Int [{ affirm arg > 0; }] [{ affirm return > arg; }]>(f: &F, x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] { return f(x); }; let g: " ++ positiveStep ++ " = step; return use(g, 41);") 42)
                , testCase "an Fn bound cannot discard a function value precondition"
                    (rejects (increment ++ "fn use<F: Fn(Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; let g: " ++ positiveStep ++ " = step; return use(g, 41);") "Could not prove")
                , testCase "a builtin through a pointer checks its declared input at the call"
                    (rejects "let f: fn(xs: &List<Int>) -> Int [{ affirm size(xs) > 0; }] = first; let xs: List<Int> = []; return f(xs);" "size(xs) > 0")
                , TestCase "builtin values with the same label link across packages and instantiations" $ do
                    program <-
                        programFromFiles
                            "pkgs/app/main.tersus"
                            [ ("pkgs/app/package.tersus", "")
                            , ("pkgs/app/main.tersus", "import ints::intheads as ints; import bools::boolheads as bools; if bools::headBool() { return ints::headInt() + bools::headInt(); }; return 0;")
                            , ("pkgs/ints/package.tersus", "")
                            , ("pkgs/ints/intheads.tersus", "fn headInt() -> Int { let f: fn(xs: &List<Int>) -> Int [{ affirm size(xs) > 0; }] = first; return f([20]); };")
                            , ("pkgs/bools/package.tersus", "")
                            , ("pkgs/bools/boolheads.tersus", "fn headBool() -> Bool { let f: fn(xs: &List<Bool>) -> Bool [{ affirm size(xs) > 0; }] = first; return f([true]); }; fn headInt() -> Int { let f: fn(xs: &List<Int>) -> Int [{ affirm size(xs) > 0; }] = first; return f([22]); };")
                            ]
                    let wrappers = mapResult (length . filter ("builtin::first#" `isPrefixOf`) . Map.keys . Mir.progFunctions) program
                    case testAssertEq (wrappers, program `bindResult` MirEval.runProgram) (Ok 3, Ok (Just (MirEval.MInt 42))) of
                        Just failure -> pure (Just failure)
                        Nothing -> case program of
                            Ok mir -> nativeMirCase "builtin values across packages" mir "42\n"
                            Error e -> pure (Just e)
                , testCase "a plain function value meets FnMut and FnOnce"
                    (checked "fn inc(x: Int) -> Int { return x + 1; }; fn mutate<F: FnMut(Int) -> Int>(f: &mut F) -> Int { return f(19); }; fn once<F: FnOnce(Int) -> Int>(f: F) -> Int { return f(21); }; p = inc; return mutate(p) + once(p);" 42)
                , testCase "termination cannot be justified by hiding recursion through a callback"
                    (rejects "fn apply(f: fn() -> Int) -> Int { return f(); }; fn cycle() -> Int { return apply(cycle); }; return cycle();" "potential recursion through a function value")
                , testCase "an indirect world reader does not give a deterministic result to its callers"
                    (rejects "fn read() -> Int { return readByte(); }; fn invoke(f: fn() -> Int) -> Int { return f(); }; f = read; a = invoke(f); b = invoke(f); affirm a = b; return 0;" "a = b")
                ]
            , TestList
                "higher-order library"
                [ testCase "map doubles a list" (runs "xs = push(push(push([], 1), 2), 3); ys = map(xs, fn(x) => x * 2); return get(ys, 2) * 10 + size(ys);" 63)
                , testCase "map with a capturing closure" (runs "factor = 3; xs = push(push([], 1), 2); ys = map(xs, fn(x) => x * factor); return get(ys, 1) * 10 + size(ys);" 62)
                , testCase "map with a named function" (runs "fn double(x: Int) -> Int { return x * 2; }; xs = push(push([], 1), 2); ys = map(xs, double); return get(ys, 1) * 10 + size(ys);" 42)
                , testCase "a caller proves with map's size contract" (runs "fn sameSize(xs: &List<Int>) -> Int [{ }] [{ affirm return = size(xs); }] { return size(map(xs, fn(x) => x * 2)); }; return sameSize(push(push([], 1), 2));" 2)
                , testCase "filter keeps what passes" (runs "xs = push(push(push([], 1), 2), 3); ys = filter(xs, fn(x) => x > 1); return size(ys) * 10 + get(ys, 0);" 22)
                , testCase "a caller proves with filter's size contract" (runs "fn keptAtMost(xs: &List<Int>) -> Int [{ }] [{ affirm return <= size(xs); }] { return size(filter(xs, fn(x) => x > 0)); }; return keptAtMost(push(push([], 1), 2));" 2)
                , testCase "fold sums and multiplies" (runs "xs = push(push(push([], 1), 2), 3); return fold(xs, 0, fn(acc, x) => acc + x) * 10 + fold(xs, 1, fn(acc, x) => acc * x);" 66)
                , testCase "fold over an empty list is the init" (runs "xs = []; return fold(xs, 41, fn(acc: Int, x: Int) => acc + x) + size(xs);" 41)
                , testCase "any and all" (runs "xs = push(push(push([], 1), 2), 3); r = 0; if any(xs, fn(x) => x > 2) { r = r + 10; }; if all(xs, fn(x) => x > 0) { r = r + 1; }; if any(xs, fn(x) => x > 9) { r = r + 100; }; return r;" 11)
                , testCase "find gives the index or -1" (runs "xs = push(push(push([], 1), 2), 3); return find(xs, fn(x) => x = 2) * 10 + find(xs, fn(x) => x > 9) + 1;" 10)
                , testCase "sortBy sorts ascending and descending" (runs "xs = push(push(push([], 3), 1), 2); up = sortBy(xs, fn(a, b) => a < b); down = sortBy(xs, fn(a, b) => a > b); return get(up, 0) * 1000 + get(up, 2) * 100 + get(down, 0) * 10 + size(up);" 1333)
                , testCase "an updating closure does not meet map's Fn bound" (rejected "xs = push([], 1); count = 0; ys = map(xs, fn(x) -> Int { count = count + 1; return x; }); return 0;" "is FnMut and cannot be given where Fn(...) is wanted")
                , testCase "mapArray doubles an array" (runs "a = #[1, 2, 3]; doubled = mapArray(a, fn(x) => x * 2); return get(doubled, 2) * 10 + size(doubled);" 63)
                , testCase "filterArray gives a list" (runs "a = #[1, 2, 3]; big = filterArray(a, fn(x) => x > 1); return size(big) * 10 + get(big, 0);" 22)
                , testCase "foldArray, findArray, anyArray, allArray" (runs "a = #[1, 2, 3]; r = foldArray(a, 0, fn(acc, x) => acc + x) * 100 + findArray(a, fn(x) => x = 2) * 10; if anyArray(a, fn(x) => x > 2) { r = r + 2; }; if allArray(a, fn(x) => x > 0) { r = r + 1; }; return r;" 613)
                , testCase "sortArrayBy sorts an array" (runs "a = #[3, 1, 2]; sorted = sortArrayBy(a, fn(x, y) => x < y); return get(sorted, 0) * 100 + get(sorted, 2) * 10 + size(sorted);" 133)
                ]
            ]

closureAdder :: String
closureAdder = "struct Adder { n: Int }; impl Fn(x: Int) -> Int for Adder { fn call(self: &Self, x: Int) -> Int { return x + self.n; }; }; "

closureCounter :: String
closureCounter = "struct Counter { count: Int }; impl FnMut() -> Int for Counter { fn call(self: &mut Self) -> Int { (*self).count = (*self).count + 1; return (*self).count; }; }; "

closureModuleFiles :: [(FilePath, String)]
closureModuleFiles =
    [ ("app/package.tersus", "")
    , ("app/main.tersus", "import app::apply; " ++ closureAdder ++ "a = Adder { n: 10 }; return apply::apply(&a, 5);")
    , ("app/apply.tersus", "fn apply<F: Fn(x: Int) -> Int>(f: &F, x: Int) -> Int { return f(x); };")
    ]
