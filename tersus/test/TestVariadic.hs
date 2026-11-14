module TestVariadic (testVariadic, variadicPrograms) where

import Data.List (isInfixOf)

import Cli (Command (..), runSource)
import Syntax
import TestHarness
import TestParserFragments (parseStatementBlock)
import Types (Signature (..), Type (..))
import TestModules (phase2Files, phase2Rejects, phase2Runs)
import TestNative (sameAsMir)
import Utils (Result (..))

-- Variadic functions (LANGUAGE.md, "Variadic functions"): `fn f<..T: B>(args: &..T)` takes any number of trailing arguments,
-- each of a type that meets the bounds. The body is checked once against the bounds alone, with each element of the pack a type of
-- its own, and each call's copy has one parameter per argument, size(args) a number, get(args, k) the parameter at k, its loops
-- over the pack unrolled and the branches it does not take dropped.
testVariadic :: Test
testVariadic =
    let runs body (VInt expected) = testAssertEq (runSource Interpret body) (Ok (show expected))
        runs _ other = Just ("not a number: " ++ show other)
        refused source needle = case runSource Check source of
            Error err | needle `isInfixOf` err -> Nothing
            Error err -> Just ("expected " ++ show needle ++ ", got: " ++ err)
            Ok _ -> Just ("accepted instead of refusing with " ++ show needle)
        rejected = refused
     in TestList
            "testVariadic"
            [ TestList
                "parser"
                [ testCase "a pack and a lent pack parameter make a function with bounds" (parsedHeader "fn f<..T: B>(args: &..T) -> Int { return 0; };" $ \bounds ptys -> if bounds == [("..T", "B", [])] && ptys == [TRef (TParam "..T")] then Nothing else Just (show (bounds, ptys)))
                , testCase "a pack with no bound and a pack taken by value too" (parsedHeader "fn f<K, ..T>(k: K, args: ..T) -> Int { return 0; };" $ \bounds ptys -> if null bounds && ptys == [TParam "K", TParam "..T"] then Nothing else Just (show (bounds, ptys)))
                , testCase "for a in args is a loop over the pack that takes its elements" (packLoopOf "for a in args { }" $ \(i, a, p, takes) -> if take 7 i == "$index " && a == "a" && p == "args" && takes then Nothing else Just (show (i, a, p, takes)))
                , testCase "for a in &args reads them" (packLoopOf "for a in &args { }" $ \(_, a, _, takes) -> if a == "a" && not takes then Nothing else Just (show (a, takes)))
                , testCase "for i, a in args names both" (packLoopOf "for i, a in args { }" $ \(i, a, _, _) -> if (i, a) == ("i", "a") then Nothing else Just (show (i, a)))
                , testCase "for i in 0..size(args) is a loop over the pack" (packLoopOf "for i in 0..size(args) { }" $ \(i, a, _, takes) -> if i == "i" && take 9 a == "$element " && not takes then Nothing else Just (show (i, a, takes)))
                , testCase "a loop over a list in a variadic function is not" (case parseStatementBlock "fn f<..T>(args: &..T) -> Int { l = []; for x in l { }; return 0; };" of
                    Right stmts | null [() | s' <- stmts, PackLoop{} <- bodyOf s'] -> Nothing
                    other -> Just (show other))
                ]
            , TestList
                "syntax and bounds"
                [ testCase "a pack with no bound" (runs (count ++ "return count(1, true, push([], 2)) * 10 + count();") (VInt 30))
                , testCase "a pack with two bounds" (runs (measure ++ "trait Named { }; impl Named for Int { }; impl Named for Bool { }; fn both<..T: Measure + Named>(args: &..T) -> Int { t = 0; for a in args { t = t + a.measure(); }; return t; }; return both(3, true, 4);") (VInt 8))
                , testCase "a fixed parameter before the pack" (runs (measure ++ "fn log<K: Measure, ..T: Measure>(key: K, args: &..T) -> Int { t = key.measure() * 100; for a in args { t = t + a.measure(); }; return t; }; return log(2, true, 5);") (VInt 206))
                , testCase "a trait parameter is one type across the pack" (runs "fn firsts<E: Clone, ..S: Sequence<E>>(seqs: &..S) -> Int { n = 0; for s in seqs { n = n + s.size(); }; return n; }; return firsts(push(push([], 1), 2), #[3, 4, 5]);" (VInt 5))
                , testCase "and is refused when the arguments disagree" (refused "fn firsts<E: Clone, ..S: Sequence<E>>(seqs: &..S) -> Int { return size(seqs); }; return firsts(push([], 1), push([], true));" "firsts needs S (argument 2, List<Bool>) to implement Sequence<Int>")
                , testCase "an argument that does not meet the bound is named by its position" (refused (measure ++ "struct P { x: Int }; fn show<..T: Measure>(args: &..T) -> Int { return size(args); }; return show(1, P { x: 1 });") "show needs T (argument 2, P) to implement Measure")
                , testCase "fewer arguments than the fixed parameters" (refused (measure ++ "fn log<K: Measure, ..T: Measure>(key: K, args: &..T) -> Int { return 0; }; return log();") "log takes at least 1 arguments, got 0")
                ]
            , TestList
                "operations"
                [ testCase "size" (runs "fn n<..T>(args: &..T) -> Int { return size(args); }; return n(1, true, 3) * 10 + n();" (VInt 30))
                , testCase "get at a number and at a folded index" (runs (measure ++ "fn two<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 2; }] [{ }] { return get(args, 0).measure() * 10 + get(args, 2 - 1).measure(); }; return two(4, true);") (VInt 41))
                , testCase "for a in args, for i in 0..size(args) and for i, a in args" (runs (measure ++ "fn loops<..T: Measure>(args: &..T) -> Int { t = 0; for a in args { t = t + a.measure(); }; for i in 0..size(args) { t = t + i * 100; }; for i, a in args { t = t + i * a.measure() * 1000; }; return t; }; return loops(3, true);") (VInt 1104))
                , testCase "an index of a loop over the pack indexes it" (runs (measure ++ "fn idx<..T: Measure>(args: &..T) -> Int { t = 0; for i in 0..size(args) { t = t * 10 + get(args, i).measure(); }; return t; }; return idx(1, 2, 3);") (VInt 123))
                , testCase "nested loops are N times M copies" (runs (measure ++ "fn pairs<..T: Measure>(args: &..T) -> Int { t = 0; for a in args { for b in args { t = t + a.measure() * b.measure(); }; }; return t; }; return pairs(1, 2, 3);") (VInt 36))
                , testCase "a return in a loop" (runs (measure ++ "fn firstBig<..T: Measure>(args: &..T) -> Int { for a in args { if a.measure() > 2 { return a.measure(); }; }; return 0; }; return firstBig(1, 5, 7) * 10 + firstBig(1);") (VInt 50))
                , testCase "after a range loop the index is size(args)" (runs "fn after<..T>(args: &..T) -> Int { for i in 0..size(args) { }; return i; }; return after(1, 2, true);" (VInt 3))
                , testCase "a branch a copy does not take is dropped, with its get" (runs (measure ++ "fn head<..T: Measure>(args: &..T) -> Int { if size(args) > 0 { return get(args, 0).measure(); }; return 0 - 1; }; return head(7, true) * 10 + head();") (VInt 69))
                , testCase "no arguments, one, and seventeen" (runs (count ++ "return count() * 10000 + count(1) * 100 + count(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, true);") (VInt 117))
                ]
            , TestList
                "copies and trait contracts"
                [ testCase "a pack element's method gives a copy only the trait's contract" (refused "trait W { fn w(self: &Self) -> Int [{ }] [{ }]; }; impl W for Int { fn w(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; impl W for Bool { fn w(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; fn sum<..T: W>(args: &..T) -> Int [{ }] [{ affirm return >= 0; }] { t = 0; for a in args { t = t + a.w(); }; return t; }; return sum(1, true);" "Could not prove: return >= 0 (in sum[Int, Bool])")
                , testCase "and what the trait promises is enough" (runs (measure ++ "fn sum<..T: Measure>(args: &..T) -> Int [{ }] [{ affirm return >= 0; }] { t = 0; for a in args { t = t + a.measure(); }; return t; }; return sum(0 - 3, true);") (VInt 4))
                ]
            , TestList
                "element types"
                [ testCase "the same number is the same type" (runs "fn same<..T>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { x = get(args, 0); x = get(args, 0); return size(args); }; return same(1, true);" (VInt 2))
                , testCase "two numbers are two types" (refused "fn two<..T>(args: &..T) -> Int [{ affirm size(args) >= 2; }] [{ }] { x = get(args, 0); x = get(args, 1); return 0; }; return two(1, 2);" "expected the type of get(args, 0), got the type of get(args, 1)")
                , testCase "and are not compared" (refused "fn eq<..T: Eq>(args: &..T) -> Bool [{ affirm size(args) >= 2; }] [{ }] { return get(args, 0) = get(args, 1); }; return eq(1, 1);" "the type of get(args, 1)")
                , testCase "a loop's element and get on its index are one type" (runs "fn one<..T: Eq>(args: &..T) -> Int { n = 0; for i, a in args { if a = get(args, i) { n = n + 1; }; }; return n; }; return one(1, true);" (VInt 2))
                ]
            , TestList
                "refusals"
                [ testCase "the pack is not a value" (refused "fn f<..T>(args: &..T) -> Int { x = args; return 0; }; return f(1);" "args is a pack of arguments, not a value")
                , testCase "a method of the pack is not called" (refused "fn f<..T>(args: &..T) -> Int { return args.size(); }; return f(1);" "args is a pack of arguments, not a value")
                , testCase "the pack is given to another function only to fill its pack" (refused "fn g(x: &Int) -> Int { return 0; }; fn f<..T>(args: &..T) -> Int { return g(args); }; return f(1);" "args is given to g, which has no pack")
                , testCase "an index that is not fixed in each copy" (refused "fn f<..T>(args: &..T) -> Int { j = 0; x = get(args, j); return 0; }; return f(1);" "needs an index that is fixed in each copy")
                , testCase "a reference result is not from the pack" (refused "fn f<..T>(l: &List<Int>, args: &..T) -> &List<Int> from args { return l; }; return 0;" "a reference result is from one parameter")
                , testCase "two packs" (refused "fn f<..T, ..U>(args: &..T) -> Int { return 0; }; return 0;" "f has two packs of types")
                , testCase "the pack parameter is the last" (refused "fn f<..T>(args: &..T, x: Int) -> Int { return 0; }; return 0;" "the pack parameter args is the last parameter of f")
                , testCase "a pack the function does not have" (refused "fn f<..T>(args: &..U) -> Int { return 0; }; return 0;" "..U is not a pack of types of f")
                , testCase "a pack of types with no pack parameter" (refused "fn f<..T>(x: Int) -> Int { return 0; }; return 0;" "f has the pack of types ..T and no pack parameter")
                , testCase "a pack of types in another type" (refused "fn f<..T>(args: &..T) -> List<..T> { return []; }; return 0;" "..T is a pack of types: only the pack parameter has it")
                , testCase "a loop over a pack has no invariant" (refused "fn f<..T>(args: &..T) -> Int { for a in args [{ affirm true; }] { }; return 0; }; return 0;" "a loop over a pack is unrolled: it has no invariant")
                , testCase "a loop over a pack does not assign its element" (refused "fn f<..T>(args: ..T) -> Int { for a in args { a = 1; }; return 0; }; return 0;" "cannot assign its element a")
                ]
            , TestList
                "ownership"
                [ testCase "a lent pack leaves the arguments with the caller" (runs (count ++ "l = push([], 1); n = count(l, l); return size(l) + n;") (VInt 3))
                , testCase "a pack taken by value moves the arguments" (rejected "fn take<..T>(args: ..T) -> Int { return size(args); }; l = push([], 1); x = take(l); return size(l);" "moved")
                , testCase "an element of a pack taken by value is moved once" (runs (eat ++ "fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 2; }] [{ }] { return eat(get(args, 0)) + eat(get(args, 1)); }; return f(push([], 1), push([], 2));") (VInt 2))
                , testCase "and not twice" (refused (eat ++ "fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return eat(get(args, 0)) + eat(get(args, 0)); }; return 0;") "get(args, 0)")
                , testCase "an element of a lent pack is not moved" (refused (eat ++ "fn f<..T>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return eat(get(args, 0)); }; return 0;") "get(args, 0)")
                , testCase "an element at an index that is not a number is not moved" (refused (eat ++ "fn f<..T>(args: ..T) -> Int { n = 0; for i in 0..size(args) { n = n + eat(get(args, i)); }; return n; }; return 0;") "args")
                , testCase "for a in args takes the elements of a pack taken by value" (runs (eat ++ "fn f<..T>(args: ..T) -> Int { n = 0; for a in args { n = n + eat(a); }; return n; }; return f(push([], 1), true);") (VInt 2))
                , testCase "and its elements are not used after it, though its size is" (refused (eat ++ "fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { n = 0; for a in args { n = n + eat(a); }; return n + size(args) + eat(get(args, 0)); }; return 0;") "args was taken by the loop over it")
                , testCase "for a in &args keeps it" (runs "fn f<..T>(args: ..T) -> Int { n = 0; for a in &args { n = n + 1; }; return n + size(args); }; return f(push([], 1), true);" (VInt 4))
                , testCase "an element of a Copy pack is used twice" (runs (eat ++ "fn f<..T: Copy>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return eat(get(args, 0)) + eat(get(args, 0)); }; return f(1);") (VInt 2))
                ]
            , TestList
                "contracts"
                [ testCase "a requires on size(args) met" (runs (measure ++ "fn two<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return get(args, 0).measure(); }; return two(5);") (VInt 5))
                , testCase "and not met" (rejected (measure ++ "fn two<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return get(args, 0).measure(); }; return two();") "")
                , testCase "a forall over the pack is proved at the call and used in the body" (runs (measure ++ "fn total<..T: Measure>(args: &..T) -> Int [{ affirm forall i in 0..size(args): Measure::measure(get(args, i)) >= 0; }] [{ affirm return >= 0; }] { t = 0; for a in args { t = t + a.measure(); }; return t; }; return total(3, true, 4);") (VInt 8))
                , testCase "an element out of range is refused by the validator" (rejected "fn f<..T>(args: &..T) -> Int { x = get(args, 1); return 0; }; return f(1);" "Could not prove")
                , testCase "and is accepted on a path the contract rules out" (runs "fn f<..T>(flag: Bool, args: &..T) -> Int [{ affirm flag = false; }] [{ }] { if flag { x = get(args, 1); return 1; }; return 0; }; return f(false, 1);" (VInt 0))
                , testCase "and on a branch the copy does not take" (runs "fn f<..T>(args: &..T) -> Int { if size(args) >= 2 { x = get(args, 1); return 1; }; return 0; }; return f(1);" (VInt 0))
                ]
            , TestList
                "copies follow what the program does"
                [ testCase "a local written through &mut is not folded" (runs (measure ++ "fn bump(x: &mut Int) -> Int [{ }] [{ }] { *x = *x + 1; return 0; }; fn f<..T: Measure>(args: &..T) -> Int { n = 0; z = bump(&mut n); if n = 0 { return 100; }; return get(args, 0).measure(); }; return f(5);") (VInt 5))
                , testCase "nor one written through a reference to it" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { n = 0; r = &mut n; *r = 1; if n = 0 { return get(args, 5).measure(); }; return 7; }; return f(5);") (VInt 7))
                , testCase "an element read at a computed index has its argument's type" (runs (measure ++ "fn lastOf<..T: Measure>(args: &..T) -> Int { if size(args) > 0 { return get(args, size(args) - 1).measure(); }; return 0; }; return lastOf(3, true, 5) * 10 + lastOf(true);") (VInt 51))
                , testCase "in each iteration of a loop" (runs (measure ++ "fn pairs<..T: Measure>(args: &..T) -> Int { s = 0; for i in 0..size(args) - 1 { s = s + get(args, i + 1).measure() * 10 + get(args, i).measure(); }; return s; }; return pairs(1, true, 7);") (VInt 82))
                , testCase "and given to a function written for any type" (runs (measure ++ "fn eat<T>(x: &T) -> Int { return 1; }; fn f<..T: Measure>(args: &..T) -> Int { t = 0; for i in 1..size(args) + 1 { t = t + eat(get(args, i - 1)); }; return t; }; return f(1, true);") (VInt 2))
                , testCase "a range loop past the pack that reads no element" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { t = 0; for i in 0..size(args) + 1 { t = t + i; }; return t; }; return f(1, true);") (VInt 3))
                , testCase "a function defined in a loop over the pack, with several arguments" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { fn inner(x: Int) -> Int { return x + 1; }; t = 0; for a in args { fn twice(y: Int) -> Int { return y * 2; }; t = t + twice(a.measure()) + inner(0); }; return inner(size(args)) * 100 + t; }; return f(3, true) * 1000 + f();") (VInt 310100))
                , testCase "a forall over the pack at a computed index" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm forall i in 0..size(args) - 1: Measure::measure(get(args, i + 1)) >= 0; }] [{ }] { return size(args); }; return f(1, true);") (VInt 2))
                , testCase "an assumed forall over the pack" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { assume forall i in 0..size(args): Measure::measure(get(args, i)) >= 0; return size(args); }; return f(1, true);") (VInt 2))
                , testCase "a define of size(args)" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { define n = size(args); affirm n = size(args); return size(args); }; return f(1, true);") (VInt 2))
                , testCase "and what it says is checked" (refused (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { define n = size(args); affirm n = 7; return 0; }; return f(1, true);") "Could not prove")
                , testCase "a loop's element is not kept after it" (refused (measure ++ "fn f<..T: Measure + Clone>(args: &..T) -> Int { xs = []; for a in args { xs = push(xs, clone(a)); }; return size(xs); }; return f(1, true);") "xs would keep an element of args after the loop over it")
                , testCase "even when the body reads it back" (refused (measure ++ "fn f<..T: Measure + Clone>(args: &..T) -> Int { xs = []; s = 0; for a in args { xs = push(xs, clone(a)); s = s * 100 + get(xs, 0).measure(); }; return s; }; return f(0 - 4, true);") "xs would keep an element of args")
                , testCase "nor is an element read at a computed index in the loop" (refused (measure ++ "fn f<..T: Measure + Clone>(args: &..T) -> Int { xs = []; for i in 0..size(args) { xs = push(xs, clone(get(args, i + 0))); }; return size(xs); }; return f(1, true);") "xs would keep an element of args")
                , testCase "an element a taking loop moved twice is named as itself" (refused (eat ++ "fn f<..T>(args: ..T) -> Int { n = 0; for a in args { n = n + eat(a) + eat(a); }; return n; }; return f(push([], 1));") "a was moved")
                , testCase "an element of a lent pack is not moved out of the pack" (refused (eat ++ "fn f<..T>(args: &..T) -> Int { n = 0; for a in args { n = n + eat(a); }; return n; }; return f(push([], 1));") "out of the pack args")
                , testCase "nor one read by for a in &args" (refused (eat ++ "fn f<..T>(args: ..T) -> Int { n = 0; for a in &args { n = n + eat(a); }; return n; }; return f(push([], 1));") "out of the pack args")
                ]
            , TestList
                "proofs, defines and definitions in copies"
                [ testCase "an affirm in a loop reads the pack at the loop's index" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { for i, a in args { affirm Measure::measure(get(args, i)) = Measure::measure(a); }; return size(args); }; return f(5, true);") (VInt 2))
                , testCase "and at an index computed from it" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { for i in 1..size(args) { affirm Measure::measure(get(args, i - 1)) >= 0; }; return size(args); }; return f(5, true);") (VInt 2))
                , testCase "a define in a loop reads the pack at the loop's index" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { for i, a in args { define m = Measure::measure(get(args, i)); affirm m >= 0; }; return size(args); }; return f(5, true);") (VInt 2))
                , testCase "a define of an element is the argument" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define m = get(args, 0); return 1; }; return f(4);") (VInt 1))
                , testCase "and of a call through its bound, the impl's function" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define m = Measure::measure(get(args, 0)) + 0; affirm m >= 0; return 1; }; return f(4);") (VInt 1))
                , testCase "a function defined in a branch a copy drops" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { t = 0; if size(args) > 0 { fn twice(y: Int) -> Int { return y * 2; }; t = twice(get(args, 0).measure()); }; return t; }; return f() + f(2);") (VInt 4))
                , testCase "and in a loop over the pack in such a branch" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { t = 0; if size(args) > 0 { for a in args { fn twice(y: Int) -> Int { return y * 2; }; t = t + twice(a.measure()); }; }; return t; }; return f();") (VInt 0))
                , testCase "a generic struct holds an element" (runs (measure ++ "struct Hold<U> { u: U }; fn f<..T: Measure + Clone>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { h = Hold { u: clone(get(args, 0)) }; return h.u.measure(); }; return f(5);") (VInt 5))
                , testCase "and a loop's element in its iteration" (runs (measure ++ "struct Hold<U> { u: U }; fn f<..T: Measure + Clone>(args: &..T) -> Int { t = 0; for a in args { h = Hold { u: clone(a) }; t = t + h.u.measure(); }; return t; }; return f(5, true);") (VInt 6))
                , testCase "but not after it" (refused (measure ++ "struct Hold<U> { u: List<U> }; fn f<..T: Measure + Clone>(args: &..T) -> Int { h = Hold { u: [] }; for a in args { h = Hold { u: push([], clone(a)) }; }; return 0; }; return f(1, true);") "h would keep an element of args after the loop over it, which reads it as a")
                , testCase "an element a range loop reads is named by its get" (refused (measure ++ "fn f<..T: Measure + Clone>(args: &..T) -> Int { xs = []; for i in 0..size(args) { xs = push([], clone(get(args, i))); }; return size(xs); }; return f(1, true);") "which reads it as get(args, i):")
                , testCase "two element types are told apart" (refused (measure ++ "fn f<..T: Measure + Clone>(args: &..T) -> Int { t = 0; for i in 0..size(args) { x = clone(get(args, i)); for b in args { x = clone(get(args, i * 1)); }; t = t + x.measure(); }; return t; }; return f(1, 5);") "expected the type of get(args, i), got the type of get(args, i * 1)")
                , testCase "an index out of range is named with its line" (refused (measure ++ "fn f<..T: Measure>(args: &..T) -> Int {\n s = 0;\n for i in 0..size(args) { s = s + get(args, i + 1).measure(); };\n return s;\n};\nreturn f(1, 2);") "Could not prove: the index 2 of get(args, ...) at line 3:")
                , testCase "a forall over the pack with bounds no copy fixes is refused where it is written" (refused (measure ++ "fn f<..T: Measure>(n: Int, args: &..T) -> Int [{ affirm forall i in 0..n: Measure::measure(get(args, i)) >= 0; }] [{ }] { return size(args); }; return 0;") "a forall over the elements of args is written forall i in lo..hi with bounds fixed in each copy")
                ]
            , TestList
                "defines and nested functions across iterations"
                [ testCase "a define of an element at an index built from size(args), and a call through its bound on it" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define k = get(args, size(args) - 1); affirm Measure::measure(k) >= 0; return 1; }; return f(4) + f(4, true) - 1;") (VInt 1))
                , testCase "beside a forall and a define at a number" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { affirm forall i in 0..size(args): Measure::measure(get(args, i)) >= 0; define m = Measure::measure(get(args, 0)); define k = get(args, size(args) - 1); affirm m >= 0; affirm Measure::measure(k) >= 0; return 1; }; return f(4) + f(4, true) - 1;") (VInt 1))
                , testCase "a define in a loop over the pack read in a loop inside it" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { for i, a in args { define m = i; for b in args { affirm m >= 0; }; }; return size(args); }; return f(5, true);") (VInt 2))
                , testCase "of a call through the bound of the element" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { for i in 0..size(args) { define m = Measure::measure(get(args, i)); for b in args { affirm m >= 0; }; }; return size(args); }; return f(5, true);") (VInt 2))
                , testCase "an index out of range in an affirm is named with its line" (refused (measure ++ "fn f<..T: Measure>(args: &..T) -> Int {\n for i in 0..size(args) { affirm Measure::measure(get(args, i + 1)) >= 0; };\n return size(args);\n};\nreturn f(5, true);") "Could not prove: the index 2 of get(args, ...) at line 2:")
                ]
            , TestList
                "defines of elements a copy does not have"
                [ testCase "a define of an element a copy has no argument for, on a path the call rules out" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define k = get(args, 0); affirm Measure::measure(k) >= 0; return 4; }; n = 0; if n > 0 { return f(); }; return f(4);") (VInt 4))
                , testCase "is the index's obligation where the copy runs it" (refused (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { define k = get(args, 0); affirm Measure::measure(k) >= 0; return 4; }; return f();") "Could not prove: the index 0 of get(args, ...) at line 1:")
                , testCase "and leaves the call to answer for the contract" (refused (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define k = get(args, size(args) - 1); affirm Measure::measure(k) >= 0; return 1; }; return f();") "Could not prove: 0 >= 1 (in main)")
                , testCase "as does a define of a call on one" (refused (measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define m = Measure::measure(get(args, 0)); affirm m >= 0; return 1; }; return f();") "Could not prove: 0 >= 1 (in main)")
                , testCase "a define in a loop over the pack read by the invariant of a loop in it" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { for a in args { define m = Measure::measure(a); j = 0; while j < 2 [{ affirm j >= 0; affirm j <= 2; affirm m >= 0; }] shrinks 2 - j { j = j + 1; }; }; return size(args); }; return f(5, true);") (VInt 2))
                , testCase "a define outside the loop read before the body defines the name again" (runs (measure ++ "fn f<..T: Measure>(args: &..T) -> Int { define m = size(args); for a in args { affirm m >= 0; define m = 5; }; return size(args); }; return f(5, true);") (VInt 2))
                ]
            , TestList
                "forwarding"
                [ testCase "the whole pack" (runs (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { return total(args); }; return f(1, true, 3);") (VInt 5))
                , testCase "a slice with numbers" (runs (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 3; }] [{ }] { return total(slice(args, 1, 3)); }; return f(1, true, 3);") (VInt 4))
                , testCase "a slice per iteration of a loop over the pack" (runs (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { t = 0; for i in 0..size(args) { t = t * 10 + total(slice(args, i, size(args))); }; return t; }; return f(1, 2, 3);") (VInt 653))
                , testCase "after fixed arguments" (runs (measure ++ "fn g<..U: Measure>(k: Int, rest: &..U) -> Int { t = k; for a in rest { t = t + a.measure(); }; return t; }; fn f<..T: Measure>(args: &..T) -> Int { return g(10, args); }; return f(1, true);") (VInt 12))
                , testCase "after plain arguments that fill the callee's pack first" (runs (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { return total(5, args); }; return f(1, true);") (VInt 7))
                , testCase "recursion through a shrinking slice, with no shrinks" (runs (measure ++ sumRec ++ "return sum(1, true, 3) * 10 + sum();") (VInt 50))
                , testCase "on 17 arguments" (runs (measure ++ sumRec ++ "return sum(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, true);") (VInt 137))
                , testCase "by value, moving the head and forwarding the rest" (runs (eat ++ "fn cnt<..T>(args: ..T) -> Int { if size(args) = 0 { return 0; }; return eat(get(args, 0)) + cnt(slice(args, 1, size(args))); }; return cnt(push([], 1), push([], 2));") (VInt 2))
                , testCase "the head given as an argument of the same call" (runs (eat ++ headRest ++ "fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return g(get(args, 0), slice(args, 1, size(args))); }; return f(push([], 1), push([], 2));") (VInt 2))
                , testCase "the head moved into a variable first" (runs (eat ++ headRest ++ "fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { a = get(args, 0); return g(a, slice(args, 1, size(args))); }; return f(push([], 1), push([], 2));") (VInt 2))
                , testCase "the head given with the rest lent" (runs (eat ++ "fn g<A, ..U>(x: A, rest: &..U) -> Int { return eat(x) + size(rest); }; fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return g(get(args, 0), slice(args, 1, size(args))); }; return f(push([], 1), push([], 2), true);") (VInt 3))
                , testCase "the head borrowed while the rest is forwarded by value" (runs (eat ++ "fn sz<T>(r: &T) -> Int { return 10; }; fn h<..U>(rest: ..U) -> Int { n = 0; for a in rest { n = n + eat(a); }; return n; }; fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { r = &get(args, 0); n = h(slice(args, 1, size(args))); return n + sz(r); }; return f(push([], 1), push([], 2), true);") (VInt 12))
                , testCase "but not an element moved inside the part forwarded" (refused (eat ++ "fn h<..U>(rest: ..U) -> Int { return 0; }; fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 2; }] [{ }] { n = eat(get(args, 1)); return h(slice(args, 1, size(args))); }; return f(1, 2);") "was moved")
                , testCase "forwarding the whole pack to itself does not end" (refused "fn f<..T>(args: &..T) -> Int { return f(args); }; return f(1);" "Could not prove")
                , testCase "a forward that grows the pack is refused" (refused "fn f<..T>(args: &..T) -> Int { if size(args) < 3 { return f(0, args); }; return 0; }; return f();" "f calls itself with the types Int")
                , testCase "an unguarded slice past an empty pack is refused with its bounds" (refused (measure ++ total ++ "fn r<..T: Measure>(args: &..T) -> Int {\n return total(slice(args, 1, size(args)));\n};\nreturn r();") "Could not prove: the start 1 of slice(args, ...) at line 2:")
                , testCase "and past the end of the pack" (refused (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { return total(slice(args, 0, 3)); }; return f(1, 2);") "the end 3 of slice(args, ...)")
                , testCase "accepted under a guard" (runs (measure ++ total ++ "fn r<..T: Measure>(args: &..T) -> Int { if size(args) > 0 { return total(slice(args, 1, size(args))); }; return 0; }; return r() + r(4, 5);") (VInt 5))
                , testCase "and under a contract" (runs (measure ++ total ++ "fn r<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { return total(slice(args, 1, size(args))); }; return r(4, 5);") (VInt 5))
                , testCase "the caller's bounds meet the callee's" (runs (measure ++ total ++ "fn f<..T: Measure + Clone>(args: &..T) -> Int { return total(args); }; return f(2, 3);") (VInt 5))
                , testCase "a bound of the callee the caller lacks is refused where the forward is written" (refused "trait Measure { fn measure(self: &Self) -> Int; }; fn h<..U: Measure>(rest: &..U) -> Int { return 0; }; fn f<..T>(args: &..T) -> Int { return h(args); }; return 0;" "f forwards args to h, which needs each element of its pack U to implement Measure, and the bounds of ..T in f do not say it: add Measure to them")
                , testCase "trait parameters solved across the forward" (runs "fn lens<E, ..S: Sequence<E>>(seqs: &..S) -> Int { n = 0; for s in seqs { n = n + size(s); }; return n; }; fn f<E, ..T: Sequence<E>>(args: &..T) -> Int { return lens(args); }; return f(push([], 1), push(push([], 2), 3));" (VInt 3))
                , testCase "a lent pack keeps its elements" (runs (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { return total(args) + total(args); }; return f(1, 2);") (VInt 6))
                , testCase "a pack taken by value lent to a lent pack is kept" (runs (measure ++ total ++ "fn f<..T: Measure>(args: ..T) -> Int { t = total(args); return t + size(args); }; return f(1, true);") (VInt 4))
                , testCase "and given to a pack taken by value moves its elements" (runs (eat ++ "fn h<..U>(rest: ..U) -> Int { n = 0; for a in rest { n = n + eat(a); }; return n; }; fn f<..T>(args: ..T) -> Int { return h(args); }; return f(push([], 1), push([], 2));") (VInt 2))
                , testCase "after which the pack is not used" (refused (eat ++ "fn h<..U>(rest: ..U) -> Int { return 0; }; fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { n = h(args); return eat(get(args, 0)); }; return f(1);") "args was forwarded at line 1:")
                , testCase "a lent pack is not forwarded to a pack taken by value" (refused "fn h<..U>(rest: ..U) -> Int { return 0; }; fn f<..T>(args: &..T) -> Int { return h(args); }; return 0;" "args is lent to f (&..T), so it can be forwarded only to a lent pack, and h takes its pack by value")
                , testCase "the callee's contract is met in one copy" (runs (measure ++ need ++ "fn f<..T: Measure>(args: &..T) -> Int { return need(slice(args, 1, size(args))); }; return f(1, 2);") (VInt 1))
                , testCase "and refused in another" (refused (measure ++ need ++ "fn f<..T: Measure>(args: &..T) -> Int { return need(slice(args, 1, size(args))); }; return f(1);") "Could not prove: 0 >= 1 (in f[Int])")
                , testCase "a method takes a forwarded pack" (runs (measure ++ "struct S { k: Int }; impl S { fn add<..U: Measure>(self: &Self, rest: &..U) -> Int { t = self.k; for a in rest { t = t + a.measure(); }; return t; }; }; fn f<..T: Measure>(args: &..T) -> Int { s = S { k: 100 }; return s.add(args) + S::add(&s, slice(args, 1, size(args))); }; return f(1, true);") (VInt 203))
                , testCase "to a plain function, refused" (refused "fn p(x: Int) -> Int { return x; }; fn f<..T>(args: &..T) -> Int { return p(args); }; return 0;" "args is given to p, which has no pack")
                , testCase "to a function written for any type, refused" (refused "fn eat<T>(x: &T) -> Int { return 1; }; fn f<..T>(args: &..T) -> Int { return eat(args); }; return 0;" "args is given to eat, which has no pack: a pack is forwarded only to the pack parameter of a variadic function")
                , testCase "to a function with bounds and no pack, refused" (refused (measure ++ "fn one<T: Measure>(x: &T) -> Int { return 1; }; fn f<..T: Measure>(args: &..T) -> Int { return one(args); }; return 0;") "one has no pack: args is forwarded only to the pack parameter of a variadic function")
                , testCase "to a builtin, refused" (refused "fn f<..T>(args: &..T) -> Int { x = push([], args); return 0; }; return 0;" "args is given to push, which has no pack")
                , testCase "not as the last argument, refused" (refused (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { return total(args, 1); }; return 0;") "args is forwarded only as the last argument of a call, where it fills the callee's pack, and once")
                , testCase "twice in one call, refused" (refused (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { return total(args, args); }; return 0;") "and once")
                , testCase "a slice that is not forwarded, refused" (refused "fn f<..T>(args: &..T) -> Int { x = slice(args, 0, 1); return 0; }; return 0;" "slice(args, a, b) is only given as the last argument of a call to a variadic function")
                , testCase "a loop over a slice, refused" (refused "fn f<..T>(args: &..T) -> Int { for a in slice(args, 0, 1) { }; return 0; }; return 0;" "to loop over a part of the pack, write for i in a..b and get(args, i)")
                , testCase "slice bounds no copy fixes, refused" (refused (measure ++ total ++ "fn f<..T: Measure>(n: Int, args: &..T) -> Int { return total(slice(args, n, size(args))); }; return 0;") "slice(args, a, b) needs bounds fixed in each copy")
                , testCase "a negative slice bound, refused" (refused (measure ++ total ++ "fn f<..T: Measure>(args: &..T) -> Int { return total(slice(args, 0 - 1, 1)); }; return 0;") "slice(args, a, b) needs bounds of 0 or more")
                , testCase "too few arguments before the pack, refused" (refused (measure ++ "fn g<..U: Measure>(k: Int, j: Int, rest: &..U) -> Int { return k; }; fn f<..T: Measure>(args: &..T) -> Int { return g(1, args); }; return 0;") "g takes 2 arguments before its pack, and args comes after 1: a forwarded pack fills only the pack")
                , testCase "clone of the pack, refused" (refused "fn f<..T>(args: &..T) -> Int { x = clone(args); return 0; }; return 0;" "args is given to clone, which has no pack")
                , testCase "to a function value, refused" (refused "fn f<..T>(k: fn(Int) -> Int, args: &..T) -> Int { return k(args); }; return 0;" "args is given to k, which has no pack")
                , testCase "forwarding in a define, refused" (refused "fn cnt<..U>(rest: &..U) -> Int { return size(rest); }; fn f<..T>(args: &..T) -> Int { define d = cnt(args); return 0; }; return 0;" "forwarding args in a contract or a validation statement is not supported yet")
                , testCase "and a slice in one" (refused "fn cnt<..U>(rest: &..U) -> Int { return size(rest); }; fn f<..T>(args: &..T) -> Int { define d = cnt(slice(args, 0, size(args))); return 0; }; return 0;" "forwarding args in a contract or a validation statement is not supported yet")
                , testCase "forwarding in a contract, refused" (refused "fn g<..U>(rest: &..U) -> Int { return 0; }; fn f<..T>(args: &..T) -> Int [{ affirm g(args) >= 0; }] [{ }] { return 0; }; return 0;" "forwarding args in a contract or a validation statement is not supported yet")
                , testCase "after another argument too" (refused "fn g<..U>(k: Int, rest: &..U) -> Int { return 0; }; fn f<..T>(args: &..T) -> Int [{ affirm g(0, args) >= 0; }] [{ }] { return 0; }; return 0;" "forwarding args in a contract or a validation statement is not supported yet")
                , testCase "to a variadic function of another package" (phase2Runs forwardingPackage 12)
                , testCase "by a variadic function of another package to its private helper" (phase2Runs forwardingHelperPackage 13)
                ]
            , TestList
                "methods"
                [ testCase "a method with self and a pack" (runs (measure ++ "struct S { k: Int }; impl S { fn add<..T: Measure>(self: &Self, args: &..T) -> Int { t = self.k; for a in args { t = t + a.measure(); }; return t; }; }; s = S { k: 1 }; return s.add(2, true) * 10 + S::add(s, 3);") (VInt 44))
                , testCase "in an impl with bounds" (runs (measure ++ "struct W<T> { v: T }; impl<T: Measure> W<T> { fn plus<..U: Measure>(self: &Self, args: &..U) -> Int { t = self.v.measure(); for a in args { t = t + a.measure(); }; return t; }; }; w = W<Int> { v: 5 }; return w.plus(1, true);") (VInt 7))
                ]
            , TestList
                "packages"
                [ testCase "a variadic function of another package, with a private helper and a caller impl of its bound" (phase2Runs variadicPackage 42)
                , testCase "and its bound is checked at the call" (phase2Rejects variadicPackageUnmet ["total needs T (argument 1", "Mark"])
                ]
            , TestParallel "native against eval" [TestCase name (sameAsMir name source) | (name, source) <- variadicPrograms]
            ]

-- The bounds and parameter types of the one function a source defines
parsedHeader :: String -> ([Bound] -> [Type] -> TestResult) -> TestResult
parsedHeader source check = case parseStatementBlock source of
    Right [BoundedDef bounds (Assign _ (Val (VFunct _ _ _ (NativeFunct (Signature ptys _ _ _ _ _) _ _) _)))] -> check bounds ptys
    other -> Just ("not one function with bounds: " ++ show other)

-- The pack loop a statement is in the body of a variadic function
packLoopOf :: String -> ((String, String, String, Bool) -> TestResult) -> TestResult
packLoopOf loop check = case parseStatementBlock ("fn f<..T>(args: &..T) -> Int { " ++ loop ++ "; return 0; };") of
    Right [s'] -> case [(i, a, p, takes) | PackLoop i a p _ _ takes _ <- bodyOf s'] of
        [found] -> check found
        other -> Just ("no pack loop: " ++ show other)
    other -> Just (show other)

bodyOf :: Statement -> [Statement]
bodyOf s' = case s' of
    BoundedDef _ inner -> bodyOf inner
    Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> body
    _ -> []

measure :: String
measure = "trait Measure { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Measure for Int { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { if self < 0 { return 0 - self; }; return self; }; }; impl Measure for Bool { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { if self { return 1; }; return 0; }; }; "

count :: String
count = "fn count<..T>(args: &..T) -> Int { n = 0; for a in args { n = n + 1; }; return n; }; "

eat :: String
eat = "fn eat<T>(x: T) -> Int { return 1; }; "

total :: String
total = "fn total<..U: Measure>(rest: &..U) -> Int { t = 0; for a in rest { t = t + a.measure(); }; return t; }; "

sumRec :: String
sumRec = "fn sum<..T: Measure>(args: &..T) -> Int { if size(args) = 0 { return 0; }; return get(args, 0).measure() + sum(slice(args, 1, size(args))); }; "

headRest :: String
headRest = "fn g<A, ..U>(x: A, rest: ..U) -> Int { n = eat(x); for a in rest { n = n + eat(a); }; return n; }; "

need :: String
need = "fn need<..U: Measure>(rest: &..U) -> Int [{ affirm size(rest) >= 1; }] [{ }] { return 1; }; "

forwardingPackage :: [(FilePath, String)]
forwardingPackage = phase2Files
    "import vendor::api { total, Mark }; fn f<..T: Mark>(args: &..T) -> Int { return total(args); }; return f(2, 3);"
    "trait Mark { fn mark(self: &Self) -> Int; }; impl Mark for Int { fn mark(self: &Self) -> Int { return self; }; }; fn total<..T: Mark>(args: &..T) -> Int { n = 7; for a in args { n = n + a.mark(); }; return n; };"
    []

forwardingHelperPackage :: [(FilePath, String)]
forwardingHelperPackage = phase2Files
    "import vendor::api { total }; return total(100, 4, 8);"
    "trait Mark { fn mark(self: &Self) -> Int; }; impl Mark for Int { fn mark(self: &Self) -> Int { return self; }; }; fn helper<..T: Mark>(args: &..T) -> Int { n = 0; for a in args { n = n + a.mark(); }; return n; }; fn total<..T: Mark>(args: &..T) -> Int { if size(args) = 0 { return 0; }; return helper(slice(args, 1, size(args))) + 1; };"
    []

variadicPackage :: [(FilePath, String)]
variadicPackage = phase2Files
    "import vendor::api { total, Mark }; struct Item { }; impl Mark for Item { fn mark(self: &Self) -> Int { return 30; }; }; return total(Item { }, 2, 3);"
    "trait Mark { fn mark(self: &Self) -> Int; }; impl Mark for Int { fn mark(self: &Self) -> Int { return self; }; }; fn base() -> Int { return 7; }; fn total<..T: Mark>(args: &..T) -> Int { n = base(); for a in args { n = n + a.mark(); }; return n; };"
    []

variadicPackageUnmet :: [(FilePath, String)]
variadicPackageUnmet = phase2Files
    "import vendor::api { total }; return total(true);"
    "trait Mark { fn mark(self: &Self) -> Int; }; impl Mark for Int { fn mark(self: &Self) -> Int { return self; }; }; fn total<..T: Mark>(args: &..T) -> Int { n = 0; for a in args { n = n + a.mark(); }; return n; };"
    []

-- Run natively and by the MIR's executor, which have to agree
variadicPrograms :: [(String, String)]
variadicPrograms =
    [ ("a lent pack read in a loop", measure ++ "fn total<..T: Measure>(args: &..T) -> Int { t = 0; for a in args { t = t + a.measure(); }; return t; }; return total(3, true, 0 - 4);")
    , ("a lent pack of heap values the caller keeps", count ++ "l = push(push([], 1), 2); s = \"text\"; n = count(l, s, l); return n * 100 + size(l) + size(s.bytes);")
    , ("a heap value moved out of a pack taken by value", "fn keep<T>(x: T) -> List<T> { return push([], x); }; fn second<..T>(args: ..T) -> Int [{ affirm size(args) >= 2; }] [{ }] { k = keep(get(args, 1)); return size(k) + size(args); }; return second(push([], 1), push(push([], 2), 3), true);")
    , ("for a in args takes heap values", "fn eat<T>(x: T) -> Int { return 1; }; fn all<..T>(args: ..T) -> Int { n = 0; for a in args { n = n + eat(a); }; return n; }; return all(push([], 1), \"two\", push([], push([], 3)));")
    , ("elements read at computed indices", measure ++ "fn pairs<..T: Measure>(args: &..T) -> Int { s = 0; for i in 0..size(args) - 1 { s = s + get(args, i + 1).measure() * 10 + get(args, i).measure(); }; if size(args) > 0 { s = s + get(args, size(args) - 1).measure() * 1000; }; return s; }; return pairs(1, true, 7);")
    , ("a function defined in a loop over the pack in a branch the copy drops", measure ++ "fn f<..T: Measure>(args: &..T) -> Int { t = 0; if size(args) > 0 { for a in args { fn twice(y: Int) -> Int { return y * 2; }; t = t + twice(a.measure()); }; }; return t; }; return f() + f(3);")
    , ("a function defined in a branch the copy drops", measure ++ "fn f<..T: Measure>(args: &..T) -> Int { t = 0; if size(args) > 0 { fn twice(y: Int) -> Int { return y * 2; }; t = twice(get(args, 0).measure()); }; return t; }; return f() + f(2);")
    , ("functions defined in loops over the pack", measure ++ "fn f<..T: Measure>(args: &..T) -> Int { fn inner(x: Int) -> Int { return x + 1; }; t = 0; for a in args { fn twice(y: Int) -> Int { return y * 2; }; t = t + twice(a.measure()) + inner(0); }; return inner(size(args)) * 100 + t; }; return f(3, true) * 1000 + f();")
    , ("a computed index from an outer loop read in an inner one", measure ++ "fn f<..T: Measure>(args: &..T) -> Int { t = 0; for i in 1..size(args) + 1 { for b in args { affirm Measure::measure(get(args, size(args) - i)) >= 0; t = t + 0 * b.measure(); }; }; return size(args) + t; }; return f(5, true);")
    , ("validation statements and defines at loop indices", measure ++ "fn f<..T: Measure>(args: &..T) -> Int { for i, a in args { affirm Measure::measure(get(args, i)) = Measure::measure(a); define m = Measure::measure(get(args, i)); for b in args { affirm m >= 0; }; }; return size(args); }; return f(5, true);")
    , ("a define of an element at a computed index", measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define k = get(args, size(args) - 1); affirm Measure::measure(k) >= 0; return get(args, size(args) - 1).measure(); }; return f(4) + f(4, true);")
    , ("defines of elements on a path the call rules out, in loop invariants and before a body's own", measure ++ "fn f<..T: Measure>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { define k = get(args, 0); affirm Measure::measure(k) >= 0; define n = size(args); for a in args { affirm n >= 0; define n = 5; define m = Measure::measure(a); j = 0; while j < 2 [{ affirm j >= 0; affirm j <= 2; affirm m >= 0; }] shrinks 2 - j { j = j + 1; }; }; return 4; }; n = 0; if n > 0 { return f(); }; return f(4, true);")
    , ("lent recursion through a slice", measure ++ sumRec ++ "return sum(1, true, 3, 0 - 4) * 10 + sum();")
    , ("by-value recursion moving heap values", eat ++ "fn cnt<..T>(args: ..T) -> Int { if size(args) = 0 { return 0; }; return eat(get(args, 0)) + cnt(slice(args, 1, size(args))); }; return cnt(push([], 1), \"two\", push([], push([], 3)));")
    , ("a pack of heap values taken by value lent to a lent pack and then forwarded by value", count ++ eat ++ "fn h<..U>(rest: ..U) -> Int { n = 0; for a in rest { n = n + eat(a); }; return n; }; fn f<..T>(args: ..T) -> Int { c = count(args); return c * 10 + h(slice(args, 1, size(args))); }; return f(push([], 1), \"two\", push([], push([], 3)));")
    , ("the head moved and the rest forwarded by value through a helper", eat ++ "fn walk<..T>(args: ..T) -> Int { if size(args) = 0 { return 0; }; return step(get(args, 0), slice(args, 1, size(args))); }; fn step<A, ..U>(x: A, rest: ..U) -> Int { return eat(x) + walk(rest); }; return walk(push([], 1), \"two\", push([], push([], 3)));")
    , ("the head borrowed while the rest is forwarded by value", eat ++ "fn sz<T>(r: &T) -> Int { return 10; }; fn h<..U>(rest: ..U) -> Int { n = 0; for a in rest { n = n + eat(a); }; return n; }; fn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] { r = &get(args, 0); n = h(slice(args, 1, size(args))); return n + sz(r); }; return f(push([], 1), \"two\", push([], push([], 3)));")
    , ("nested loops and indices", measure ++ "fn grid<..T: Measure>(args: &..T) -> Int { t = 0; for i, a in args { for j in 0..size(args) { if i < j { t = t + a.measure() * get(args, j).measure(); }; }; }; return t; }; return grid(1, 2, 3);")
    ]
