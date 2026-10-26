module TestConnectives (testConnectives) where

import Cli (Command (..), runSource)
import TestHarness
import Utils

-- `&&`, `||` and `!` in the conditions and the values of a program. They are lowered to the jumps they stand for, so `a && b` does not evaluate b
-- when a is false, and the validator knows a when it checks b. A proof has `&&` (`affirm a && b;` is two statements) and not `||` or `!`.
testConnectives :: Test
testConnectives =
    let runs body expected = testAssertEq (runSource Interpret body) (Ok expected)
        valid body = testAssertEq (runSource Check body) (Ok "OK")
        rejected body expected = testAssertErrorContains expected (runSource Check body)
     in TestList
            "testConnectives"
            [ TestList
                "values"
                [ testCase "and" (runs "return true && true;" "true")
                , testCase "and with false" (runs "return true && false;" "false")
                , testCase "or" (runs "return false || true;" "true")
                , testCase "or with neither" (runs "return false || false;" "false")
                , testCase "not" (runs "return !true;" "false")
                , testCase "not of a relation" (runs "x = 3; return !(x > 5);" "true")
                , testCase "not binds tighter than and" (runs "return !false && false;" "false")
                , testCase "and binds tighter than or" (runs "return true || false && false;" "true")
                , testCase "relations bind tighter than and" (runs "a = 1; b = 2; return a < b && b < 3;" "true")
                , testCase "!= is not a not" (runs "a = 1; return a != 2 && !(a = 2);" "true")
                , testCase "parentheses" (runs "return (true || false) && false;" "false")
                , testCase "a value kept in a variable" (runs "ok = 1 < 2 && 2 < 3; return ok;" "true")
                , testCase "the right side is not evaluated when the left decides" (runs "a = 0; return a != 0 && 10 / a > 1;" "false")
                , testCase "nor for an or" (runs "a = 0; return a = 0 || 10 / a > 1;" "true")
                , testCase "but is when it does not" (runs "a = 5; return a != 0 && 10 / a > 1;" "true")
                , testCase "an argument" (runs "fn id(b: Bool) -> Bool [{ }] [{ }] { return b; }; return id(1 < 2 && 3 < 2);" "false")
                , testCase "a nested group as a value" (runs "a = 1; b = 2; return (a = 1 && (b = 3 || b = 2)) && !(a = b);" "true")
                , testCase "in a call that the right side makes" (runs "fn big(n: Int) -> Bool [{ }] [{ }] { return n > 5; }; return 1 < 2 && big(9);" "true")
                ]
            , TestList
                "conditions"
                [ testCase "an if" (runs "x = 4; if x > 1 && x < 9 { return 1; }; return 0;" "1")
                , testCase "an if with an else" (runs "x = 4; if x > 1 && x > 9 { return 1; } else { return 2; };" "2")
                , testCase "an or in an if" (runs "x = 4; if x > 9 || x = 4 { return 1; }; return 0;" "1")
                , testCase "not in an if" (runs "x = 4; if !(x = 4) { return 1; }; return 0;" "0")
                , testCase "mixed" (runs "x = 4; y = 7; if (x > 9 || y = 7) && !(x = y) { return 1; }; return 0;" "1")
                , testCase "a while with and" (runs "i = 0; s = 0; while i < 10 && s < 20 shrinks 10 - i { s = s + i * 2; i = i + 1; }; return s;" "20")
                , testCase "a while with or" (runs "i = 0; while i < 3 || i < 5 [{ affirm i >= 0; affirm i <= 5; }] shrinks 5 - i { i = i + 1; }; return i;" "5")
                , testCase "a call in the second part" (runs "fn small(n: Int) -> Bool [{ }] [{ }] { return n < 3; }; i = 0; while i < 10 && small(i) shrinks 10 - i { i = i + 1; }; return i;" "3")
                ]
            , TestList
                "validation"
                [ testCase "the left side is known when the right is checked" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { if i < size(l) && get(l, i) = 0 { return true; }; return false; };")
                , testCase "without it the index is not known to be in range" (rejected "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { if get(l, i) = 0 && i < size(l) { return true; }; return false; };" "Funct input validation failed")
                , testCase "for an or, the left side is false when the right is checked" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { if i >= size(l) || get(l, i) = 0 { return true; }; return false; };")
                , testCase "chained guards in a returned value" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ }] [{ }] { return i >= 0 && i < size(l) && get(l, i) = 0; };")
                , testCase "chained guards in the value of a variable" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ }] [{ }] { ok = i >= 0 && i < size(l) && get(l, i) = 0; return ok; };")
                , testCase "chained guards in an argument" (valid "fn g(b: Bool) -> Bool [{ }] [{ }] { return b; }; fn f(l: &List<Int>, i: Int) -> Bool [{ }] [{ }] { return g(i >= 0 && i < size(l) && get(l, i) = 0); };")
                , testCase "guards of an or in a value" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { return i >= size(l) || get(l, i) = 0; };")
                , testCase "a group in a value" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { return i < size(l) && (get(l, i) = 0 || get(l, i) = 1); };")
                , testCase "and in the value of a variable" (valid "fn f(a: Int, b: Int) -> Bool [{ }] [{ }] { ok = a > 0 && b > 0; return ok; };")
                , testCase "a loop guarded by its first test" (valid "fn f(l: &List<Int>) -> Int [{ }] [{ affirm return >= 0; affirm return <= size(l); }] { i = 0; while i < size(l) && get(l, i) != 0 [{ affirm i >= 0; affirm i <= size(l); }] shrinks size(l) - i { i = i + 1; }; return i; };")
                , testCase "the facts of both tests hold in the body" (valid "fn f(a: Int, b: Int) -> Int [{ }] [{ }] { i = 0; while i < a && i < b shrinks a - i { affirm i < a; affirm i < b; i = i + 1; }; return i; };")
                , testCase "the variant has to shrink with two tests too" (rejected "fn f(a: Int, b: Int) -> Int [{ }] [{ }] { i = 0; while i < a && i < b shrinks a - i { b = b; }; return i; };" "Loop variant does not shrink")
                , testCase "an or knows only what both of its tests give" (rejected "n = 3; m = 2; while n > 0 || m > 0 [{ affirm n >= 0; affirm m >= 0; }] shrinks n + m { if n > 0 { n = n - 1; } else { m = m - 1; }; }; return n + m;" "Loop invariant is not preserved")
                , testCase "affirm with and is two statements" (valid "fn f(a: Int, b: Int) -> Int [{ affirm a > 0 && b > 0; }] [{ affirm return > 1; }] { affirm a >= 1 && b >= 1; return a + b; };")
                , testCase "and a contract with and is met by the caller" (rejected "fn f(a: Int, b: Int) -> Int [{ affirm a > 0 && b > 0; }] [{ }] { return a; }; x = f(1, 0);" "Funct input validation failed")
                , testCase "a conjunct that does not hold" (rejected "fn f(a: Int) -> Int [{ affirm a > 0; }] [{ }] { affirm a > 0 && a > 5; return a; };" "Could not prove")
                ]
            , TestList
                "refused"
                [ testCase "an Int is not a condition" (rejected "x = 1; if x && true { return 1; }; return 0;" "Bool")
                , testCase "nor is it a value of a connective" (rejected "x = 1; y = x || false; return 0;" "Bool")
                , testCase "not of an Int" (rejected "x = 1; y = !x; return 0;" "Bool")
                , testCase "a proof has no or" (rejected "x = 1; affirm x = 1 || x = 2; return 0;" "||")
                , testCase "nor not" (rejected "x = 1; affirm x = 1 && x = 1 || x = 2; return 0;" "||")
                ]
            ]
