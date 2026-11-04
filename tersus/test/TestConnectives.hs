module TestConnectives (testConnectives) where

import Data.List (isInfixOf)

import Cli (Command (..), runSource)
import TestHarness
import Utils

-- `&&`, `||` and `!` in the conditions and the values of a program. They are lowered to the jumps they stand for, so `a && b` does not evaluate b
-- when a is false, and the validator knows a when it checks b. A proof has `&&` (`affirm a && b;` is two statements) and not `||` or `!`.
testConnectives :: Test
testConnectives =
    let runs body expected = testAssertEq (runSource Interpret body) (Ok expected)
        valid body = testAssertEq (runSource Check body) (Ok "OK")
        rejected body expected = case runSource Check body of
            Ok _ -> Just "Expected the program to be refused"
            Error message -> if expected `isInfixOf` message
                then Nothing
                else Just ("Expected failure containing: " ++ show expected ++ "\nGot: " ++ message)
     in TestList
            "testConnectives"
            [ TestList
                "values"
                [ testCase name (runs body expected)
                | (name, body, expected) <-
                    [ ("and", "return true && true;", "true")
                    , ("and with false", "return true && false;", "false")
                    , ("or", "return false || true;", "true")
                    , ("or with neither", "return false || false;", "false")
                    , ("not", "return !true;", "false")
                    , ("not of a relation", "x = 3; return !(x > 5);", "true")
                    , ("not binds tighter than and", "return !false && false;", "false")
                    , ("and binds tighter than or", "return true || false && false;", "true")
                    , ("relations bind tighter than and", "a = 1; b = 2; return a < b && b < 3;", "true")
                    , ("!= is not a not", "a = 1; return a != 2 && !(a = 2);", "true")
                    , ("parentheses", "return (true || false) && false;", "false")
                    , ("a value kept in a variable", "ok = 1 < 2 && 2 < 3; return ok;", "true")
                    , ("the right side is not evaluated when the left decides", "a = 0; return a != 0 && 10 / a > 1;", "false")
                    , ("nor for an or", "a = 0; return a = 0 || 10 / a > 1;", "true")
                    , ("but is when it does not", "a = 5; return a != 0 && 10 / a > 1;", "true")
                    , ("an argument", "fn id(b: Bool) -> Bool [{ }] [{ }] { return b; }; return id(1 < 2 && 3 < 2);", "false")
                    , ("a nested group as a value", "a = 1; b = 2; return (a = 1 && (b = 3 || b = 2)) && !(a = b);", "true")
                    , ("in a call that the right side makes", "fn big(n: Int) -> Bool [{ }] [{ }] { return n > 5; }; return 1 < 2 && big(9);", "true")
                    ]
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
                , testCase "without it the index is not known to be in range" (rejected "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { if get(l, i) = 0 && i < size(l) { return true; }; return false; };" "Could not prove: index < size(list) (in f)")
                , testCase "for an or, the left side is false when the right is checked" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { if i >= size(l) || get(l, i) = 0 { return true; }; return false; };")
                , testCase "chained guards in a returned value" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ }] [{ }] { return i >= 0 && i < size(l) && get(l, i) = 0; };")
                , testCase "chained guards in the value of a variable" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ }] [{ }] { ok = i >= 0 && i < size(l) && get(l, i) = 0; return ok; };")
                , testCase "chained guards in an argument" (valid "fn g(b: Bool) -> Bool [{ }] [{ }] { return b; }; fn f(l: &List<Int>, i: Int) -> Bool [{ }] [{ }] { return g(i >= 0 && i < size(l) && get(l, i) = 0); };")
                , testCase "guards of an or in a value" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { return i >= size(l) || get(l, i) = 0; };")
                , testCase "a group in a value" (valid "fn f(l: &List<Int>, i: Int) -> Bool [{ affirm i >= 0; }] [{ }] { return i < size(l) && (get(l, i) = 0 || get(l, i) = 1); };")
                , testCase "and in the value of a variable" (valid "fn f(a: Int, b: Int) -> Bool [{ }] [{ }] { ok = a > 0 && b > 0; return ok; };")
                , testCase "a loop guarded by its first test" (valid "fn f(l: &List<Int>) -> Int [{ }] [{ affirm return >= 0; affirm return <= size(l); }] { i = 0; while i < size(l) && get(l, i) != 0 [{ affirm i >= 0; affirm i <= size(l); }] shrinks size(l) - i { i = i + 1; }; return i; };")
                , testCase "the facts of both tests hold in the body" (valid "fn f(a: Int, b: Int) -> Int [{ }] [{ }] { i = 0; while i < a && i < b shrinks a - i { affirm i < a; affirm i < b; i = i + 1; }; return i; };")
                , testCase "the variant has to shrink with two tests too" (rejected "fn f(a: Int, b: Int) -> Int [{ }] [{ }] { i = 0; while i < a && i < b shrinks a - i { b = b; }; return i; };" "Could not prove: an obligation could not be proved by the Tersus validator (in f, block 1, step -1)")
                , testCase "an or knows only what both of its tests give" (rejected "n = 3; m = 2; while n > 0 || m > 0 [{ affirm n >= 0; affirm m >= 0; }] shrinks n + m { if n > 0 { n = n - 1; } else { m = m - 1; }; }; return n + m;" "Could not prove: an obligation could not be proved by the Tersus validator (in main, block 1, step 2)")
                , testCase "affirm with and is two statements" (valid "fn f(a: Int, b: Int) -> Int [{ affirm a > 0 && b > 0; }] [{ affirm return > 1; }] { affirm a >= 1 && b >= 1; return a + b; };")
                , testCase "and a contract with and is met by the caller" (rejected "fn f(a: Int, b: Int) -> Int [{ affirm a > 0 && b > 0; }] [{ }] { return a; }; x = f(1, 0);" "Could not prove: b > 0 (in main)")
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
