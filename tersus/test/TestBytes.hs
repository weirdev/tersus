module TestBytes (testBytes) where

import Cli (Command (..), runSource)
import TestHarness
import Utils

-- The type Byte: an Int from 0 to 255 that is a type of its own. toByte(x) asks for a proof of the range, toInt(b) is the Int, and the validator
-- knows the range of every Byte, wherever it came from.
testBytes :: Test
testBytes =
    let runs body expected = testAssertEq (runSource Interpret body) (Ok expected)
        rejected body expected = testAssertErrorContains expected (runSource Check body)
        valid body = testAssertEq (runSource Check body) (Ok "OK")
     in TestList
            "testBytes"
            [ TestList
                "conversions"
                [ testCase "an Int is a Byte, and a Byte an Int" (runs "b = toByte(200); return toInt(b) + 1;" "201")
                , testCase "the ends of the range" (runs "return toInt(toByte(0)) * 1000 + toInt(toByte(255));" "255")
                , testCase "an Int above the range is refused" (rejected "b = toByte(256); return 0;" "Funct input validation failed")
                , testCase "and one below it" (rejected "b = toByte(0 - 1); return 0;" "Funct input validation failed")
                , testCase "an Int that is not known to be in the range is refused" (rejected "x = readByte(); b = toByte(x); return 0;" "Funct input validation failed")
                , testCase "and is accepted where it has been tested" (valid "x = readByte(); if x >= 0 { b = toByte(x); return toInt(b); }; return 0 - 1;")
                , testCase "a parameter that is tested" (valid "fn f(x: Int) -> Byte [{ }] [{ }] { if x < 0 { return toByte(0); }; if x > 255 { return toByte(255); }; return toByte(x); }; return toInt(f(300));")
                , testCase "a clamped value" (runs "fn f(x: Int) -> Byte [{ }] [{ }] { if x < 0 { return toByte(0); }; if x > 255 { return toByte(255); }; return toByte(x); }; return toInt(f(300)) * 1000 + toInt(f(0 - 4)) * 10 + toInt(f(7));" "255007")
                ]
            , TestList
                "types"
                [ testCase "an Int is not a Byte" (rejected "fn f(b: Byte) -> Int [{ }] [{ }] { return toInt(b); }; n = 5; return f(n);" "expected Byte, got Int")
                , testCase "nor a Byte an Int" (rejected "b = toByte(5); c = b + 1; return 0;" "expected Int, got Byte")
                , testCase "or compared with an order" (rejected "b = toByte(5); if b < 7 { return 1; }; return 0;" "expected Int, got Byte")
                , testCase "Bytes are equal when they are the same number" (runs "b = toByte(9); c = toByte(4 + 5); if b = c { return 1; }; return 0;" "1")
                , testCase "and are not when they differ" (runs "if toByte(9) = toByte(8) { return 1; }; return 0;" "0")
                , testCase "a Byte in a struct" (runs "struct P { b: Byte }; p = P { b: toByte(9) }; return toInt(p.b);" "9")
                , testCase "a field that is an Int is not a Byte" (rejected "struct P { b: Byte }; n = 9; p = P { b: n }; return 0;" "expected Byte, got Int")
                , testCase "a list of Bytes" (runs "bs = push(push([], toByte(1)), toByte(2)); return toInt(get(bs, 1)) * 10 + size(bs);" "22")
                , testCase "an Int does not go into a list of them" (rejected "bs = push(push([], toByte(1)), 2); return 0;" "Byte")
                , testCase "a list of Bytes is written as the numbers" (runs "return push(push([], toByte(1)), toByte(2));" "[1, 2]")
                , testCase "a function over Bytes" (runs "fn next(b: Byte) -> Byte [{ affirm toInt(b) < 255; }] [{ affirm toInt(return) = toInt(b) + 1; }] { return toByte(toInt(b) + 1); }; return toInt(next(toByte(41)));" "42")
                , testCase "and the caller has to meet its contract" (rejected "fn next(b: Byte) -> Byte [{ affirm toInt(b) < 255; }] [{ }] { return toByte(toInt(b) + 1); }; return toInt(next(toByte(255)));" "Funct input validation failed")
                , testCase "Byte is a type that can be written" (valid "fn f(a: List<Byte>, b: Byte) -> Byte [{ }] [{ }] { return b; }; return 0;")
                ]
            , TestList
                "what the validator knows"
                [ testCase "a Byte is from 0 to 255 without a contract" (valid "fn f(b: Byte) -> Int [{ }] [{ affirm return >= 0; affirm return <= 255; }] { return toInt(b); }; return f(toByte(7));")
                , testCase "also for a field" (valid "struct P { b: Byte }; fn f(p: P) -> Int [{ }] [{ affirm return < 256; }] { return toInt(p.b); }; return f(P { b: toByte(3) });")
                , testCase "an element of a list" (valid "bs = push([], toByte(7)); c = get(bs, 0); affirm toInt(c) >= 0; affirm toInt(c) < 256; return 0;")
                , testCase "the sum of three is at most 765" (valid "fn f(a: Byte, b: Byte, c: Byte) -> Int [{ }] [{ affirm return <= 765; affirm return >= 0; }] { return toInt(a) + toInt(b) + toInt(c); }; return f(toByte(1), toByte(2), toByte(3));")
                , testCase "but not more than that" (rejected "fn f(a: Byte, b: Byte) -> Int [{ }] [{ affirm return < 510; }] { return toInt(a) + toInt(b); }; return f(toByte(1), toByte(2));" "Could not prove")
                , testCase "the value of a conversion is known" (valid "b = toByte(7); affirm toInt(b) = 7; return 0;")
                , testCase "a Byte of a loop" (valid "bs = push(push([], toByte(1)), toByte(2)); i = 0; total = 0; while i < size(bs) [{ affirm i >= 0; affirm i <= size(bs); affirm total >= 0; affirm total <= 255 * i; }] shrinks size(bs) - i { total = total + toInt(get(bs, i)); i = i + 1; }; return total;")
                ]
            ]
