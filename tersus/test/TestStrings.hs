module TestStrings (testStrings) where

import Data.List (intercalate)

import Cli (Command (..), runSource)
import TestHarness
import Utils

-- Strings: a literal is a value of the struct `String` of lib/string.tersus, made of the UTF-8 bytes of its text
testStrings :: Test
testStrings =
    let runs body expected = testAssertEq (runSource Interpret body) (Ok expected)
        rejected body expected = testAssertErrorContains expected (runSource Check body)
        valid body = testAssertEq (runSource Check body) (Ok "OK")
        parseError body = testAssertErrorContains "Parse error" (runSource Check body)
        bytes xs = "String { bytes: [" ++ intercalate ", " (map show (xs :: [Int])) ++ "] }"
        true = "true"
        false = "false"
     in TestList
            "testStrings"
            [ TestList
                "literals"
                [ testCase "a string is the bytes of its text" (runs "return \"hi\";" (bytes [104, 105]))
                , testCase "the empty string" (runs "return \"\";" (bytes []))
                , testCase "escapes" (runs "return \"a\\n\\t\\r\\0\\\"\\\\\";" (bytes [97, 10, 9, 13, 0, 34, 92]))
                , testCase "a character that is not ASCII is its UTF-8 bytes" (runs "return \"\\u{e9}\\u{20ac}\\u{1f600}\";" (bytes [195, 169, 226, 130, 172, 240, 159, 152, 128]))
                , testCase "also as it is written" (runs "return \"\233\";" (bytes [195, 169]))
                , testCase "the size is the number of bytes" (runs "return size(\"caf\\u{e9}\");" "5")
                , testCase "a quote in a comment is not a string" (runs "x = 1; // \"\nreturn x;" "1")
                , testCase "a `//` in a string is text" (runs "return size(\"a//b\");" "4")
                , testCase "the program's line numbers are its own" (parseError "x = 1;\ny = \"a\n\";")
                , testCase "an unfinished string" (parseError "x = \"ab;")
                , testCase "an escape that does not exist" (parseError "x = \"\\q\";")
                , testCase "a character that does not exist" (parseError "x = \"\\u{d800}\";")
                ]
            , TestList
                "the functions of a string"
                [ testCase "size and get" (runs "s = \"abc\"; return size(s) * 1000 + get(s, 1);" "3098")
                , testCase "push and set" (runs "s = \"ab\".push(99); return set(s, 0, 65);" (bytes [65, 98, 99]))
                , testCase "concat" (runs "return \"ab\".concat(\"cd\");" (bytes [97, 98, 99, 100]))
                , testCase "concat borrows its second string" (runs "t = \"x\"; s = \"a\".concat(t).concat(t); return size(s) + size(t);" "4")
                , testCase "strings are compared by their bytes" (runs "return \"ab\" = \"a\".push(98);" true)
                , testCase "and are not equal when the bytes differ" (runs "return \"ab\" = \"ac\";" false)
                , testCase "a function on a Sequence<Int> takes one" (runs "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { sum = 0; i = 0; while i < size(s) [{ affirm i >= 0; affirm i <= size(s); }] shrinks size(s) - i { sum = sum + get(s, i); i = i + 1; }; return sum; }; return total(\"ab\");" "195")
                , testCase "a string in a struct and a list" (runs "struct Named { name: String, n: Int }; xs = push(push([], Named { name: \"a\", n: 1 }), Named { name: \"bc\", n: 2 }); return size(get(xs, 1).name) + get(xs, 0).n;" "3")
                ]
            , TestList
                "validation"
                [ testCase "a size is known from the literal" (valid "s = \"abc\"; affirm size(s) = 3; return 0;")
                , testCase "and of a concat and a push" (valid "s = \"ab\".concat(\"c\").push(1); affirm size(s) = 4; affirm get(s, 3) = 1; return 0;")
                , testCase "an index out of range is refused" (rejected "s = \"ab\"; return get(s, 2);" "Could not prove: i < size(self.bytes)")
                , testCase "a wrong size is refused" (rejected "s = \"ab\"; affirm size(s) = 3; return 0;" "Could not prove: <String as Sequence>::size(s) = 3")
                , testCase "the size of a concat is the sum" (rejected "s = \"ab\".concat(\"cd\"); affirm size(s) = 3; return 0;" "Could not prove: <String as Sequence>::size(s) = 3")
                ]
            , TestList
                "output"
                [ testCase "a byte is written, then the value" (runs "writeByte(104); writeByte(105); return 1;" "hi1")
                , testCase "and is its own value" (runs "x = writeByte(65); return x;" "A65")
                , testCase "only the low eight bits are written" (runs "writeByte(321); writeByte(0 - 191); return 0;" "AA0")
                , testCase "a string is printed with its bytes" (runs "\"ab\\n\".print(); return 7;" "ab\n7")
                , testCase "print is the number of bytes" (runs "n = \"caf\\u{e9}\".print(); return n;" ("caf\233" ++ "5"))
                , testCase "bytes that are UTF-8 are the character" (runs "writeByte(226); writeByte(130); writeByte(172); return 0;" ("\8364" ++ "0"))
                , testCase "and bytes that are not are U+FFFD" (runs "writeByte(255); writeByte(65); return 0;" "\65533A0")
                , testCase "the output is in the order of the calls" (runs "\"a\".print(); writeByte(98); \"c\".print(); return 0;" "abc0")
                , testCase "a call in a loop" (runs "i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { writeByte(48 + i); i = i + 1; }; return i;" "0123")
                , testCase "a call is a statement of its own" (runs "fn id(x: Int) -> Int [{ }] [{ affirm return = x; }] { return x; }; id(3); y = 4; id(y); return y;" "4")
                , testCase "a method call too" (runs "s = \"a\"; s.concat(\"b\"); return 1;" "1")
                , testCase "the input contract of the call still has to be met" (rejected "fn pos(x: Int) -> Int [{ affirm x > 0; }] [{ }] { return x; }; pos(0); return 1;" "Could not prove: x > 0")
                , testCase "an expression that is not a call is not a statement" (parseError "x = 1; x + 2; return x;")
                , testCase "nor is a name" (parseError "x = 1; x; return x;")
                , testCase "the call is validated: print gives the size" (valid "n = \"ab\".print(); affirm n = 2; return n;")
                , testCase "and a wrong claim is refused" (rejected "n = \"ab\".print(); affirm n = 3; return n;" "Could not prove: n = 3")
                , testCase "the bytes of a UTF-8 text decode" (testAssertEq (decodeUtf8 (map toEnum [104, 195, 169, 226, 130, 172, 240, 159, 152, 128])) "h\233\8364\128512")
                , testCase "a byte that starts a character that is cut short is U+FFFD" (testAssertEq (decodeUtf8 (map toEnum [226, 130])) "\65533\65533")
                , testCase "an overlong encoding is U+FFFD" (testAssertEq (decodeUtf8 (map toEnum [192, 128])) "\65533\65533")
                ]
            , TestList
                "the library"
                [ testCase "a program without a string has no String" (rejected "return \"a\"; fn f(x: Int) -> Int [{ }] [{ }] { return y; };" "y")
                , testCase "a String of its own is used, and a literal is then refused" (parseError "struct String { x: Int }; s = \"a\";")
                , testCase "but the program still runs without one" (runs "struct String { x: Int }; return String { x: 3 }.x;" "3")
                , testCase "a declaration in the text of a literal is not one" (runs "return size(\"struct String\");" "13")
                , testCase "nor is a declaration in the text of a literal with an escape" (runs "x = \"\\\" trait Sequence\"; return size(x);" "16")
                , testCase "nor is one in a comment" (runs "// struct String\nreturn size(\"a\");" "1")
                , testCase "mentioning String is enough" (runs "fn f(s: String) -> Int [{ }] [{ }] { return size(s); }; return f(\"abc\");" "3")
                , testCase "a program with its own Sequence has no library" (parseError "trait Sequence<E> { fn size(self: &Self) -> Int [{ }] [{ }]; }; s = \"a\";")
                , testCase "and without a string nothing changes" (runs "return [1, 2];" "[1, 2]")
                ]
            ]
