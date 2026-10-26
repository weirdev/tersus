module TestStrings (testStrings) where

import Data.List (intercalate)

import Cli (Command (..), runSource, runSourceStreams, runSourceWith)
import TestHarness
import Utils

-- Strings: a literal is a value of the struct `String` of lib/string.tersus, made of the UTF-8 bytes of its text
testStrings :: Test
testStrings =
    let runs body expected = testAssertEq (runSource Interpret body) (Ok expected)
        rejected body expected = testAssertErrorContains expected (runSource Check body)
        valid body = testAssertEq (runSource Check body) (Ok "OK")
        reads input body expected = testAssertEq (runSourceWith input Interpret body) (Ok expected)
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
                [ testCase "size and get" (runs "s = \"abc\"; return size(s) * 1000 + toInt(get(s, 1));" "3098")
                , testCase "push and set" (runs "s = \"ab\".push(toByte(99)); return set(s, 0, toByte(65));" (bytes [65, 98, 99]))
                , testCase "concat" (runs "return \"ab\".concat(\"cd\");" (bytes [97, 98, 99, 100]))
                , testCase "concat borrows its second string" (runs "t = \"x\"; s = \"a\".concat(t).concat(t); return size(s) + size(t);" "4")
                , testCase "strings are compared by their bytes" (runs "return \"ab\" = \"a\".push(toByte(98));" true)
                , testCase "and are not equal when the bytes differ" (runs "return \"ab\" = \"ac\";" false)
                , testCase "a function on a Sequence<Byte> takes one" (runs "fn total<S: Sequence<Byte>>(s: &S) -> Int [{ }] [{ }] { sum = 0; i = 0; while i < size(s) [{ affirm i >= 0; affirm i <= size(s); }] shrinks size(s) - i { sum = sum + toInt(get(s, i)); i = i + 1; }; return sum; }; return total(\"ab\");" "195")
                , testCase "a string in a struct and a list" (runs "struct Named { name: String, n: Int }; xs = push(push([], Named { name: \"a\", n: 1 }), Named { name: \"bc\", n: 2 }); return size(get(xs, 1).name) + get(xs, 0).n;" "3")
                ]
            , TestList
                "validation"
                [ testCase "a size is known from the literal" (valid "s = \"abc\"; affirm size(s) = 3; return 0;")
                , testCase "and of a concat and a push" (valid "s = \"ab\".concat(\"c\").push(toByte(1)); affirm size(s) = 4; affirm toInt(get(s, 3)) = 1; return 0;")
                , testCase "an index out of range is refused" (rejected "s = \"ab\"; return get(s, 2);" "Could not prove: i < size(self.bytes)")
                , testCase "a wrong size is refused" (rejected "s = \"ab\"; affirm size(s) = 3; return 0;" "Could not prove: <String as Sequence>::size(s) = 3")
                , testCase "the size of a concat is the sum" (rejected "s = \"ab\".concat(\"cd\"); affirm size(s) = 3; return 0;" "Could not prove: <String as Sequence>::size(s) = 3")
                ]
            , TestList
                "facts about strings"
                [ testCase "a string written in a proof" (valid "c = \"ab\"; affirm c = \"ab\"; return 0;")
                , testCase "is not written with a list of Ints" (rejected "c = \"ab\"; affirm c = String { bytes: [97, 98] }; return 0;" "expected List<Byte>, got List<Int>")
                , testCase "and a different string is refused" (rejected "c = \"ab\"; affirm c = \"ac\"; return 0;" "Could not prove: c = String { bytes: [97, 99] }")
                , testCase "an escape in a proof" (valid "c = \"a\\n\"; affirm c = \"a\\n\"; return 0;")
                , testCase "a string in the input contract of a function" (valid "fn f(s: String) -> Int [{ affirm s = \"hi\"; }] [{ affirm return = 2; }] { return size(s); }; return f(\"hi\");")
                , testCase "that a caller has to meet" (rejected "fn f(s: String) -> Int [{ affirm s = \"hi\"; }] [{ }] { return size(s); }; return f(\"ho\");" "Could not prove: s = String { bytes: [104, 105] }")
                , testCase "concat keeps the bytes of the first string" (valid "c = \"ab\".concat(\"cd\"); affirm toInt(get(c, 0)) = 97; affirm toInt(get(c, 1)) = 98; return 0;")
                , testCase "and not any others" (rejected "c = \"ab\".concat(\"cd\"); affirm toInt(get(c, 0)) = 98; return 0;" "Could not prove")
                , testCase "the bytes of the second follow the first, at the index that is named" (valid "a = \"ab\"; b = \"cd\"; c = a.concat(b); affirm get(c.bytes, size(a.bytes) + 1) = get(b.bytes, 1); return 0;")
                , testCase "push keeps the bytes and adds one" (valid "c = \"ab\".push(toByte(99)); affirm toInt(get(c, 0)) = 97; affirm toInt(get(c, 2)) = 99; return 0;")
                ]
            , TestList
                "the bytes of a string are Bytes"
                [ testCase "get gives a Byte" (valid "s = \"ab\"; b = get(s, 0); affirm toInt(b) = 97; return 0;")
                , testCase "every byte is from 0 to 255, with nothing said of it" (valid "fn f(s: String, i: Int) -> Int [{ affirm i >= 0; affirm i < size(s); }] [{ affirm return >= 0; affirm return < 256; }] { return toInt(get(s, i)); }; return f(\"ab\", 1);")
                , testCase "also of what is read" (valid "fn f(i: Int) -> Int [{ affirm i >= 0; affirm i < 3; }] [{ affirm return >= 0; affirm return < 256; }] { s = String::read(3); if i < size(s) { return toInt(get(s, i)); }; return 0; }; return f(1);")
                , testCase "an Int is not pushed" (rejected "s = \"ab\".push(99); return 0;" "expected Byte, got Int")
                , testCase "nor set" (rejected "s = set(\"ab\", 0, 99); return 0;" "expected Byte, got Int")
                , testCase "a Byte is pushed" (runs "s = \"ab\".push(toByte(99)); return size(s);" "3")
                , testCase "a Byte that is made of an Int in range" (valid "n = 99; s = \"ab\".push(toByte(n)); return 0;")
                , testCase "and not of one that is not" (rejected "fn f(n: Int) -> Int [{ }] [{ }] { s = \"ab\".push(toByte(n)); return size(s); }; return f(7);" "Funct input validation failed")
                , testCase "a string is a Sequence<Byte>" (rejected "fn total<S: Sequence<Int>>(s: &S) -> Int [{ }] [{ }] { return size(s); }; return total(\"ab\");" "String implements Sequence<Byte>")
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
                "standard error"
                [ testCase "a byte is written to the standard error, not to the output" (testAssertEq (runSourceStreams "" Interpret "writeError(69); writeByte(79); return 1;") (Ok ("O1", "E")))
                , testCase "a string is printed to it" (testAssertEq (runSourceStreams "" Interpret "n = \"oops\\n\".printError(); return n;") (Ok ("5", "oops\n")))
                , testCase "and the two do not mix" (testAssertEq (runSourceStreams "" Interpret "\"out\".print(); \"err\".printError(); return 0;") (Ok ("out0", "err")))
                , testCase "UTF-8 is decoded" (testAssertEq (runSourceStreams "" Interpret "\"caf\\u{e9}\".printError(); return 0;") (Ok ("0", "caf\233")))
                , testCase "printError gives the number of bytes" (valid "n = \"ab\".printError(); affirm n = 2; return n;")
                , testCase "and a wrong claim is refused" (rejected "n = \"ab\".printError(); affirm n = 3; return n;" "Could not prove: n = 3")
                , testCase "a program that writes nothing to it has nothing there" (testAssertEq (runSourceStreams "" Interpret "return 1;") (Ok ("1", "")))
                ]
            , TestList
                "input"
                [ testCase "a byte" (reads "A" "return readByte();" "65")
                , testCase "-1 at the end of the input" (reads "" "return readByte();" "-1")
                , testCase "and after it" (reads "A" "a = readByte(); b = readByte(); c = readByte(); return b * 10 + c;" "-11")
                , testCase "the bytes in turn" (reads "\1\2\3" "a = readByte(); b = readByte(); return a * 10 + b;" "12")
                , testCase "a line" (reads "ab\ncd" "l = String::readLine(10); return size(l);" "2")
                , testCase "two lines, and what is written" (reads "ab\ncd" "a = String::readLine(10); b = String::readLine(10); b.print(); a.print(); return 0;" "cdab0")
                , testCase "a line longer than the limit is cut" (reads "abcdef\n" "a = String::readLine(3); b = String::readLine(10); b.print(); return size(a);" "def3")
                , testCase "everything" (reads "ab\ncd" "a = String::read(10); return size(a);" "5")
                , testCase "no more than the limit" (reads "abcdef" "a = String::read(4); b = String::read(10); return size(a) * 10 + size(b);" "42")
                , testCase "UTF-8 is read as bytes" (reads "caf\195\169" "a = String::read(10); return size(a);" "5")
                , testCase "an input that is a stream is read as it is needed" (testAssertEq (runSourceWith (take 3 (cycle "ab")) Interpret "a = readByte(); return a;") (Ok "97"))
                , testCase "a program has no input unless it is given some" (runs "return readByte();" "-1")
                , testCase "a byte that is read is from -1 to 255 and no more is known" (valid "c = readByte(); affirm c >= 0 - 1; affirm c < 256; return c;")
                , testCase "so a claim about it is refused" (rejected "c = readByte(); affirm c >= 0; return c;" "Could not prove: c >= 0")
                , testCase "two reads are not the same value" (rejected "a = readByte(); b = readByte(); affirm a = b; return a;" "Could not prove: a = b")
                , testCase "two reads of a function are not the same value either" (rejected "a = String::readLine(5); b = String::readLine(5); affirm a = b; return 0;" "Could not prove: a = b")
                , testCase "so two reads cannot make an index valid" (rejected "c = readByte(); d = readByte(); x = [0]; return get(x, c - d);" "Funct input validation failed")
                , testCase "a proof does not call readByte (it does not know the end of the input)" (rejected "affirm readByte() = 0 - 1; return 0;" "A proof calls readByte")
                , testCase "nor to say it is a byte" (rejected "affirm readByte() >= 0; return 0;" "A proof calls readByte")
                , testCase "nor to say two of them are one value" (rejected "affirm readByte() = readByte(); return 0;" "A proof calls readByte")
                , testCase "nor the size of a line" (rejected "affirm size(String::readLine(5)) = 0; return 0;" "reads the input")
                , testCase "nor to compare it with the value read before" (rejected "c = readByte(); affirm c = readByte(); return 0;" "A proof calls readByte")
                , testCase "nor are the sizes of two reads" (rejected "a = String::readLine(5); b = String::readLine(5); affirm size(a) = size(b); return 0;" "Could not prove")
                , testCase "a function that calls one that reads does not give the same value twice" (rejected "fn next() -> Int [{ }] [{ }] { return readByte(); }; a = next(); b = next(); affirm a = b; return 0;" "Could not prove: a = b")
                , testCase "a proof does not call a function that reads" (rejected "fn next() -> Int [{ }] [{ }] { return readByte(); }; fn f(x: Int) -> Int [{ affirm next() >= 0 - 1; }] [{ }] { return x; }; return f(1);" "reads the input")
                , testCase "a function that does not read still gives the same value twice" (valid "fn double(x: Int) -> Int [{ }] [{ }] { return x + x; }; a = double(3); b = double(3); affirm a = b; return 0;")
                , testCase "a limit that is negative is refused" (rejected "a = String::read(0 - 1); return 0;" "Could not prove: limit >= 0")
                , testCase "and the size of what is read is at most the limit" (valid "a = String::readLine(5); affirm size(a) <= 5; return 0;")
                , testCase "but not more than that" (rejected "a = String::readLine(5); affirm size(a) <= 4; return 0;" "Could not prove: <String as Sequence>::size(a) <= 4")
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
