module TestArrays (testArrays) where

import TersusTypes
import TestHarness

-- Array<T>: a sequence whose size is fixed when it is made. Reading and replacing work as they do for lists; what is known of
-- the size comes from where the array was made, and a function says what it needs of the size in its input contract.
testArrays :: Test
testArrays =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        rejected = parseValidateFailProgramHelper
        ints = VList . map VInt
        parseFails source = case parseValidProgramHelper source of
            Just err | take 11 err == "Parse faile" -> Nothing
            _ -> Just ("Expected a parse error for: " ++ source)
        dot =
            unlines
                [ "fn dot(a: Array<Int>, b: Array<Int>) -> Int [{ affirm size(a) = size(b); }] [{ }] {"
                , "    total = 0; i = 0;"
                , "    while i < size(a) [{ affirm i >= 0; affirm i <= size(a); affirm size(b) = size(a); }] shrinks size(a) - i {"
                , "        total = total + get(a, i) * get(b, i); i = i + 1;"
                , "    };"
                , "    return total;"
                , "};"
                ]
     in TestList
            "testArrays"
            [ TestList
                "construction"
                [ testCase "n copies of an element" (runs "return array(3, 7);" (ints [7, 7, 7]))
                , testCase "an array of no elements" (runs "return array(0, 7);" (ints []))
                , testCase "the size can be computed" (runs "n = 2 + 1; return array(n, 4);" (ints [4, 4, 4]))
                , testCase "a literal" (runs "return #[1, 2, 3];" (ints [1, 2, 3]))
                , testCase "an empty literal" (runs "a = #[]; return size(a);" (VInt 0))
                , testCase "an array of Bool" (runs "return array(2, true);" (VList [VBool True, VBool True]))
                , testCase "a literal of lists" (runs "return get(#[[1], [2, 3]], 1);" (ints [2, 3]))
                , testCase "an array of arrays has a copy of the element in each slot" (runs "m = array(2, array(2, 0)); m = set(m, 0, array(2, 5)); return m;" (VList [ints [5, 5], ints [0, 0]]))
                , testCase "an array of lists" (runs "rows = array(2, [1]); return rows;" (VList [ints [1], ints [1]]))
                , testCase "a list of arrays" (runs "rows = push([], array(2, 1)); return rows;" (VList [ints [1, 1]]))
                , testCase "an array is made in a function" (runs "fn make(n: Int) -> Array<Int> [{ affirm n >= 0; }] [{ affirm size(return) = n; }] { return array(n, 1); }; return make(2);" (ints [1, 1]))
                ]
            , TestList
                "reading and replacing"
                [ testCase "size" (runs "return size(array(4, 0));" (VInt 4))
                , testCase "get, first and last" (runs "a = #[4, 5, 6]; return get(a, 1) * 100 + first(a) * 10 + last(a);" (VInt 546))
                , testCase "set" (runs "a = #[1, 2, 3]; b = set(a, 1, 9); return b;" (ints [1, 9, 3]))
                , testCase "set does not change its argument" (runs "a = #[1, 2, 3]; b = set(a, 1, 9); return a;" (ints [1, 2, 3]))
                , testCase "an element can be written again and again" (runs "a = array(3, 0); a = set(a, 0, 1); a = set(a, 2, 3); a = set(a, 0, 4); return a;" (ints [4, 0, 3]))
                , testCase "equality is structural" (runs "return #[1, 2] = #[1, 2];" (VBool True))
                , testCase "inequality" (runs "return #[1, 2] != array(2, 1);" (VBool True))
                , testCase "arrays of different sizes differ" (runs "return array(2, 0) = array(3, 0);" (VBool False))
                , testCase "an array in a struct" (runs "struct Grid { cells: Array<Int> }; g = Grid { cells: array(3, 2) }; return get(g.cells, 2);" (VInt 2))
                , testCase "an array in an enum" (runs "enum Shape { Cells { cells: Array<Int> }, Empty }; s = Shape::Cells { cells: #[1, 2] }; return size((s as Shape::Cells).cells);" (VInt 2))
                ]
            , TestList
                "what is known of the size"
                [ testCase "from the size it is made with" (valid "a = array(4, 0); affirm size(a) = 4; return 0;")
                , testCase "from a computed size" (valid "n = 2 * 3; a = array(n, 0); affirm size(a) = 6; return 0;")
                , testCase "from a literal" (valid "a = #[1, 2, 3]; affirm size(a) = 3; return 0;")
                , testCase "set keeps the size" (valid "a = array(4, 0); b = set(a, 1, 9); affirm size(b) = 4; affirm get(b, 1) = 9; return 0;")
                , testCase "every element is the one it was made with" (valid "a = array(5, 9); affirm forall j in 0..5: get(a, j) = 9; return 0;")
                , testCase "an element can be read at an index in range" (valid "a = array(4, 8); return get(a, 3);")
                , testCase "a symbolic size needs to be shown not to be negative" (rejected "fn f(n: Int) -> Int { a = array(n, 0); return size(a); }; return f(2);" "Funct input validation failed")
                , testCase "a symbolic size that is not negative" (valid "fn f(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return = n; }] { a = array(n, 0); return size(a); }; return f(2);")
                , testCase "a size that is negative" (rejected "n = 2 - 5; return size(array(n, 0));" "Relation does not hold")
                , testCase "an index past the end" (rejected "a = array(3, 0); return get(a, 3);" "Relation does not hold")
                , testCase "first of an array with no elements" (rejected "a = array(0, 0); return first(a);" "Funct input validation failed")
                , testCase "a function states the size it makes" (valid "fn make(n: Int) -> Array<Int> [{ affirm n >= 0; }] [{ affirm size(return) = n; }] { return array(n, 0); }; a = make(5); affirm size(a) = 5; return 0;")
                , testCase "a function that says nothing of the size leaves it unknown" (rejected "fn make(n: Int) -> Array<Int> [{ affirm n >= 0; }] [{ }] { return array(n, 0); }; a = make(5); affirm size(a) = 5; return 0;" "Could not prove: size(a) = 5")
                ]
            , TestList
                "arrays of any size"
                [ testCase "a function takes arrays of the size its contract asks for" (runs (dot ++ "return dot(#[1, 2, 3], array(3, 2));") (VInt 12))
                , testCase "a size that does not meet the contract" (rejected (dot ++ "return dot(array(3, 1), array(4, 1));") "Could not prove: size(a) = size(b)")
                , testCase "the contract is met by what was made" (valid (dot ++ "a = array(4, 1); b = set(a, 0, 5); return dot(a, b);"))
                , testCase "a size checked when the program runs" (runs (dot ++ "fn safe(a: Array<Int>, b: Array<Int>) -> Int { if size(a) = size(b) { return dot(a, b); }; return -1; }; return safe(array(2, 1), array(3, 1)) + safe(array(2, 2), array(2, 3));") (VInt 11))
                , testCase "the other branch does not know the sizes agree" (rejected (dot ++ "fn safe(a: Array<Int>, b: Array<Int>) -> Int { if size(a) != size(b) { return dot(a, b); }; return -1; }; return safe(array(2, 1), array(3, 1));") "Could not prove: size(a) = size(b)")
                , testCase "a function that reads needs the size in its contract" (rejected "fn at(a: Array<Int>) -> Int { return get(a, 0); }; return at(array(1, 5));" "Relation lacks a proof")
                , testCase "a function that reads, with the contract" (runs "fn at(a: Array<Int>) -> Int [{ affirm size(a) > 0; }] [{ }] { return get(a, 0); }; return at(array(1, 5));" (VInt 5))
                , testCase "a size that is not enough" (rejected "fn at(a: Array<Int>) -> Int [{ affirm size(a) > 2; }] [{ }] { return get(a, 2); }; return at(array(2, 5));" "Could not prove: size(a) > 2")
                , testCase "a loop keeps the size of an array it sets" (runs "a = array(3, 0); i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; affirm size(a) = 3; }] shrinks 3 - i { a = set(a, i, i + 1); i = i + 1; }; return a;" (ints [1, 2, 3]))
                , testCase "a trait function takes an array" (runs "struct Box { n: Int }; trait Sized { fn cells(self: Self, a: Array<Int>) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Sized for Box { fn cells(self: Self, a: Array<Int>) -> Int [{ }] [{ affirm return >= 0; }] { return size(a) + self.n; }; }; b = Box { n: 1 }; return b.cells(array(2, 0));" (VInt 3))
                ]
            , TestList
                "types"
                [ testCase "an array has no push" (rejected "a = array(2, 0); a = push(a, 1); return 0;" "argument 1 of push: expected List<?>, got Array<Int>")
                , testCase "an array is not a list" (rejected "fn f(l: List<Int>) -> Int { return 0; }; return f(array(2, 0));" "argument 1 of f: expected List<Int>, got Array<Int>")
                , testCase "a list is not an array" (rejected "fn f(a: Array<Int>) -> Int { return 0; }; return f([1, 2]);" "argument 1 of f: expected Array<Int>, got List<Int>")
                , testCase "arrays and lists are not compared" (rejected "return array(2, 0) = [0, 0];" "Type error")
                , testCase "the size is an Int" (rejected "return size(array(true, 0));" "argument 1 of array: expected Int, got Bool")
                , testCase "an element has the type of the others" (rejected "a = array(2, 0); a = set(a, 0, true); return 0;" "argument 3 of set")
                , testCase "a literal has one element type" (rejected "return #[1, true];" "list element")
                , testCase "size is not an array" (rejected "return size(3);" "argument 1 of size")
                , testCase "array types are written in full" (parseFails "fn f(a: Array) -> Int { return 0; }; return 0;")
                , testCase "arrays of arrays" (valid "fn f(m: Array<Array<Int>>) -> Int [{ affirm size(m) > 0; }] [{ }] { return size(get(m, 0)); }; return f(array(2, array(3, 0)));")
                , testCase "the returned type is the declared one" (rejected "fn f() -> Array<Int> { return [1]; }; return 0;" "returned value: expected Array<Int>, got List<Int>")
                ]
            , TestList
                "parsing"
                [ testCase "a literal in a proof" (valid "a = #[1, 2]; affirm a = #[1, 2]; affirm size(#[4, 5, 6]) = 3; return 0;")
                , testCase "array in a proof" (valid "a = array(3, 4); affirm a = array(3, 4); return 0;")
                , testCase "a space before the type argument" (valid "fn f(a: Array <Int>) -> Int { return 0; }; return 0;")
                , testCase "a literal is an operand" (runs "return size(#[1, 2]) + size(#[3]);" (VInt 3))
                , testCase "a hash needs a literal" (parseFails "return #;")
                , testCase "variables are still named array" (runs "arrays = 2; return arrays;" (VInt 2))
                ]
            ]
