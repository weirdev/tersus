module TestArrays (testArrays) where

import TersusTypes
import TestHarness

-- Array<T, N>: N elements held inline, wherever the array is made. The size is a constant and part of the type; the validator
-- knows it from the type of every local, and the elements are any value that has a size.
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
                [ "fn dot(a: Array<Int, 3>, b: Array<Int, 3>) -> Int {"
                , "    total = 0; i = 0;"
                , "    while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i {"
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
                , testCase "the size is arithmetic on numbers" (runs "return array(2 * 3 - 1, 4);" (ints [4, 4, 4, 4, 4]))
                , testCase "a literal" (runs "return #[1, 2, 3];" (ints [1, 2, 3]))
                , testCase "an empty literal" (runs "a = #[]; return size(a);" (VInt 0))
                , testCase "an array of Bool" (runs "return array(2, true);" (VList [VBool True, VBool True]))
                , testCase "an array of arrays has a copy of the element in each slot" (runs "m = array(2, array(2, 0)); m = set(m, 0, array(2, 5)); return m;" (VList [ints [5, 5], ints [0, 0]]))
                , testCase "an array of arrays of arrays" (runs "return get(get(array(2, array(2, array(2, 3))), 1), 0);" (ints [3, 3]))
                , testCase "an array is made in a function and returned" (runs "fn make() -> Array<Int, 2> { return array(2, 1); }; return make();" (ints [1, 1]))
                , testCase "a function takes an array" (runs (dot ++ "return dot(#[1, 2, 3], array(3, 2));") (VInt 12))
                , testCase "the argument is not changed by the function" (runs "fn bump(a: Array<Int, 2>) -> Array<Int, 2> { a = set(a, 0, 9); return a; }; x = array(2, 1); y = bump(x); return x;" (ints [1, 1]))
                , testCase "a function can be given its own result" (runs "fn bump(a: Array<Int, 2>) -> Array<Int, 2> { return set(a, 0, get(a, 0) + 1); }; x = array(2, 1); x = bump(x); x = bump(x); return x;" (ints [3, 1]))
                ]
            , TestList
                "reading and replacing"
                [ testCase "size" (runs "return size(array(4, 0));" (VInt 4))
                , testCase "get, first and last" (runs "a = #[4, 5, 6]; return get(a, 1) * 100 + first(a) * 10 + last(a);" (VInt 546))
                , testCase "set" (runs "a = #[1, 2, 3]; b = set(a, 1, 9); return b;" (ints [1, 9, 3]))
                , testCase "set does not change its argument" (runs "a = #[1, 2, 3]; b = set(a, 1, 9); return a;" (ints [1, 2, 3]))
                , testCase "an element can be written again and again" (runs "a = array(3, 0); a = set(a, 0, 1); a = set(a, 2, 3); a = set(a, 0, 4); return a;" (ints [4, 0, 3]))
                , testCase "a row of a grid" (runs "m = array(2, array(2, 0)); m = set(m, 1, set(get(m, 1), 0, 7)); return get(m, 1);" (ints [7, 0]))
                , testCase "equality is structural" (runs "return #[1, 2] = #[1, 2];" (VBool True))
                , testCase "inequality" (runs "return #[1, 2] != array(2, 1);" (VBool True))
                , testCase "equality of grids" (runs "return array(2, array(2, 1)) = array(2, array(2, 1));" (VBool True))
                ]
            , TestList
                "what is known of the size"
                [ testCase "from the type of a local" (valid "a = array(4, 0); affirm size(a) = 4; return 0;")
                , testCase "from the type of a parameter" (valid "fn f(a: Array<Int, 4>) -> Int { return get(a, 3); }; return f(array(4, 1));")
                , testCase "from the type of a result" (valid "fn make() -> Array<Int, 5> { return array(5, 1); }; a = make(); affirm size(a) = 5; return get(a, 4);")
                , testCase "from the type of a row" (valid "m = array(2, array(3, 0)); row = get(m, 1); affirm size(row) = 3; return get(row, 2);")
                , testCase "through a loop that sets" (valid "a = array(3, 0); i = 0; while i < 3 [{ affirm i >= 0; affirm i <= 3; }] shrinks 3 - i { a = set(a, i, i); i = i + 1; }; affirm size(a) = 3; return get(a, 2);")
                , testCase "after a branch" (valid "a = array(2, 0); if size(a) > 1 { a = set(a, 0, 1); } else { a = set(a, 1, 1); }; affirm size(a) = 2; return get(a, 1);")
                , testCase "every element is the one it was made with" (valid "a = array(5, 9); affirm forall j in 0..5: get(a, j) = 9; return 0;")
                , testCase "set keeps the facts of the element it writes" (valid "a = array(4, 0); b = set(a, 1, 9); affirm get(b, 1) = 9; return 0;")
                , testCase "an index past the end of a local" (rejected "return get(array(3, 0), 3);" "Relation does not hold")
                , testCase "an index past the end of a parameter" (rejected "fn f(a: Array<Int, 4>) -> Int { return get(a, 4); }; return f(array(4, 1));" "Relation lacks a proof")
                , testCase "first of an array with no elements" (rejected "return first(array(0, 0));" "Could not prove: size(list) > 0")
                , testCase "a wrong claim about the size" (rejected "a = array(4, 0); affirm size(a) = 5; return 0;" "Could not prove: size(a) = 5")
                ]
            , TestList
                "types"
                [ testCase "the size is part of the type" (rejected "fn f(a: Array<Int, 3>) -> Int { return 0; }; return f(array(4, 1));" "argument 1 of f: expected Array<Int, 3>, got Array<Int, 4>")
                , testCase "two sizes are not compared" (rejected "return #[1, 2] = #[1, 2, 3];" "expected Array<Int, 2>, got Array<Int, 3>")
                , testCase "a function returns the size it says" (rejected "fn f() -> Array<Int, 3> { return array(2, 0); }; return 0;" "returned value: expected Array<Int, 3>, got Array<Int, 2>")
                , testCase "an array has no push" (rejected "a = array(2, 0); a = push(a, 1); return 0;" "argument 1 of push: expected List<?>, got Array<Int, 2>")
                , testCase "an array is not a list" (rejected "fn f(l: List<Int>) -> Int { return 0; }; return f(array(2, 0));" "argument 1 of f: expected List<Int>, got Array<Int, 2>")
                , testCase "a list is not an array" (rejected "fn f(a: Array<Int, 2>) -> Int { return 0; }; return f([1, 2]);" "argument 1 of f: expected Array<Int, 2>, got List<Int>")
                , testCase "the size is an Int" (rejected "return size(array(true, 0));" "argument 1 of array: expected Int, got Bool")
                , testCase "an element has the type of the others" (rejected "a = array(2, 0); a = set(a, 0, true); return 0;" "argument 3 of set")
                , testCase "a literal has one element type" (rejected "return #[1, true];" "list element")
                , testCase "size is not an array" (rejected "return size(3);" "argument 1 of size")
                , testCase "arrays of arrays" (valid "fn f(m: Array<Array<Int, 3>, 2>) -> Int { return size(get(m, 0)); }; return f(array(2, array(3, 0)));")
                ]
            , TestList
                "what an array can be"
                [ testCase "the size must be a constant" (rejected "n = 3; return size(array(n, 0));" "the size of an array must be a constant")
                , testCase "the size must be known where the array is made, not in a function" (rejected "fn f(n: Int) -> Int { return size(array(n, 0)); }; return f(2);" "the size of an array must be a constant")
                , testCase "the size cannot be negative" (rejected "return size(array(2 - 5, 0));" "the size of an array cannot be negative, got -3")
                , testCase "a step of the size that leaves the Int range is refused, not folded away" (rejected "return size(array(9223372036854775807 + 1 - 9223372036854775807, 0));" "integer overflow in the size of an array")
                , testCase "a product that leaves the Int range" (rejected "return size(array(4611686018427387904 * 2 / 4611686018427387904, 0));" "integer overflow in the size of an array")
                , testCase "a division by zero in the size" (rejected "return size(array(3 / 0, 0));" "division by zero in the size of an array")
                , testCase "a modulo by zero in the size" (rejected "return size(array(3 % 0, 0));" "modulo by zero in the size of an array")
                , testCase "a size can pass through a negative step" (runs "return size(array(5 - 10 + 8, 0));" (VInt 3))
                , testCase "the size in a proof is checked the same way" (rejected "affirm size(array(9223372036854775807 + 1 - 9223372036854775807, 0)) = 1; return 0;" "integer overflow in the size of an array")
                , testCase "an array that is too large for a frame" (rejected "return size(array(9000, 0));" "more than the 8192")
                , testCase "arrays inside an array count" (rejected "fn f(a: Array<Array<Int, 100>, 100>) -> Int { return 0; }; return 0;" "takes 10000 words")
                , testCase "an element that is a list" (runs "return array(2, [1]);" (VList [VList [VInt 1], VList [VInt 1]]))
                , testCase "an element that is a struct" (runs "struct P { x: Int }; return size(array(2, P { x: 1 }));" (VInt 2))
                , testCase "an element that is a function" (rejected "fn f() -> Int { return 1; }; return size(array(2, f));" "an array holds values that have a size (Int, Bool, a list, a struct, an enum, a Box or an array), not fn() -> Int")
                , testCase "a literal is made of Int, Bool and arrays" (rejected "return size(#[[1], [2]]);" "an array literal holds Int, Bool or arrays of them, not List<Int>")
                , testCase "an array of structs counts the words of the struct" (rejected "struct P { a: Int, b: Int, c: Int }; fn f(x: Array<P, 3000>) -> Int { return 0; }; return 0;" "takes 9000 words")
                , testCase "array is not a value" (rejected "h = array; return 0;" "cannot be used as a value")
                ]
            , TestList
                "arrays in structs, enums and lists"
                [ testCase "a struct with an array field" (runs "struct G { name: Int, cells: Array<Int, 3>, last: Int }; g = G { name: 1, cells: #[4, 5, 6], last: 9 }; return get(g.cells, 2) + g.last;" (VInt 15))
                , testCase "the fields around it are not disturbed" (runs "struct G { name: Int, cells: Array<Int, 3>, last: Int }; g = G { name: 1, cells: #[4, 5, 6], last: 9 }; return g.name * 10 + g.last;" (VInt 19))
                , testCase "an update builds a struct around a new array" (runs "struct G { name: Int, cells: Array<Int, 3> }; g = G { name: 1, cells: #[4, 5, 6] }; h = G { cells: set(g.cells, 0, 7), ..g }; return h.cells;" (ints [7, 5, 6]))
                , testCase "and leaves the first one as it was" (runs "struct G { name: Int, cells: Array<Int, 3> }; g = G { name: 1, cells: #[4, 5, 6] }; h = G { cells: set(g.cells, 0, 7), ..g }; return g.cells;" (ints [4, 5, 6]))
                , testCase "a struct with an array field is equal to another" (runs "struct G { cells: Array<Int, 2> }; return G { cells: #[1, 2] } = G { cells: array(2, 1) };" (VBool False))
                , testCase "an enum whose variants have arrays of different sizes" (runs "enum E { A { v: Array<Int, 2> }, B { x: Int, v: Array<Int, 4> }, C }; e = E::B { x: 1, v: array(4, 7) }; return match e { E::A { v: v } => size(v), E::B { x: x, v: v } => size(v) + x, E::C => 0 };" (VInt 5))
                , testCase "a list of arrays" (runs "rows = push(push([], #[1, 2]), #[3, 4]); return get(get(rows, 1), 0) + size(rows);" (VInt 5))
                , testCase "first and set on a list of arrays" (runs "rows = push(push([], #[1, 2]), #[3, 4]); rows = set(rows, 0, #[9, 9]); return first(rows);" (ints [9, 9]))
                , testCase "last of a list of arrays" (runs "rows = push(push([], #[1, 2]), #[3, 4]); rows = set(rows, 0, #[9, 9]); return last(rows);" (ints [3, 4]))
                , testCase "a list of arrays that grows" (runs "rows = []; i = 0; while i < 50 [{ affirm i >= 0; }] shrinks 50 - i { rows = push(rows, array(3, i)); i = i + 1; }; return get(get(rows, 49), 2) + size(rows);" (VInt 99))
                , testCase "a list of lists of arrays" (runs "inner = push([], #[1, 2]); outer = push([], inner); return get(get(get(outer, 0), 0), 1);" (VInt 2))
                , testCase "an array in a struct in a list" (runs "struct P { v: Array<Int, 2> }; ps = push([], P { v: #[3, 4] }); return get(get(ps, 0).v, 1);" (VInt 4))
                , testCase "the copy of a list of arrays is its own" (runs "rows = push([], #[1, 2]); other = rows; other = set(other, 0, #[0, 0]); return rows;" (VList [ints [1, 2]]))
                , testCase "an array of arrays in a struct" (runs "struct G { m: Array<Array<Int, 2>, 2> }; g = G { m: array(2, array(2, 5)) }; return get(get(g.m, 1), 0);" (VInt 5))
                , testCase "a function takes and gives a struct with an array" (runs "struct G { cells: Array<Int, 2> }; fn bump(g: G) -> G { return G { cells: set(g.cells, 0, get(g.cells, 0) + 1) }; }; return bump(bump(G { cells: #[1, 1] })).cells;" (ints [3, 1]))
                , testCase "what is known of the size of an array that was a field" (valid "struct G { cells: Array<Int, 3> }; g = G { cells: #[1, 2, 3] }; c = g.cells; affirm size(c) = 3; return get(c, 2);")
                , testCase "what is known of the size of an array that was an element" (valid "rows = push([], #[1, 2]); row = get(rows, 0); affirm size(row) = 2; return get(row, 1);")
                , testCase "an element of a list of arrays is read past its end" (rejected "rows = push([], #[1, 2]); return get(get(rows, 0), 2);" "Relation does not hold")
                , testCase "a list of arrays is read past its end" (rejected "rows = push([], #[1, 2]); return get(rows, 1);" "Relation does not hold")
                ]
            , TestList
                "parsing"
                [ testCase "a literal in a proof" (valid "a = #[1, 2]; affirm a = #[1, 2]; affirm size(#[4, 5, 6]) = 3; return 0;")
                , testCase "array in a proof" (valid "a = array(3, 4); affirm a = array(3, 4); return 0;")
                , testCase "spaces in the type" (valid "fn f(a: Array <Int , 2>) -> Int { return 0; }; return 0;")
                , testCase "a literal is an operand" (runs "return size(#[1, 2]) + size(#[3]);" (VInt 3))
                , testCase "a size can be left out, and then it is ?" (rejected "fn f(a: Array<Int>) -> Int { return 0; }; return 0;" "an array with no size (Array<T> is Array<T, ?>) can only be used behind a Box, as in Box<Array<Int>>")
                , testCase "or written as ?" (rejected "fn f(a: Array<Int, ?>) -> Int { return 0; }; return 0;" "an array with no size")
                , testCase "with spaces" (rejected "fn f(a: Array <Int , ?>) -> Int { return 0; }; return 0;" "an array with no size")
                , testCase "an array with no size is not held by value as a result" (rejected "fn f() -> Array<Int> { return #[1]; }; return 0;" "an array with no size")
                , testCase "nor as an element of a list" (rejected "fn f(l: List<Array<Int>>) -> Int { return 0; }; return 0;" "an array with no size")
                , testCase "nor as the parameter of a function value" (rejected "fn f(g: fn(Array<Int>) -> Int) -> Int { return 0; }; return 0;" "an array with no size")
                , testCase "nor as a field" (rejected "struct S { a: Array<Int> }; return 0;" "an array with no size")
                , testCase "nor as the element of an array that has a size" (rejected "fn f(a: Array<Array<Int>, 2>) -> Int { return 0; }; return 0;" "an array with no size")
                , testCase "the size of an array of arrays can be left out too" (rejected "fn f(a: Array<Array<Int, 3>>) -> Int { return 0; }; return 0;" "an array with no size")
                , testCase "a size is a number or ?" (parseFails "fn f(a: Array<Int, !>) -> Int { return 0; }; return 0;")
                , testCase "a type without a type argument" (parseFails "fn f(a: Array) -> Int { return 0; }; return 0;")
                , testCase "a hash needs a literal" (parseFails "return #;")
                , testCase "variables are still named array" (runs "arrays = 2; return arrays;" (VInt 2))
                ]
            , TestList
                "size parameters"
                [ testCase "one function over arrays of every size" (runs "fn dot<n>(a: Array<Int, n>, b: Array<Int, n>) -> Int { total = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { total = total + get(a, i) * get(b, i); i = i + 1; }; return total; };  return dot(#[1, 2, 3], #[4, 5, 6]) + dot(#[2], #[5]);" (VInt 42))
                , testCase "an empty array" (runs "fn dot<n>(a: Array<Int, n>, b: Array<Int, n>) -> Int { total = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { total = total + get(a, i) * get(b, i); i = i + 1; }; return total; };  return dot(#[], #[]);" (VInt 0))
                , testCase "the size is a value in the body" (runs "fn count<n>(a: Array<Int, n>) -> Int { return n; }; return count(#[1, 2, 3]) * 10 + count(array(4, 0));" (VInt 34))
                , testCase "and the length of the array" (valid "fn count<n>(a: Array<Int, n>) -> Int [{ }] [{ affirm return = size(a); }] { return n; }; return count(#[1, 2]);")
                , testCase "the size is a constant in a loop bound" (valid "fn sum<n>(a: Array<Int, n>) -> Int [{ define k = n; affirm k >= 0; }] [{ }] { t = 0; i = 0; while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i { t = t + get(a, i); i = i + 1; }; return t; }; return sum(#[1, 2, 3]);")
                , testCase "an array made from the size" (runs "fn ones<n>(a: Array<Int, n>) -> Array<Int, n> { return array(n, 1); }; return ones(#[7, 8, 9]);" (ints [1, 1, 1]))
                , testCase "the size of the result is known to the caller" (valid "fn ones<n>(a: Array<Int, n>) -> Array<Int, n> { return array(n, 1); }; r = ones(#[7, 8, 9]); affirm size(r) = 3; return get(r, 2);")
                , testCase "a size is given by an array of arrays" (runs "fn grid<n, m>(a: Array<Array<Int, n>, m>) -> Int { return n * 10 + m; }; return grid(array(3, array(2, 0)));" (VInt 23))
                , testCase "a function calls another with its own size" (runs "fn count<n>(a: Array<Int, n>) -> Int { return n; }; fn outer<m>(a: Array<Int, m>) -> Int { return count(a) + count(#[1, 2]); }; return outer(#[1]) + outer(#[1, 2, 3]);" (VInt 8))
                , testCase "a function calls itself" (runs "fn count<n>(a: Array<Int, n>, k: Int) -> Int [{ define z = k; affirm z >= 0; }] [{ }] shrinks k { if k = 0 { return n; }; return count(a, k - 1); }; return count(#[1, 2, 3], 4);" (VInt 3))
                , testCase "a Box of an array with the size" (runs "fn f<n>(a: Array<Int, n>, b: Box<Array<Int, n>>) -> Int { return size(b) + n; }; return f(#[1, 2], Box::new(#[3, 4]));" (VInt 4))
                , testCase "a Box of the array is given where any size is wanted" (runs "fn mk<n>(a: Array<Int, n>) -> Box<Array<Int>> { return Box::new(a); }; return size(mk(#[1, 2, 3]));" (VInt 3))
                , testCase "an array of a field" (runs "struct S { a: Array<Int, 2> }; fn count<n>(a: Array<Int, n>) -> Int { return n; }; s = S { a: #[1, 2] }; return count(s.a);" (VInt 2))
                , testCase "a size can be used in a contract" (valid "fn head<n>(a: Array<Int, n>) -> Int [{ define k = n; rewrite eqToGtZero k; affirm k > 0; }] [{ }] { return get(a, 0); }; return head(#[5, 6]);")
                , testCase "and is checked at the call" (rejected "fn head<n>(a: Array<Int, n>) -> Int [{ define k = n; rewrite eqToGtZero k; affirm k > 0; }] [{ }] { return get(a, 0); }; return head(#[]);" "Proof term is not greater than 0")
                , testCase "an index past the size" (rejected "fn past<n>(a: Array<Int, n>) -> Int { return get(a, n); }; return past(#[1]);" "Relation lacks a proof")
                , testCase "the arrays have to be of one size" (rejected "fn dot<n>(a: Array<Int, n>, b: Array<Int, n>) -> Int { total = 0; i = 0; while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i { total = total + get(a, i) * get(b, i); i = i + 1; }; return total; };  return dot(#[1, 2], #[1, 2, 3]);" "argument 2 of dot: expected Array<Int, 2>, got Array<Int, 3>")
                , testCase "a size the arguments do not decide" (rejected "fn f<n>() -> Int { return n; }; return f();" "the size n of f cannot be worked out from its arguments")
                , testCase "a size is not assigned" (rejected "fn f<n>(a: Array<Int, n>) -> Int { n = 3; return n; }; return f(#[1]);" "n is a size parameter of the function, which a call gives, and it cannot be assigned")
                , testCase "a name has to be declared to be a size" (rejected "fn f(a: Array<Int, k>) -> Int { return 0; }; return 1;" "k is not a size here")
                , testCase "a size is not named twice" (rejected "fn f<n, n>(a: Array<Int, n>) -> Int { return 0; }; return 1;" "names a size twice")
                , testCase "a size is not also a parameter" (rejected "fn f<n>(n: Int, a: Array<Int, n>) -> Int { return 0; }; return 1;" "names a size twice, or the same as a parameter")
                , testCase "the function is called, not named" (rejected "fn f<n>(a: Array<Int, n>) -> Int { return n; }; h = f; return 0;" "f has size parameters <n>, so it is called")
                , testCase "arithmetic on a size is not a size" (rejected "fn f<n>(a: Array<Int, n>) -> Int { return size(array(n + 1, 0)); }; return f(#[1]);" "the size of an array must be a constant")
                , testCase "no size parameters in an impl" (rejected "struct S { x: Int }; impl S { fn f<n>(a: Array<Int, n>) -> Int { return n; }; }; return 0;" "size parameters, which a function of an impl cannot have yet")
                , testCase "the declaration is parsed with spaces" (runs "fn count < n , m > (a: Array<Int, n>, b: Array<Int, m>) -> Int { return n * 10 + m; }; return count(#[1], #[1, 2]);" (VInt 12))
                , testCase "an empty list of sizes" (parseFails "fn f<>(a: Int) -> Int { return 0; }; return 1;")
                ]
            , TestList
                "structs with sizes"
                [ testCase "a struct for a size" (runs "struct P<n> { id: Int, body: Array<Int, n> };  p = P<3> { id: 7, body: #[1, 2, 3] }; return p.id + size(p.body) + get(p.body, 2);" (VInt 13))
                , testCase "a value is printed as the struct" (runs "struct P<n> { id: Int, body: Array<Int, n> };  return P<2> { id: 1, body: #[5, 6] };" (VData "P" [("id", VInt 1), ("body", VList [VInt 5, VInt 6])]))
                , testCase "the size is known to the validator" (valid "struct P<n> { id: Int, body: Array<Int, n> };  p = P<3> { id: 7, body: #[1, 2, 3] }; affirm size(p.body) = 3; return get(p.body, 2);")
                , testCase "a field is read past its size" (rejected "struct P<n> { id: Int, body: Array<Int, n> };  p = P<3> { id: 7, body: #[1, 2, 3] }; return get(p.body, 3);" "Relation does not hold")
                , testCase "a size is a type" (rejected "struct P<n> { id: Int, body: Array<Int, n> };  fn f(p: P<3>) -> Int { return 0; }; return f(P<2> { id: 1, body: #[1, 2] });" "argument 1 of f: expected P<3>, got P<2>")
                , testCase "structs of two sizes are not compared" (rejected "struct P<n> { id: Int, body: Array<Int, n> };  return P<3> { id: 1, body: #[1, 2, 3] } = P<2> { id: 1, body: #[1, 2] };" "expected P<3>, got P<2>")
                , testCase "structs of one size are" (runs "struct P<n> { id: Int, body: Array<Int, n> };  return P<2> { id: 1, body: #[1, 2] } = P<2> { id: 1, body: #[1, 2] };" (VBool True))
                , testCase "the body has the size" (rejected "struct P<n> { id: Int, body: Array<Int, n> };  x = P<2> { id: 1, body: #[5] }; return 1;" "field body of P<2>: expected Array<Int, 2>, got Array<Int, 1>")
                , testCase "a function over any size" (runs "struct P<n> { id: Int, body: Array<Int, n> };  fn total<m>(p: P<m>) -> Int { s = p.id; i = 0; while i < m [{ affirm i >= 0; affirm i <= m; }] shrinks m - i { s = s + get(p.body, i); i = i + 1; }; return s; }; return total(P<3> { id: 7, body: #[1, 2, 3] }) + total(P<1> { id: 1, body: #[10] });" (VInt 24))
                , testCase "its size is the size of the struct" (runs "struct P<n> { id: Int, body: Array<Int, n> };  fn width<m>(p: P<m>) -> Int { return m; }; return width(P<4> { id: 0, body: array(4, 0) });" (VInt 4))
                , testCase "a struct is made in a function that has the size" (runs "struct P<n> { id: Int, body: Array<Int, n> };  fn blank<m>(a: Array<Int, m>) -> P<m> { return P<m> { id: m, body: array(m, 0) }; }; return blank(#[1, 2]);" (VData "P" [("id", VInt 2), ("body", VList [VInt 0, VInt 0])]))
                , testCase "a struct that holds another of its size" (runs "struct I<n> { cells: Array<Int, n> }; struct O<n> { tag: Int, inner: I<n> }; fn w<m>(o: O<m>) -> Int { return m * 10 + o.tag; }; return w(O<2> { tag: 4, inner: I<2> { cells: #[1, 2] } });" (VInt 24))
                , testCase "an update keeps the size" (runs "struct P<n> { id: Int, body: Array<Int, n> };  a = P<2> { id: 1, body: #[5, 6] }; b = P<2> { id: 9, ..a }; return b.id + get(b.body, 1);" (VInt 15))
                , testCase "a Box and a list of them" (runs "struct P<n> { id: Int, body: Array<Int, n> };  b = Box::new(P<2> { id: 1, body: #[5, 6] }); l = push([], P<2> { id: 2, body: #[7, 8] }); return b.id + size(b.body) + get(l, 0).id;" (VInt 5))
                , testCase "a struct with sizes holds itself in a Box" (valid "struct L<n> { v: Array<Int, n>, next: Box<L<n>> }; return 0;")
                , testCase "but not by value" (rejected "struct L<n> { v: Array<Int, n>, next: L<n> }; return 0;" "L holds itself, so it would have no size")
                , testCase "its sizes are given" (rejected "struct P<n> { id: Int, body: Array<Int, n> };  fn f(p: P) -> Int { return 0; }; return 1;" "P has sizes <n>, which a type gives: P<n>")
                , testCase "as many as it has" (rejected "struct P<n> { id: Int, body: Array<Int, n> };  x = P<1, 2> { id: 1, body: #[5] }; return 1;" "P has 1 sizes (n), got 2")
                , testCase "a size that no field uses still fits in an Int" (runs "struct Tag<n> { x: Int }; fn width<m>(p: Tag<m>) -> Int { return m; }; return width(Tag<9223372036854775807> { x: 0 });" (VInt 9223372036854775807))
                , testCase "and not more" (rejected "struct Tag<n> { x: Int }; fn width<m>(p: Tag<m>) -> Int { return m; }; return width(Tag<9223372036854775808> { x: 0 });" "the size 9223372036854775808 in Tag<9223372036854775808> is more than an Int can hold")
                , testCase "a size is a name that the struct declares" (rejected "struct Q<n> { body: Array<Int, k> }; return 1;" "k is not a size here")
                , testCase "a size is not named twice" (rejected "struct Q<n, n> { body: Array<Int, n> }; return 1;" "names a size twice")
                , testCase "a size that is not given" (rejected "struct P<n> { id: Int, body: Array<Int, n> };  fn f(p: P<?>) -> Int { return 0; }; return 1;" "a size that is not given")
                , testCase "the declaration is parsed with spaces" (runs "struct Q < n , m > { a: Array<Int, n>, b: Array<Int, m> }; q = Q < 1 , 2 > { a: #[1], b: #[2, 3] }; return size(q.a) * 10 + size(q.b);" (VInt 12))
                ]
            , TestList
                "elements that own something"
                [ testCase "n copies of a list" (runs "a = array(3, push([], 1)); return a;" (VList [VList [VInt 1], VList [VInt 1], VList [VInt 1]]))
                , testCase "a copy is its own" (runs "a = array(2, push([], 1)); c = a; c = set(c, 0, push(push([], 8), 9)); return a;" (VList [VList [VInt 1], VList [VInt 1]]))
                , testCase "an element is replaced" (runs "a = array(3, push([], 1)); a = set(a, 1, push(push([], 2), 3)); return a;" (VList [VList [VInt 1], VList [VInt 2, VInt 3], VList [VInt 1]]))
                , testCase "an element is read" (runs "a = array(2, push(push([], 5), 6)); return size(get(a, 0)) + get(get(a, 1), 1);" (VInt 8))
                , testCase "an element that is read and changed does not change the array" (runs "a = array(2, push([], 1)); l = get(a, 0); l = push(l, 7); return a;" (VList [VList [VInt 1], VList [VInt 1]]))
                , testCase "an array of arrays of lists" (runs "a = array(2, array(2, push([], 5))); return get(get(a, 1), 0);" (VList [VInt 5]))
                , testCase "an array of structs that own lists" (runs "struct P { xs: List<Int>, n: Int }; a = array(2, P { xs: push([], 1), n: 7 }); a = set(a, 0, P { xs: [], n: 9 }); return a;" (VList [VData "P" [("xs", VList []), ("n", VInt 9)], VData "P" [("xs", VList [VInt 1]), ("n", VInt 7)]]))
                , testCase "an array of Boxes" (runs "a = array(2, Box::new(5)); return Box::unbox(get(a, 1));" (VInt 5))
                , testCase "arrays of lists are compared" (runs "return array(2, push([], 1)) = array(2, push([], 1));" (VBool True))
                , testCase "and told apart" (runs "return array(2, push([], 1)) != array(2, []);" (VBool True))
                , testCase "a function takes and gives one" (runs "fn grow(a: Array<List<Int>, 2>) -> Array<List<Int>, 2> { return set(a, 1, push(get(a, 1), 9)); }; return grow(grow(array(2, [])));" (VList [VList [], VList [VInt 9, VInt 9]]))
                , testCase "or lends it" (runs "fn total(a: &Array<List<Int>, 2>) -> Int { return size(get(a, 0)) + size(get(a, 1)); }; a = array(2, push([], 1)); return total(a) + total(a) + size(a);" (VInt 6))
                , testCase "a struct has one" (runs "struct H { items: Array<List<Int>, 2>, n: Int }; h = H { items: array(2, push([], 3)), n: 1 }; g = H { n: 2, ..h }; return g;" (VData "H" [("items", VList [VList [VInt 3], VList [VInt 3]]), ("n", VInt 2)]))
                , testCase "an enum has one" (runs "enum Shape { Pair { xs: Array<List<Int>, 2> }, None }; s = Shape::Pair { xs: array(2, push([], 4)) }; return match s { Shape::Pair { xs: xs } => size(get(xs, 1)), Shape::None => 0 };" (VInt 1))
                , testCase "a list has one" (runs "l = push(push([], array(2, push([], 1))), array(2, [])); return get(l, 0);" (VList [VList [VInt 1], VList [VInt 1]]))
                , testCase "the size of an element array is known" (valid "a = array(2, push([], 1)); affirm size(a) = 2; return size(get(a, 0));")
                , testCase "an index past the end" (rejected "a = array(2, push([], 1)); return get(a, 2);" "Relation does not hold")
                , testCase "a function with sizes takes one" (runs "fn count<n>(a: Array<List<Int>, n>) -> Int { return n; }; return count(array(3, []));" (VInt 3))
                ]
            ]
