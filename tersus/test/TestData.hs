module TestData
    ( testTypeCheck
    , testGenericLists
    , testStructs
    , testEnums
    , testEnumCast
    ) where

import Data.List (isInfixOf)
import Parse
import StdLib
import TersusTypes
import TypeCheck
import Utils
import TestHarness

testTypeCheck :: Test
testTypeCheck =
    let typeError source expected =
            case parseStatementBlock source of
                Left err -> Just ("Parse failed: " ++ show err)
                Right stmts -> testAssertErrorContains expected (typeCheck stmts)
        typeOk source =
            case parseStatementBlock source of
                Left err -> Just ("Parse failed: " ++ show err)
                Right stmts -> case typeCheck stmts of
                    Ok () -> Nothing
                    Error e -> Just ("Type check failed: " ++ e)
        parseFails source =
            case parseStatementBlock source of
                Left _ -> Nothing
                Right _ -> Just ("Expected a parse error for: " ++ source)
     in testCaseSeq
            "testTypeCheck"
            [ -- Well typed programs
              typeOk "x = 1; l = [1, 2]; y = size(l) + x; b = y < 3; affirm b = b;"
            , typeOk "fn f(l: List<Int>, i: Int) -> List<Int> { return push(l, get(l, i)); }; r = f([1], 0);"
            , typeOk "fn isBig(n: Int) -> Bool { return n > 9; }; if isBig(10) { x = 1; };"
            , typeOk "fn apply(g: fn(Int) -> Int, n: Int) -> Int { return g(g(n)); }; fn inc(n: Int) -> Int { return n + 1; }; r = apply(inc, 1);"
            , typeOk "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; }; x = f(2);"
            , typeOk "l = []; l = push(l, 1); m = set(l, 0, 5); x = first(m) + last(m);"
            , -- Equality works on any type, ordering only on Int
              typeOk "affirm [1] = [1]; affirm true = true;"
            , typeError "affirm [1] < [2];" "expected Int, got List<Int>"
            , typeError "for i in 0..true { x = 1; };" "expected Int, got Bool"
            , typeError "for i in [1]..3 { x = 1; };" "expected Int, got List<Int>"
            , typeError "for x in 3 { y = 1; };" "expected List<?>, got Int"
            , typeError "while 1 < 2 shrinks true { x = 2; };" "shrinks needs an Int, an enum or a struct, got Bool"
            , -- Builtins
              typeError "x = size(5);" "argument 1 of size: expected List<?>, got Int"
            , typeError "l = [1]; x = push(l, [2]);" "argument 2 of push: expected Int, got List<Int>"
            , typeError "x = set([1], 0, true);" "argument 3 of set: expected Int, got Bool"
            , typeError "x = get([1], [0]);" "argument 2 of get: expected Int, got List<Int>"
            , typeError "x = 1 + [1];" "expected Int, got List<Int>"
            , -- Variables keep their type
              typeError "x = 1; x = [1];" "assignment to x: expected Int, got List<Int>"
            , typeError "x = y;" "Undefined variable: y"
            , typeError "if 1 { x = 2; };" "condition of if: expected Bool, got Int"
            , typeError "while 1 [{ }] { x = 2; };" "condition of while: expected Bool, got Int"
            , -- A variable assigned in a branch is local to it
              typeError "if true { t = 1; }; x = t;" "Undefined variable: t"
            , -- Functions: parameters, return and arity
              typeError "fn f(n: Int) -> Int { l = [1]; return l; };" "returned value: expected Int, got List<Int>"
            , typeError "fn f(n: Int) -> Int { return n; }; x = f([1]);" "argument 1 of f: expected Int, got List<Int>"
            , typeError "fn f(n: Int) -> Int { return n; }; x = f(1, 2);" "f takes 1 arguments, got 2"
            , typeError "fn f(n: Int) -> Bool { return n; };" "returned value: expected Bool, got Int"
            , typeError "x = 1; y = x(2);" "x is not a function"
            , -- The program has one return type, the first return's, as a function has its declared one
              typeError "if true { return 1; } else { return false; };" "returned value of the program: expected Int, got Bool"
            , typeError "x = 1; if x = 1 { return [1]; }; return 2;" "returned value of the program: expected List<Int>, got Int"
            , -- (a function has its own, and a return in it does not count for the program)
              typeOk "fn f(n: Int) -> Bool { return n = 1; }; if true { return 1; } else { return 2; };"
            , -- Equality is structural, which functions do not have
              typeError "fn f(n: Int) -> Int { return n; }; b = f = f;" "functions cannot be compared"
            , typeError "fn f(n: Int) -> Int { return n; }; fn g(n: Int) -> Int { return n; }; affirm f != g;" "functions cannot be compared"
            , -- Bodies see only their parameters and earlier functions
              typeError "y = 1; fn f(n: Int) -> Int { return y; };" "Undefined variable: y"
            , typeError "fn f(n: Int) -> Int { return g(n); }; fn g(n: Int) -> Int { return n; };" "Undefined variable: g"
            , typeOk "fn f(n: Int) -> Int { return n; }; fn g(n: Int) -> Int { return f(n); };"
            , -- Contracts and proofs are typed too
              typeError "fn f(n: Int) -> Int [{ affirm n; }] [{ }] { return n; };" "affirmed proof: expected Bool, got Int"
            , typeError "fn f(l: List<Int>) -> Int [{ }] [{ affirm return = l; }] { return 1; };" "expected Int, got List<Int>"
            , typeError "fn f(l: List<Int>) -> Int [{ affirm forall j in 0..size(l): get(l, j); }] [{ }] { return 1; };" "body of forall: expected Bool"
            , typeOk "fn f(l: List<Int>) -> Int [{ affirm size(l) > 0; define s = size(l); }] [{ affirm s > 0; }] { return first(l); };"
            , -- Annotations are required
              parseFails "fn f(n) -> Int { return n; };"
            , parseFails "fn f(n: Int) { return n; };"
            , typeError "fn f(n: Float) -> Int { return 1; };" "unknown type Float"
            , -- validate runs the check first
              parseValidateFailProgramHelper "fn f(n: Int) -> List<Int> { return n; }; x = 1;" "returned value: expected List<Int>, got Int"
            ]

testGenericLists :: Test
testGenericLists =
    let ints = VList . map VInt
     in testCaseSeq
            "testGenericLists"
            [ -- Lists of any element type, in evaluation
              parseEvalProgramHelper "return [true, false];" (Just (VList [VBool True, VBool False]))
            , parseEvalProgramHelper "return [[1, 2], [3]];" (Just (VList [ints [1, 2], ints [3]]))
            , parseEvalProgramHelper "return get([[1, 2], [3]], 1);" (Just (ints [3]))
            , parseEvalProgramHelper "return size([[1, 2], [3], []]);" (Just (VInt 3))
            , parseEvalProgramHelper "return push([[1]], [2, 3]);" (Just (VList [ints [1], ints [2, 3]]))
            , parseEvalProgramHelper "return [1, 2] = [1, 2];" (Just (VBool True))
            , parseEvalProgramHelper "return [true] != [false];" (Just (VBool True))
            , parseEvalProgramHelper "return first([true]);" (Just (VBool True))
            , parseEvalProgramHelper "return set([true, true], 1, false);" (Just (VList [VBool True, VBool False]))
            , parseEvalProgramHelper "return [-1, 2];" (Just (ints [-1, 2]))
            , -- Types
              parseValidProgramHelper "fn flags(n: Int) -> List<Bool> { return push([true], n > 0); }; x = flags(1);"
            , -- A builtin is used at its own element type each time
              parseValidProgramHelper "x = push([], push([], 1)); y = push([true], false);"
            , parseValidateFailProgramHelper "e = []; x = push(e, 1); y = push(e, push(e, 1));" "argument 2 of push: expected Int, got List<Int>"
            , parseValidProgramHelper "fn pair(a: Int, b: Int) -> List<List<Int>> { return push(push([], push([], a)), push([], b)); }; x = pair(1, 2);"
            , parseValidateFailProgramHelper "x = [1, true];" "list element: expected Int, got Bool"
            , parseValidateFailProgramHelper "x = [[1], 2];" "list element: expected List<Int>, got Int"
            , parseValidateFailProgramHelper "fn f(l: List<Bool>) -> Int { return first(l); };" "returned value: expected Int, got Bool"
            , parseValidateFailProgramHelper "x = push([true], 1);" "argument 2 of push: expected Bool, got Int"
            , -- Validation: elements of any type are terms, so contracts and foralls work on them
              parseValidProgramHelper "fn f(l: List<Bool>) -> Bool [{ affirm size(l) > 0; }] [{ affirm return = get(l, 0); }] { return first(l); };"
            , parseValidProgramHelper "l = [true, false]; affirm get(l, 1) = false; affirm size(l) = 2;"
            , parseValidProgramHelper "m = [[1, 2], [3]]; affirm size(get(m, 0)) = 2; affirm get(get(m, 0), 1) = 2;"
            , parseValidateFailProgramHelper "l = [true, false]; affirm get(l, 1) = true;" "Could not prove: get(l, 1) = true"
            , parseValidProgramHelper "fn f(m: List<List<Int>>) -> List<List<Int>> [{ affirm size(m) > 0; }] [{ affirm size(return) = size(m) + 1; affirm get(return, size(m)) = get(m, 0); }] { return push(m, first(m)); };"
            , parseValidProgramHelper "fn f(m: List<List<Int>>) -> List<List<Int>> [{ affirm size(m) > 0; affirm forall j in 0..size(m): size(get(m, j)) = 2; }] [{ affirm forall j in 0..size(return): size(get(return, j)) = 2; }] { return push(m, first(m)); };"
            ]

testStructs :: Test
testStructs =
    let node = "struct Node { value: Int, prev: Int, next: Int };"
        point = "struct Point { x: Int, y: Int };"
        ctor name fields = builtinFunct (Ctor name fields)
        field name = builtinFunct (Field Nothing name)
        fieldOf struct name = builtinFunct (Field (Just struct) name)
     in testCaseSeq
            "testStructs"
            [ -- Parsing: a literal is the application of the constructor, in declaration order
              case parseStatementBlock (point ++ "p = Point { y: 2, x: 1 };") of
                Right [_, Assign "p" expr] -> testAssertEq expr (F (Val (ctor "Point" ["x", "y"])) [Val (VInt 1), Val (VInt 2)])
                other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock (point ++ "q = Point { x: 5, ..p };") of
                Right [_, Assign "q" expr] -> testAssertEq expr (F (Val (ctor "Point" ["x", "y"])) [Val (VInt 5), F (Val (fieldOf "Point" "y")) [Var "p"]])
                other -> Just ("Unexpected parse: " ++ show other)
            , case parseStatementBlock (point ++ "v = p.x + 1;") of
                Right [_, Assign "v" expr] -> testAssertEq expr (F (Val (builtinFunct Plus)) [F (Val (field "x")) [Var "p"], Val (VInt 1)])
                other -> Just ("Unexpected parse: " ++ show other)
            , parseEvalProgramHelper (point ++ "p = Point { x: 1, y: 2 }; return p.y;") (Just (VInt 2))
            , -- Chains of fields and ranges that use `..`
              parseEvalProgramHelper (point ++ "struct Line { from: Point, to: Point }; l = Line { from: Point { x: 1, y: 2 }, to: Point { x: 3, y: 4 } }; return l.to.x;") (Just (VInt 3))
            , parseValidProgramHelper "fn f(l: List<Int>, n: Int) -> Int [{ affirm forall j in 0..n: j < n; }] [{ }] { return n; };"
            , -- The base of an update has the struct's type, and an update must copy something
              parseValidateFailProgramHelper (point ++ "struct Other { x: Int, y: Int }; p = Point { x: 1, ..Other { x: 2, y: 3 } };") "base of an update of Point: expected Point, got Other"
            , parseValidateFailProgramHelper (point ++ "p = Point { x: 1, ..5 };") "base of an update of Point: expected Point, got Int"
            , parseFailsWith (point ++ "p = Point { x: 1, y: 2, ..p };") "copies nothing"
            , parseFailsWith "struct Int { x: Int };" "builtin type"
            , parseFailsWith "struct List { x: Int };" "builtin type"
            , -- Parse errors
              parseFailsWith (point ++ "p = Point { x: 1 };") "lacks field y"
            , parseFailsWith (point ++ "p = Point { x: 1, y: 2, z: 3 };") "has no field z"
            , parseFailsWith (point ++ "p = Point { x: 1, x: 2, y: 3 };") "repeats a field"
            , parseFailsWith "struct S { a: Int, a: Int };" "repeats a field"
            , -- Evaluation
              parseEvalProgramHelper (point ++ "p = Point { x: 1, y: 2 }; return p;") (Just (VData "Point" [("x", VInt 1), ("y", VInt 2)]))
            , parseEvalProgramHelper (point ++ "p = Point { x: 1, y: 2 }; q = Point { y: 9, ..p }; return q;") (Just (VData "Point" [("x", VInt 1), ("y", VInt 9)]))
            , parseEvalProgramHelper (point ++ "return Point { x: 1, y: 2 } = Point { y: 2, x: 1 };") (Just (VBool True))
            , parseEvalProgramHelper (point ++ "return Point { x: 1, y: 2 } = Point { x: 1, y: 3 };") (Just (VBool False))
            , parseEvalProgramHelper (point ++ "fn sum(p: Point) -> Int { return p.x + p.y; }; return sum(Point { x: 3, y: 4 });") (Just (VInt 7))
            , parseEvalProgramHelper (point ++ "l = push([], Point { x: 1, y: 2 }); return get(l, 0).y;") (Just (VInt 2))
            , -- Type checking
              parseValidateFailProgramHelper (point ++ "p = Point { x: true, y: 2 };") "field x of Point: expected Int, got Bool"
            , parseValidateFailProgramHelper (point ++ "p = Point { x: 1, y: 2 }; z = p.z;") "Point has no field z"
            , parseValidateFailProgramHelper "x = 1; y = x.f;" "is read from a Int"
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Int { return p; };") "returned value: expected Int, got Point"
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Int { return 1; }; x = f(3);") "argument 1 of f: expected Point, got Int"
            , parseValidateFailProgramHelper "fn f(p: Missing) -> Int { return 1; };" "unknown type Missing"
            , parseValidateFailProgramHelper (point ++ point) "Type already defined: Point"
            , parseValidateFailProgramHelper (point ++ "struct Other { x: Int, y: Int }; p = Point { x: 1, y: 2 }; o = Other { x: 1, y: 2 }; affirm p = o;") "expected Point, got Other"
            , parseValidateFailProgramHelper "struct S { a: Missing };" "unknown type Missing"
            , -- Validation: fields of a literal, updates and their frame
              parseValidProgramHelper (point ++ "p = Point { x: 1, y: 2 }; affirm p.x = 1; affirm p.y = 2;")
            , parseValidProgramHelper (point ++ "fn f(p: Point) -> Point [{ }] [{ affirm return.x = 5; affirm return.y = p.y; }] { return Point { x: 5, ..p }; };")
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Point [{ }] [{ affirm return.y = p.x; }] { return Point { x: 5, ..p }; };") "Could not prove: return.y = p.x"
            , parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Point [{ }] [{ affirm return.x = p.x; }] { return Point { x: 5, ..p }; };") "Could not prove: return.x = p.x"
            , parseValidProgramHelper (point ++ "fn f(p: Point, q: Point) -> Int [{ affirm p = q; }] [{ affirm return = 0; }] { affirm p.x = q.x; return 0; };")
            , -- Two constructions that are equal agree field by field
              parseValidProgramHelper (point ++ "fn f(a: Int, b: Int, c: Int, d: Int) -> Int [{ affirm Point { x: a, y: b } = Point { x: c, y: d }; }] [{ }] { affirm a = c; affirm b = d; return 0; };")
            , parseValidateFailProgramHelper (point ++ "fn f(a: Int, b: Int, c: Int, d: Int) -> Int [{ affirm Point { x: a, y: b } = Point { x: c, y: d }; }] [{ }] { affirm a = d; return 0; };") "Could not prove: a = d"
            , parseValidateFailProgramHelper (point ++ "fn f(a: Int, b: Int, c: Int, d: Int) -> Int [{ }] [{ }] { affirm Point { x: a, y: b } = Point { x: c, y: d }; return 0; };") "Could not prove"
            , -- Known values
              parseValidProgramHelper (point ++ "p = Point { x: 1, y: 2 }; q = Point { y: 2, x: 1 }; affirm p = q;")
            , parseValidateFailProgramHelper (point ++ "p = Point { x: 1, y: 2 }; q = Point { x: 1, y: 3 }; affirm p = q;") "Could not prove: p = q"
            , -- Arithmetic reaches the fields
              parseValidProgramHelper (point ++ "fn f(p: Point) -> Int [{ affirm p.x > 0; }] [{ affirm return > 1; }] { return p.x + 1; };")
            , parseValidProgramHelper (node ++ "fn f(n: Node) -> Node [{ affirm n.next < 5; }] [{ affirm return.next < 6; }] { return Node { next: n.next + 1, ..n }; };")
            , -- Lists of structs
              parseValidProgramHelper (node ++ "fn f(nodes: List<Node>, i: Int) -> List<Node> [{ affirm i >= 0; affirm i < size(nodes); }] [{ affirm get(return, i).next = 5; affirm get(return, i).value = get(nodes, i).value; affirm forall j where j >= 0, j < size(nodes), j != i: get(return, j) = get(nodes, j); }] { return set(nodes, i, Node { next: 5, ..get(nodes, i) }); };")
            , parseValidateFailProgramHelper (node ++ "fn f(nodes: List<Node>, i: Int) -> List<Node> [{ affirm i >= 0; affirm i < size(nodes); }] [{ affirm get(return, i).prev = 5; }] { return set(nodes, i, Node { next: 5, ..get(nodes, i) }); };") "Could not prove: get(return, i).prev = 5"
            , parseValidProgramHelper (node ++ "fn f(nodes: List<Node>) -> List<Node> [{ }] [{ affirm size(return) = size(nodes) + 1; affirm get(return, size(nodes)).value = 7; }] { return push(nodes, Node { value: 7, prev: 0, next: 0 }); };")
            , -- Eta is not known: a struct is not equal to a rebuilt copy of its fields
              parseValidateFailProgramHelper (point ++ "fn f(p: Point) -> Int [{ }] [{ }] { affirm Point { x: p.x, y: p.y } = p; return 0; };") "Could not prove: Point { x: p.x, y: p.y } = p"
            ]
  where
    parseFailsWith source expected =
        case parseStatementBlock source of
            Left err -> if expected `isInfixOf` show err then Nothing else Just ("Wrong parse error: " ++ show err)
            Right _ -> Just ("Expected a parse error for: " ++ source)

testEnums :: Test
testEnums =
    let shape = "enum Shape { Circle { radius: Int }, Rect { width: Int, height: Int }, Empty };"
        opt = "enum Opt { None, Some { value: Int } };"
        tree = "enum Tree { Leaf, Branch { left: Tree, value: Int, right: Tree } };"
        parseFailsWith source expected =
            case parseStatementBlock source of
                Left err -> if expected `isInfixOf` show err then Nothing else Just ("Wrong parse error: " ++ show err)
                Right _ -> Just ("Expected a parse error for: " ++ source)
     in testCaseSeq
            "testEnums"
            [ -- Values
              parseEvalProgramHelper (shape ++ "return Shape::Circle { radius: 2 };") (Just (VData "Shape::Circle" [("radius", VInt 2)]))
            , parseEvalProgramHelper (shape ++ "return Shape::Empty;") (Just (VData "Shape::Empty" []))
            , parseEvalProgramHelper (shape ++ "return Shape::Empty = Shape::Empty;") (Just (VBool True))
            , parseEvalProgramHelper (shape ++ "return Shape::Empty = Shape::Circle { radius: 1 };") (Just (VBool False))
            , parseEvalProgramHelper (shape ++ "return Shape::Circle { radius: 1 } != Shape::Circle { radius: 2 };") (Just (VBool True))
            , -- is
              parseEvalProgramHelper (shape ++ "s = Shape::Rect { width: 1, height: 2 }; return s is Shape::Rect;") (Just (VBool True))
            , parseEvalProgramHelper (shape ++ "s = Shape::Rect { width: 1, height: 2 }; return s is Shape::Circle;") (Just (VBool False))
            , parseEvalProgramHelper (shape ++ "s = Shape::Empty; if s is Shape::Empty { return 1; } else { return 2; };") (Just (VInt 1))
            , -- match as a statement and after return or =
              parseEvalProgramHelper (shape ++ "s = Shape::Rect { width: 3, height: 4 }; total = 0; match s { Shape::Circle { radius: r } => { total = r; }, Shape::Rect { width: w, height: h } => { total = w * h; }, Shape::Empty => { }, }; return total;") (Just (VInt 12))
            , parseEvalProgramHelper (shape ++ "s = Shape::Circle { radius: 3 }; a = 0; a = match s { Shape::Circle { radius: r } => r * 2, Shape::Rect { width: w } => w, Shape::Empty => 0 }; return a;") (Just (VInt 6))
            , parseEvalProgramHelper (shape ++ "fn area(s: Shape) -> Int { return match s { Shape::Circle { radius: r } => r * r * 3, Shape::Rect { width: w, height: h } => w * h, Shape::Empty => 0 }; }; return area(Shape::Rect { width: 2, height: 5 });") (Just (VInt 10))
            , parseEvalProgramHelper (opt ++ "o = Opt::Some { value: 4 }; return match o { Opt::None => 0, Opt::Some { value: v } => v };") (Just (VInt 4))
            , -- A struct can be matched as the only variant of its type
              parseEvalProgramHelper "struct P { x: Int, y: Int }; p = P { x: 1, y: 2 }; return match p { P { y: b } => b };" (Just (VInt 2))
            , -- Recursive types
              parseEvalProgramHelper (tree ++ "fn sum(t: Tree) -> Int shrinks t { return match t { Tree::Leaf => 0, Tree::Branch { left: l, value: v, right: r } => v + sum(l) + sum(r) }; }; return sum(Tree::Branch { left: Tree::Branch { left: Tree::Leaf, value: 1, right: Tree::Leaf }, value: 2, right: Tree::Leaf });") (Just (VInt 3))
            , -- Parse errors
              parseFailsWith (shape ++ "s = Shape::Empty; match s { Shape::Empty => { } };") "does not cover Shape::Circle Shape::Rect"
            , parseFailsWith (shape ++ "s = Shape::Empty; match s { Shape::Empty => { }, Shape::Empty => { }, Shape::Circle { radius: r } => { }, Shape::Rect { width: w } => { } };") "repeats a variant"
            , parseFailsWith (shape ++ opt ++ "s = Shape::Empty; match s { Shape::Empty => { }, Opt::None => { } };") "arm of another type"
            , parseFailsWith (shape ++ "s = Shape::Empty; match s { Shape::Nope => { } };") "Unknown struct or variant Shape::Nope"
            , parseFailsWith (shape ++ "s = Shape::Circle { radius: 1 }; match s { Shape::Circle { diameter: d } => { }, Shape::Rect { width: w } => { }, Shape::Empty => { } };") "has no field diameter"
            , parseFailsWith (shape ++ "x = Shape::Circle { };") "lacks field radius"
            , parseFailsWith (shape ++ "x = Shape::Circle { radius: 1, ..y };") "copies nothing"
            , parseFailsWith (shape ++ "x = Shape::Empty is Shape::Nope;") "unexpected"
            , parseFailsWith "enum E { };" "has no variants"
            , parseFailsWith "enum E { A, A };" "repeats a variant"
            , parseFailsWith "enum Bool { A };" "builtin type"
            , -- Type checking
              parseValidateFailProgramHelper (shape ++ "x = Shape::Circle { radius: true };") "field radius of Shape::Circle: expected Int, got Bool"
            , parseValidateFailProgramHelper (shape ++ "fn f(s: Shape) -> Int { return s.radius; };") "cast the value to a variant first"
            , parseValidateFailProgramHelper (shape ++ opt ++ "x = Shape::Empty = Opt::None;") "expected Shape, got Opt"
            , parseValidateFailProgramHelper (shape ++ "x = 1 is Shape::Empty;") "expected Shape, got Int"
            , parseValidateFailProgramHelper (shape ++ shape) "Type already defined: Shape"
            , parseValidateFailProgramHelper (shape ++ "fn f(s: Shape) -> Bool { return s; };") "returned value: expected Bool, got Shape"
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Empty; match s { Shape::Circle { radius: r } => { x = r + true; }, Shape::Rect { width: w } => { }, Shape::Empty => { } };") "expected Int, got Bool"
            , -- Validation: the value's variant is known from where it was built
              parseValidProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s is Shape::Circle;")
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s is Shape::Rect;") "Could not prove: s is Shape::Rect"
            , parseValidProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s != Shape::Empty; affirm s != Shape::Circle { radius: 5 };")
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; affirm s != Shape::Circle { radius: 4 };") "Could not prove: s != Shape::Circle { radius: 4 }"
            , -- Only the arm of the known variant runs, so the join keeps its facts
              parseValidProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; total = 0; match s { Shape::Circle { radius: r } => { total = r; }, Shape::Rect { width: w, height: h } => { total = w; }, Shape::Empty => { } }; affirm total = 4;")
            , parseValidProgramHelper (shape ++ "s = Shape::Rect { width: 3, height: 5 }; total = 0; total = match s { Shape::Circle { radius: r } => r, Shape::Rect { width: w, height: h } => w + h, Shape::Empty => 0 }; affirm total = 8;")
            , parseValidateFailProgramHelper (shape ++ "s = Shape::Circle { radius: 4 }; total = 0; match s { Shape::Circle { radius: r } => { total = r; }, Shape::Rect { width: w, height: h } => { total = w; }, Shape::Empty => { } }; affirm total = 5;") "Could not prove: total = 5"
            , -- An unknown value: each arm is checked, and the arms' bindings are fields of the variant
              parseValidProgramHelper (shape ++ "fn area(s: Shape) -> Int [{ }] [{ }] { return match s { Shape::Circle { radius: r } => r, Shape::Rect { width: w, height: h } => w * h, Shape::Empty => 0 }; };")
            , parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ }] [{ affirm return = 1; }] { return match o { Opt::None => 1, Opt::Some { value: v } => 1 }; };")
            , parseValidateFailProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ }] [{ affirm return = 1; }] { return match o { Opt::None => 1, Opt::Some { value: v } => v }; };") "Could not prove: return = 1"
            , parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ affirm return = 7; }] { return match o { Opt::None => 1, Opt::Some { value: v } => 7 }; };")
            , parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ affirm o is Opt::None; }] [{ affirm return = 1; }] { return match o { Opt::None => 1, Opt::Some { value: v } => v }; };")
            , -- Contracts naming a variant
              parseValidProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; x = needsSome(Opt::Some { value: 2 });")
            , parseValidateFailProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; x = needsSome(Opt::None);") "Could not prove: o is Opt::Some"
            , parseValidateFailProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; fn caller(o: Opt) -> Int [{ }] [{ }] { return needsSome(o); };") "Could not prove: o is Opt::Some"
            , parseValidProgramHelper (opt ++ "fn needsSome(o: Opt) -> Int [{ affirm o is Opt::Some; }] [{ }] { return 1; }; fn caller(o: Opt) -> Int [{ }] [{ }] { if o is Opt::Some { return needsSome(o); } else { return 0; }; };")
            , -- Two variants of one value cannot both hold
              parseValidProgramHelper (opt ++ "fn f(o: Opt) -> Int [{ affirm o is Opt::None; affirm o is Opt::Some; }] [{ affirm return = 9; }] { return 1; };")
            , -- What an arm binds or first assigns is local to the arm, whatever the number of variants
              parseValidateFailProgramHelper "struct P { x: Int }; p = P { x: 1 }; match p { P { x: a } => { local = a; } }; return local;" "Undefined variable: local"
            , parseEvalProgramFailHelper "struct P { x: Int }; p = P { x: 1 }; match p { P { x: a } => { local = a; } }; return local;" "Undefined variable: local"
            , parseValidateFailProgramHelper (opt ++ "o = Opt::None; match o { Opt::None => { local = 1; }, Opt::Some { value: v } => { local = v; } }; return local;") "Undefined variable: local"
            , parseValidateFailProgramHelper (opt ++ "o = Opt::None; match o { Opt::None => { }, Opt::Some { value: v } => { } }; return v;") "Undefined variable: v"
            , -- A pattern variable hides a variable of the same name instead of assigning it
              parseEvalProgramHelper (opt ++ "v = 99; o = Opt::Some { value: 4 }; match o { Opt::None => { }, Opt::Some { value: v } => { w = v; } }; return v;") (Just (VInt 99))
            , parseValidProgramHelper (opt ++ "v = 99; o = Opt::Some { value: 4 }; match o { Opt::None => { }, Opt::Some { value: v } => { w = v; } }; affirm v = 99;")
            , parseEvalProgramHelper "struct P { x: Int }; v = 99; p = P { x: 4 }; match p { P { x: v } => { } }; return v;" (Just (VInt 99))
            , parseValidProgramHelper (opt ++ "v = true; o = Opt::Some { value: 4 }; match o { Opt::None => { }, Opt::Some { value: v } => { w = v + 1; } }; affirm v = true;")
            , -- The scrutinee is read once, so a pattern variable named like it does not change later fields
              parseEvalProgramHelper (shape ++ "r = Shape::Rect { width: 3, height: 4 }; t = 0; match r { Shape::Circle { radius: x } => { }, Shape::Rect { width: r, height: h } => { t = r * 10 + h; }, Shape::Empty => { } }; return t;") (Just (VInt 34))
            , parseValidProgramHelper (shape ++ "r = Shape::Rect { width: 3, height: 4 }; t = 0; match r { Shape::Circle { radius: x } => { }, Shape::Rect { width: r, height: h } => { t = r * 10 + h; }, Shape::Empty => { } }; affirm t = 34;")
            , -- Enums in lists
              parseValidProgramHelper (opt ++ "l = push(push([], Opt::None), Opt::Some { value: 2 }); affirm get(l, 0) is Opt::None; affirm size(l) = 2;")
            , -- Recursive types
              parseValidProgramHelper (tree ++ "fn sum(t: Tree) -> Int [{ }] [{ }] shrinks t { return match t { Tree::Leaf => 0, Tree::Branch { left: l, value: v, right: r } => v + sum(l) + sum(r) }; }; x = sum(Tree::Leaf);")
            ]

testEnumCast :: Test
testEnumCast =
    let shape = "enum Shape { Circle { radius: Int }, Rect { width: Int, height: Int }, Empty };"
     in testCaseSeq
            "testEnumCast"
            [ -- Casting to a variant lets its fields be read, and is checked by the validator
              parseEvalProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; return (c as Shape::Circle).radius;") (Just (VInt 5))
            , parseEvalProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; return c as Shape::Circle;") (Just (VData "Shape::Circle" [("radius", VInt 5)]))
            , parseValidProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; affirm (c as Shape::Circle).radius = 5;")
            , parseValidProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ affirm s is Shape::Circle; }] [{ affirm return = (s as Shape::Circle).radius; }] { return (s as Shape::Circle).radius; };")
            , parseValidProgramHelper (shape ++ "fn area(s: Shape) -> Int [{ }] [{ }] { if s is Shape::Rect { return (s as Shape::Rect).width * (s as Shape::Rect).height; } else { return 0; }; };")
            , parseEvalProgramHelper (shape ++ "fn area(s: Shape) -> Int { if s is Shape::Rect { return (s as Shape::Rect).width * (s as Shape::Rect).height; } else { return 0; }; }; return area(Shape::Rect { width: 3, height: 4 });") (Just (VInt 12))
            , -- The cast without a proof is rejected
              parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ }] [{ }] { return (s as Shape::Circle).radius; };") "Could not prove: value is Shape::Circle"
            , parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ affirm s is Shape::Rect; }] [{ }] { return (s as Shape::Circle).radius; };") "Could not prove: value is Shape::Circle"
            , parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int [{ }] [{ }] { if s is Shape::Circle { return 0; } else { return (s as Shape::Circle).radius; }; };") "Could not prove: value is Shape::Circle"
            , parseValidateFailProgramHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; k = r as Shape::Circle;") "Could not prove: value is Shape::Circle"
            , -- Running a wrong cast is undefined behaviour: the executor does not check it, and reading what is not there is an error
              parseEvalProgramHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; k = r as Shape::Circle; return 1;") (Just (VInt 1))
            , parseEvalProgramFailHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; return (r as Shape::Circle).radius;") "Expected a Shape::Circle but got a Shape::Rect"
            , -- A field of an enum is not read without a cast, whichever variants have it
              parseValidateFailProgramHelper (shape ++ "fn r(s: Shape) -> Int { return s.radius; };") "cast the value to a variant first"
            , parseValidateFailProgramHelper ("enum E { A { size: Int }, B { size: Int } };" ++ "fn f(e: E) -> Int { return e.size; };") "cast the value to a variant first"
            , parseValidProgramHelper ("enum E { A { size: Int }, B { size: Int } };" ++ "fn f(e: E) -> Int [{ affirm e is E::B; }] [{ }] { return (e as E::B).size; };")
            , -- The variant's fields are checked, and the cast value is still a value of the enum
              parseValidateFailProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; k = (c as Shape::Circle).width;") "Shape::Circle has no field width"
            , parseValidateFailProgramHelper (shape ++ "c = Shape::Circle { radius: 5 }; b = (c as Shape::Circle).radius = true;") "expected Int, got Bool"
            , parseValidateFailProgramHelper (shape ++ "x = 1; y = x as Shape::Circle;") "expected Shape, got Int"
            , parseValidProgramHelper (shape ++ "fn id(s: Shape) -> Shape { return s; }; c = Shape::Circle { radius: 5 }; d = id(c as Shape::Circle);")
            , parseValidProgramHelper (shape ++ "fn r(c: Shape::Circle) -> Int { return c.radius; }; fn use(s: Shape) -> Int [{ affirm s is Shape::Circle; }] [{ }] { return r(s as Shape::Circle); }; x = use(Shape::Circle { radius: 9 });")
            , parseValidateFailProgramHelper (shape ++ "fn r(c: Shape::Circle) -> Int { return c.radius; }; x = r(Shape::Rect { width: 1, height: 2 });") "expected Shape::Circle, got Shape"
            , -- Updating a variant copies the fields it does not name from the base cast to that variant
              parseValidProgramHelper (shape ++ "fn grow(s: Shape) -> Shape [{ affirm s is Shape::Rect; }] [{ affirm return is Shape::Rect; affirm (return as Shape::Rect).height = (s as Shape::Rect).height; affirm (return as Shape::Rect).width = 10; }] { return Shape::Rect { width: 10, ..s }; };")
            , parseValidateFailProgramHelper (shape ++ "fn grow(s: Shape) -> Shape [{ }] [{ }] { return Shape::Rect { width: 10, ..s }; };") "Could not prove: value is Shape::Rect"
            , parseValidateFailProgramHelper (shape ++ "fn grow(s: Shape) -> Shape [{ affirm s is Shape::Rect; }] [{ affirm (return as Shape::Rect).height = 5; }] { return Shape::Rect { width: 10, ..s }; };") "Could not prove: (return as Shape::Rect).height = 5"
            , parseEvalProgramHelper (shape ++ "r = Shape::Rect { width: 1, height: 2 }; return Shape::Rect { width: 7, ..r };") (Just (VData "Shape::Rect" [("width", VInt 7), ("height", VInt 2)]))
            , -- Structs read their fields directly
              parseEvalProgramHelper ("struct P { radius: Int };" ++ shape ++ "p = P { radius: 4 }; return p.radius;") (Just (VInt 4))
            ]
