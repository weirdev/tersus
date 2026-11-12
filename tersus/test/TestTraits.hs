module TestTraits (testTraits) where

import MirEval (fromMirValue)
import Compile (lowerSource)
import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Mir as M
import Pipeline (parseSource, parseWithEquality, runStatements, validateStatements)
import Types
import Syntax
import Solver
import TestHarness
import Utils

-- Traits and impls: the functions of a type, how they are called, and what an impl has to meet
testTraits :: Test
testTraits =
    let types =
            unlines
                [ "trait Clone { fn clone(self: &Self) -> Self [{ }] [{ affirm return = self; }]; }; trait Copy { };"
                , "enum Shape { Circle { radius: Int }, Rect { width: Int, height: Int }, Empty };"
                , "struct Counter { value: Int };"
                , "impl Clone for Shape { }; impl Copy for Shape { };"
                , "impl Clone for Counter { }; impl Copy for Counter { };"
                ]
        runs body expected = parseEvalProgramHelper (types ++ body) (Just (VInt expected))
        valid body = parseValidProgramHelper (types ++ body)
        rejected body expected = parseValidateFailProgramHelper (types ++ body) expected
        parseFails source = case parseValidProgramHelper source of
            Just err | take 11 err == "Parse faile" -> Nothing
            _ -> Just ("Expected a parse error for: " ++ source)
        conflict =
            unlines
                [ "trait Name { fn label(self: Self) -> Int; fn make() -> Self; };"
                , "trait Code { fn label(self: Self) -> Int; fn make() -> Self; };"
                , "impl Name for Counter { fn label(self: Self) -> Int { return 1; }; fn make() -> Self { return Self { value: 10 }; }; };"
                , "impl Code for Counter { fn label(self: Self) -> Int { return 2; }; fn make() -> Self { return Self { value: 20 }; }; };"
                , "impl Counter { fn label(self: Self) -> Int { return 3; }; };"
                ]
        -- (the prelude is put in front of a program by the pipeline, so these programs are read as the command line reads them)
        runsLib source expected = case parseSource source of
            Error e -> Just ("Parse failed: " ++ e)
            Ok stmts -> case runStatements stmts of
                Ok result -> testAssertEq (fmap fromMirValue result) (Just (VInt expected))
                Error e -> Just ("Evaluation failed with error: " ++ e)
        validLib source = case parseSource source of
            Error e -> Just ("Parse failed: " ++ e)
            Ok stmts -> case validateStatements stmts of
                Ok _ -> Nothing
                Error e -> Just ("Validation failed with error: " ++ e)
        measure =
            unlines
                [ "trait Measure { fn sides(self: Self) -> Int [{ }] [{ affirm return >= 0; }]; };"
                , "impl Measure for Shape {"
                , "    fn sides(self: Self) -> Int [{ }] [{ affirm return >= 0; }] {"
                , "        return match self { Self::Circle { radius: r } => 1, Self::Rect { width: w, height: h } => 4, Self::Empty => 0 };"
                , "    };"
                , "};"
                ]
        traitCheckerCases =
            [ ("lacks a function", "trait Step { fn a() -> Int; fn b() -> Int; }; impl Step for Counter { fn a() -> Int { return 1; }; };", "impl Step for Counter lacks the function b")
            , ("has an extra function", "trait Step { fn a() -> Int; }; impl Step for Counter { fn a() -> Int { return 1; }; fn b() -> Int { return 2; }; };", "has a function b, which Step does not declare")
            , ("wrong parameter type", "trait Step { fn a(self: Self) -> Int; }; impl Step for Counter { fn a(self: Shape) -> Int { return 1; }; };", "a is fn(Shape) -> Int, but Step declares fn(Counter) -> Int")
            , ("wrong result type", "trait Step { fn a() -> Self; }; impl Step for Counter { fn a() -> Int { return 1; }; };", "a is fn() -> Int, but Step declares fn() -> Counter")
            , ("unknown trait", "impl Missing for Counter { };", "unknown trait Missing")
            , ("implemented twice", "trait Step { }; impl Step for Counter { }; impl Step for Counter { };", "Counter already implements Step")
            , ("two functions of one name", "impl Counter { fn a() -> Int { return 1; }; }; impl Counter { fn a() -> Int { return 2; }; };", "does not model yet: two functions with one name")
            , ("a type does not implement the trait", (measure ++ "return Measure::sides(Counter { value: 1 });"), "Counter does not implement Measure")
            , ("no function of the type", "x = Counter { value: 1 }.nothing();", "Counter::nothing is not defined before this call")
            , ("a function of the type is defined later", "c = Counter { value: 1 }; x = c.later(); impl Counter { fn later(self: Self) -> Int { return 1; }; };", "Counter::later is not defined before this call")
            , ("wrong argument", "impl Counter { fn plus(self: Self, by: Int) -> Int { return by; }; }; x = Counter { value: 1 }.plus(true);", "argument 2 of <Counter>::plus: expected Int, got Bool")
            , ("wrong number of arguments", "impl Counter { fn plus(self: Self, by: Int) -> Int { return by; }; }; x = Counter { value: 1 }.plus();", "<Counter>::plus takes 2 arguments, got 1")
            , ("a method of an integer", "x = 5; y = x.double();", "Int::double is not defined before this call")
            , ("a trait function with no Self parameter, through the trait", "trait Make { fn make() -> Self; }; impl Make for Counter { fn make() -> Self { return Self { value: 0 }; }; }; c = Make::make();", "has no Self parameter to tell the type by")
            , ("a function the trait lacks", "trait Make { }; x = Make::nothing(Counter { value: 1 });", "trait Make has no function nothing")
            , ("a trait cannot read a field of Self", "trait Step { fn a(self: Self) -> Int [{ affirm self.value > 0; }]; };", "a trait does not know the fields of Self")
            , ("a type error in a trait is found at the trait", "trait Step { fn a(n: Int) -> Int [{ affirm n < true; }]; };", "expected Int, got Bool")
            , ("a trait named like a type", "struct Same { a: Int }; trait Same { };", "Same is already defined")
            , ("a trait is defined once", "trait T { }; trait T { };", "T is already defined")
            , ("a trait inside a function", "fn f() -> Int { trait T { }; return 1; }; x = f();", "a trait can only be defined at the top")
            , ("an impl inside a function", "fn f() -> Int { impl Counter { }; return 1; }; x = f();", "an impl can only be written at the top")
            ]
        traitParseCases =
            [ ("an impl needs a declared type", "impl Nothing { };")
            , ("a variant cannot also be a function", "enum E { A, B }; impl E { fn A() -> Int { return 1; }; };")
            , ("Self is not a type name", "struct Self { a: Int };")
            , ("Self is not an enum name", "enum Self { A };")
            , ("Self is not a trait name", "trait Self { };")
            , ("a trait function has no body", "trait T { fn a() -> Int { return 1; }; };")
            , ("a trait repeats a function", "trait T { fn a() -> Int; fn a() -> Int; };")
            , ("an impl is ended with a semicolon", "struct S { a: Int }; impl S { } x = 1;")
            ]
        showSize = "trait Show { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; trait Size { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; impl Show for Cell { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; impl Size for Cell { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 2; }; }; "
        bounded body expected = parseEvalProgramHelper (showSize ++ body) (Just (VInt expected))
        -- (refused in the program's words: an internal compiler error of a copy is not the refusal asked for)
        boundedRejected body expected = case parseWithEquality (showSize ++ body) of
            Left err -> Just ("Parse failed: " ++ err)
            Right stmts -> case validateStatements stmts of
                Error e | "internal compiler error" `isInfixOf` e -> Just ("an internal compiler error instead of a refusal: " ++ e)
                _ -> parseValidateFailProgramHelper (showSize ++ body) expected
        compiledRejected source expected = case lowerSource True source of
            Ok _ -> Just ("accepted: " ++ source)
            Error e -> if take (length expected) e == expected then Nothing else Just ("expected an error starting " ++ show expected ++ ", got: " ++ e)
        rejectedBoth body firstExpected secondExpected = case (rejected body firstExpected, rejected body secondExpected) of
            (Nothing, Nothing) -> Nothing
            (Just err, _) -> Just err
            (_, Just err) -> Just err
     in TestList
            "testTraits"
            [ TestList
                "calls"
                [ -- A function of a type, called by the type's name; Self is the type in the impl
                  testCase "associated function" (runs "impl Counter { fn new(v: Int) -> Self { return Self { value: v }; }; }; return Counter::new(4).value;" 4)
                , testCase "Self in a signature and a body" (runs "impl Shape { fn unit() -> Self { return Self::Rect { width: 1, height: 1 }; }; }; s = Shape::unit(); return (s as Shape::Rect).width;" 1)
                , -- The same function called on a value
                  testCase "method call" (runs (measure ++ "return Shape::Empty.sides() + Shape::Rect { width: 1, height: 2 }.sides();") 4)
                , testCase "method call with arguments" (runs "impl Counter { fn plus(self: Self, by: Int) -> Self { return Self { value: self.value + by }; }; }; c = Counter { value: 1 }; return c.plus(2).plus(3).value;" 6)
                , testCase "the receiver is an expression" (runs "impl Counter { fn plus(self: Self, by: Int) -> Self { return Self { value: self.value + by }; }; }; c = Counter { value: 1 }; return (Counter { value: 2 }).plus(c.value + 1).value;" 4)
                , testCase "method on a value cast to a variant" (runs (measure ++ "s = Shape::Circle { radius: 2 }; return (s as Shape::Circle).sides();") 1)
                , testCase "called by the type's name" (runs (measure ++ "return Shape::sides(Shape::Empty) + Shape::sides(Shape::Circle { radius: 1 });") 1)
                , -- Through the trait, the argument that is Self decides
                  testCase "through the trait" (runs (measure ++ "return Measure::sides(Shape::Rect { width: 1, height: 1 });") 4)
                , testCase "through the trait, Self not first" (runs "trait Add { fn add(by: Int, to: Self) -> Self; }; impl Add for Counter { fn add(by: Int, to: Self) -> Self { return Self { value: to.value + by }; }; }; return Add::add(3, Counter { value: 4 }).value;" 7)
                , testCase "calls nest" (runs (measure ++ "return Measure::sides(Shape::Empty) + Shape::Rect { width: 1, height: 1 }.sides() + Shape::sides(Shape::Circle { radius: 1 });") 5)
                , testCase "a function calls another of the same impl" (runs "impl Counter { fn one() -> Self { return Self { value: 1 }; }; fn two() -> Self { return Self { value: Counter::one().value + 1 }; }; }; return Counter::two().value;" 2)
                , testCase "a recursive function of an impl" (runs "impl Counter { fn count(self: Self) -> Int [{ affirm self.value >= 0; }] shrinks self.value { if self.value = 0 { return 0; } else { return 1 + Counter { value: self.value - 1 }.count(); }; }; }; return Counter { value: 3 }.count();" 3)
                , testCase "a method in a condition and a loop bound" (runs "impl Counter { fn limit(self: Self) -> Int { return self.value; }; }; c = Counter { value: 3 }; n = 0; if c.limit() > 2 { n = n + 1; }; return n;" 1)
                , testCase "a type may implement several traits" (runs (measure ++ "trait Name { fn id(self: Self) -> Int; }; impl Name for Shape { fn id(self: Self) -> Int { return 7; }; }; s = Shape::Empty; return s.sides() + Name::id(s);") 7)
                , testCase "a function of a trait impl calls an earlier one through the trait" (runs "trait T { fn first(self: Self) -> Int; fn second(self: Self) -> Int; }; impl T for Counter { fn first(self: Self) -> Int { return 4; }; fn second(self: Self) -> Int { return T::first(self) + 1; }; }; return T::second(Counter { value: 0 });" 5)
                , testCase "a trait with no functions" (valid "trait Marker { }; impl Marker for Counter { }; x = 1;")
                ]
            , TestList
                "validation"
                [ -- The contracts of a call are the impl's
                  testCase "contract of the impl at a call" (valid (measure ++ "n = Shape::Empty.sides(); affirm n >= 0;"))
                , testCase "an input contract is demanded at a method call" (rejected "impl Counter { fn from(v: Int) -> Self [{ affirm v >= 0; }] { return Self { value: v }; }; }; c = Counter::from(0 - 1);" "Could not prove: v >= 0")
                , -- An impl may ask for less than the trait and promise more
                  testCase "weaker input, stronger output" (valid "trait Step { fn advance(self: Self, by: Int) -> Self [{ affirm by > 0; }]; }; impl Step for Counter { fn advance(self: Self, by: Int) -> Self [{ affirm by >= 0; }] [{ affirm return.value = self.value + by; }] { return Self { value: self.value + by }; }; };")
                , testCase "the output contract of the impl is known to the caller" (valid "trait Step { fn advance(self: Self, by: Int) -> Self [{ affirm by > 0; }]; }; impl Step for Counter { fn advance(self: Self, by: Int) -> Self [{ affirm by >= 0; }] [{ affirm return.value = self.value + by; }] { return Self { value: self.value + by }; }; }; c = Counter { value: 1 }.advance(2); affirm c.value = 3;")
                , testCase "stronger input" (rejectedBoth "trait Step { fn advance(self: Self, by: Int) -> Self [{ affirm by > 0; }]; }; impl Step for Counter { fn advance(self: Self, by: Int) -> Self [{ affirm by > 5; }] { return Self { value: self.value + by }; }; };" "impl Step for Counter: advance does not meet what Step declares" "could not prove by > 5")
                , testCase "an impl needs the output contract itself, not what its body happens to show" (rejected "trait Measure { fn measure(self: Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Measure for Counter { fn measure(self: Self) -> Int { return 4; }; };" "impl Measure for Counter: measure does not meet what Measure declares: could not prove return >= 0")
                , testCase "weaker output" (rejected "trait Measure { fn measure(self: Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Measure for Counter { fn measure(self: Self) -> Int { return self.value * self.value; }; };" "impl Measure for Counter: measure does not meet what Measure declares: could not prove return >= 0")
                , -- (an impl declared ~ meets the trait as far as partial correctness goes, and a caller sees the ~ of the function it calls)
                  testCase "an impl that may diverge" (valid "trait Run { fn run(n: Int) -> Int; }; impl Run for Counter { fn run(n: Int) -> Int ~ { return n; }; }; x = Counter::run(1);")
                , testCase "a function that calls it has to say so" (rejected "trait Run { fn run(n: Int) -> Int; }; impl Run for Counter { fn run(n: Int) -> Int ~ { return n; }; }; fn go() -> Int { return Counter::run(1); };" "Not guaranteed to terminate")
                ]
            , TestList
                "conflicts"
                [ -- Two impls that define the same name do not clash until a call says only the type's name
                  testCase "the trait picks the function" (runs (conflict ++ "c = Counter { value: 0 }; return Name::label(c) * 100 + Code::label(c) * 10;") 120)
                , testCase "a path names the impl in full" (runs (conflict ++ "c = Counter { value: 0 }; return <Counter as Name>::label(c) + <Counter as Code>::label(c) * 10 + <Counter>::label(c) * 100;") 321)
                , testCase "a function with no Self argument is named in full" (runs (conflict ++ "return <Counter as Name>::make().value + <Counter as Code>::make().value;") 30)
                , testCase "a method call is ambiguous" (rejected (conflict ++ "c = Counter { value: 0 }; x = c.label();") "Counter::label is ambiguous")
                , testCase "a call by the type is ambiguous, and the type's own function is a path too" (rejectedBoth (conflict ++ "x = Counter::label(Counter { value: 0 });") "Counter::label is ambiguous" "<Counter>::label(...)")
                , testCase "the error lists the paths" (rejected (conflict ++ "x = Counter::make();") "<Counter as Name>::make(...) or <Counter as Code>::make(...)")
                , testCase "a trait impl alone is reached by the type's name" (runs "trait Name { fn label(self: Self) -> Int; }; impl Name for Counter { fn label(self: Self) -> Int { return 4; }; }; return Counter { value: 0 }.label() + Counter::label(Counter { value: 0 });" 8)
                , testCase "a function of the type's own impl is not ambiguous without a clash" (runs "impl Counter { fn label(self: Self) -> Int { return 5; }; }; return Counter { value: 0 }.label();" 5)
                , testCase "Self::f is ambiguous in an impl too" (rejected (conflict ++ "impl Counter { fn twice(self: Self) -> Int { return Self::label(self); }; };") "Counter::label is ambiguous")
                , testCase "a full path to a function that is not there" (rejected "x = <Counter as Nothing>::f(1);" "<Counter as Nothing>::f is not defined before this call")
                , testCase "a full path inside the impl's own function" (runs "impl Counter { fn count(self: Self) -> Int [{ affirm self.value >= 0; }] shrinks self.value { if self.value = 0 { return 0; } else { return 1 + <Counter>::count(Self { value: self.value - 1 }); }; }; }; return Counter::count(Counter { value: 3 });" 3)
                , testCase "the impls of a type are checked against their traits as before" (rejected (conflict ++ "impl Name for Counter { };") "Counter already implements Name")
                ]
            , TestList
                "type errors"
                [ TestList "checker diagnostics" [ testCase name (rejected source expected) | (name, source, expected) <- traitCheckerCases ]
                ]
            , TestList
                "parsing"
                [ TestList "parse shape" [ testCase name (parseFails source) | (name, source) <- traitParseCases ]
                , testCase "ordinary names that begin like keywords" (runs "implement = 1; traits = 2; return implement + traits;" 3)
                ]
            , TestList
                "hashing and bounded impls"
                [ testCase "the hash of an Int" (runsLib "return Hash::hash(42);" 569)
                , testCase "the hash of a Bool" (runsLib "return Hash::hash(true) * 10 + Hash::hash(false);" 13547)
                , testCase "the hash of a Byte" (runsLib "return Hash::hash(toByte(65));" 654)
                , testCase "equal strings hash equal" (runsLib "s = \"hello\"; return Hash::hash(s) - Hash::hash(\"hello\");" 0)
                , testCase "different strings hash different" (runsLib "if Hash::hash(\"hello\") = Hash::hash(\"world\") { return 1; }; return 0;" 0)
                , testCase "hashCombine is in range" (validLib "fn f(h: Int, x: Int) -> Int [{ affirm h >= 0; affirm h < 2147483647; }] [{ affirm return >= 0; affirm return < 2147483647; }] { return hashCombine(h, x); }; return f(3, 4);")
                , testCase "an impl for Int" (parseEvalProgramHelper "trait H { fn hash(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl H for Int { fn hash(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self % 10; }; }; return H::hash(42);" (Just (VInt 2)))
                , testCase "a method of an Int from an impl" (parseEvalProgramHelper "impl Int { fn double(self: &Self) -> Int [{ }] [{ }] { return self * 2; }; }; return (5).double();" (Just (VInt 10)))
                , testCase "a bounded impl calls a trait on its type" (runsLib "struct M<K, V> { x: K, y: V }; impl<K: Hash, V> M<K, V> { fn h(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return Hash::hash(self.x); }; }; return M<Int, Int> { x: 42, y: 1 }.h();" 569)
                , testCase "a bounded impl method calls another" (runsLib "struct M<K, V> { x: K, y: V }; impl<K: Hash, V> M<K, V> { fn h(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return Hash::hash(self.x); }; fn h2(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.h() + 1; }; }; return M<Int, Int> { x: 42, y: 1 }.h2();" 570)
                , testCase "the bound is checked at the call" (parseValidateFailProgramHelper "trait H { fn hash(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct M<K, V> { x: K, y: V }; impl<K: H, V> M<K, V> { fn h(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return H::hash(self.x); }; }; return M<Int, Int> { x: 42, y: 1 }.h();" "needs K to implement H")
                , testCase "a bounded trait impl is made for each type" (parseEvalProgramHelper "trait Same { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; struct Pair<T> { a: T, b: T }; impl Same for Cell { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; impl<T: Same> Same for Pair<T> { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return Same::same(self.a, other.a) + Same::same(self.b, other.b); }; }; p = Pair<Cell> { a: Cell { v: 1 }, b: Cell { v: 2 } }; return Same::same(p, p) + p.same(p);" (Just (VInt 4)))
                , testCase "a bounded trait impl calls itself for a part of its type" (parseEvalProgramHelper "trait Same { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; struct Pair<T> { a: T, b: T }; impl Same for Cell { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; impl<T: Same> Same for Pair<T> { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return Same::same(self.a, other.a) + Same::same(self.b, other.b); }; }; r = Pair<Pair<Cell>> { a: Pair<Cell> { a: Cell { v: 1 }, b: Cell { v: 2 } }, b: Pair<Cell> { a: Cell { v: 1 }, b: Cell { v: 2 } } }; return r.same(r);" (Just (VInt 4)))
                , testCase "a type meets the trait only when it meets the bounds" (parseValidateFailProgramHelper "trait Same { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; struct Pair<T> { a: T, b: T }; impl<T: Same> Same for Pair<T> { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return Same::same(self.a, other.a) + Same::same(self.b, other.b); }; }; p = Pair<Cell> { a: Cell { v: 1 }, b: Cell { v: 2 } }; return Same::same(p, p);" "needs T to implement Same, and Cell does not")
                , testCase "a bound of a function is met through a bounded impl" (parseEvalProgramHelper "trait Same { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; struct Pair<T> { a: T, b: T }; impl Same for Cell { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; impl<T: Same> Same for Pair<T> { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return Same::same(self.a, other.a) + Same::same(self.b, other.b); }; }; fn twice<S: Same>(s: &S) -> Int [{ }] [{ affirm return >= 0; }] { return Same::same(s, s) * 2; }; return twice(Pair<Cell> { a: Cell { v: 1 }, b: Cell { v: 2 } });" (Just (VInt 4)))
                , testCase "a bounded trait impl is checked against the trait for each type" (parseValidateFailProgramHelper "trait Same { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; struct Pair<T> { a: T, b: T }; impl Same for Cell { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; impl<T: Same> Same for Pair<T> { fn same(self: &Self, other: &Self) -> Int [{ }] [{ }] { return Same::same(self.a, other.a) - 5; }; }; p = Pair<Cell> { a: Cell { v: 1 }, b: Cell { v: 2 } }; return Same::same(p, p);" "impl Same for Pair: same[Cell] does not meet what Same declares")
                , testCase "a bounded trait impl has the trait's functions" (parseValidateFailProgramHelper "trait Same { fn same(self: &Self, other: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; struct Cell { v: Int }; struct Pair<T> { a: T, b: T }; impl<T: Same> Same for Pair<T> { fn other(self: &Self) -> Int { return 1; }; }; return 0;" "has a function other, which Same does not declare")
                , testCase "a bounded marker impl is refused" (parseValidateFailProgramHelper "trait M { }; trait N { }; struct Pair<T> { a: T, b: T }; impl<T: N> M for Pair<T> { }; return 0;" "the bounds of a marker impl are not supported")
                ]
            , TestList
                "bodies checked against their bounds alone"
                [ testCase "a body that uses what its bounds give" (bounded "fn twice<T: Show>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return x.show() + Show::show(x); }; return twice(Cell { v: 0 });" 2)
                , testCase "a method no bound gives is refused where the function is defined" (boundedRejected "fn m<T: Show>(x: &T) -> Int { return x.measure(); }; return 0;" "m calls measure on a T, and no bound of it has a function measure")
                , testCase "even when each type it is called with has the method" (boundedRejected "fn m<T: Show>(x: &T) -> Int { return x.measure(); }; return m(Cell { v: 0 });" "m calls measure on a T, and no bound of it has a function measure")
                , testCase "a trait call needs the trait as a bound" (boundedRejected "fn m<T: Show>(x: &T) -> Int { return Size::measure(x); }; return m(Cell { v: 0 });" "m calls Size::measure on a T, and its bounds do not say T: Size")
                , testCase "a call of a bounded function is met by the caller's bounds" (bounded "fn m<T: Size>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return x.measure(); }; fn calls<U: Size + Show>(y: &U) -> Int [{ }] [{ affirm return >= 0; }] { return m(y) + y.show(); }; return calls(Cell { v: 0 });" 3)
                , testCase "and refused when the caller's bounds do not give the callee's" (boundedRejected "fn m<T: Size>(x: &T) -> Int { return x.measure(); }; fn calls<U: Show>(y: &U) -> Int { return m(y); }; return calls(Cell { v: 0 });" "m needs T to implement Size, and the bounds of calls do not say U: Size")
                , testCase "a callee's bound is met through a bounded impl" (bounded "struct Pair<T> { a: T, b: T }; impl<T: Show> Show for Pair<T> { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.a.show() + Show::show(self.b); }; }; fn twice<S: Show>(s: &S) -> Int [{ }] [{ affirm return >= 0; }] { return s.show() * 2; }; fn outer<T: Show>(p: &Pair<T>) -> Int [{ }] [{ affirm return >= 0; }] { return twice(p); }; return outer(Pair<Cell> { a: Cell { v: 1 }, b: Cell { v: 2 } });" 4)
                , testCase "a size the caller's bound names is one the callee's bound can name" (bounded "trait Feed<E> { fn feed(self: &Self) -> E; }; struct Item { }; impl Feed<Array<Int, 3>> for Item { fn feed(self: &Self) -> Array<Int, 3> { return #[1, 2, 3]; }; }; fn make<T: Feed<Array<Int, n>>, n>(x: &T, a: &Array<Int, n>) -> Int { return size(a); }; fn outer<U: Feed<Array<Int, m>>, m>(x: &U, a: &Array<Int, m>) -> Int { return make(x, a); }; return outer(Item { }, #[4, 5, 6]);" 3)
                , testCase "a function of a bounded impl is checked against the impl's bounds" (boundedRejected "struct M<K, V> { x: K, y: V }; impl<K: Show, V> M<K, V> { fn h(self: &Self) -> Int { return Size::measure(self.y); }; }; return 0;" "calls Size::measure on a V, and its bounds do not say V: Size")
                , testCase "a function of a bounded trait impl is too" (boundedRejected "struct Pair<T> { a: T, b: T }; impl<T: Show> Size for Pair<T> { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.a.measure(); }; }; return 0;" "calls measure on a T, and no bound of it has a function measure")
                , testCase "a body calls a function defined after it" (bounded "fn f<T: Show>(x: &T) -> Int { return later(1); }; fn user() -> Int { return f(Cell { v: 0 }); }; fn later(n: Int) -> Int { return n; }; return user();" 1)
                , testCase "a bound of several traits meets a callee's bound of one" (bounded "fn f<T: Show>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return x.show(); }; fn g<T: Show + Size>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return f(x) + x.measure(); }; return g(Cell { v: 0 });" 3)
                , testCase "a function of a bounded trait impl returns a reference from self" (parseValidProgramHelper "trait R<E> { fn first(self: &Self) -> &E from self; }; struct W<T> { x: T }; impl<T: Clone> R<T> for W<T> { fn first(self: &Self) -> &T from self { return &self.x; }; }; return 0;")
                , testCase "and its copy is called" (parseEvalProgramHelper "trait R<E> { fn first(self: &Self) -> &E from self; }; struct W<T> { x: T }; impl<T: Clone> R<T> for W<T> { fn first(self: &Self) -> &T from self { return &self.x; }; }; w = W<Int> { x: 3 }; return *w.first();" (Just (VInt 3)))
                , testCase "a bounded trait impl whose trait's contracts call its functions" (parseEvalProgramHelper "trait Seq<E> { fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; fn get(self: &Self, i: Int) -> E [{ affirm i >= 0; affirm i < size(self); }] [{ }]; }; struct Two<T> { a: T, n: Int } invariant [{ affirm n >= 0; }]; impl<T: Clone> Seq<T> for Two<T> { fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; }; fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < size(self); }] [{ }] { return clone(self.a); }; }; return Two<Int> { a: 4, n: 1 }.get(0);" (Just (VInt 4)))
                , testCase "a bounded sequence impl with getRef, called through a bound" (parseEvalProgramHelper "trait Sq<E> { fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; fn get(self: &Self, i: Int) -> E [{ affirm i >= 0; affirm i < size(self); }] [{ }]; fn getRef(self: &Self, i: Int) -> &E from self [{ affirm i >= 0; affirm i < size(self); }] [{ }]; }; struct Two<T> { a: T, b: T }; impl<T: Clone> Sq<T> for Two<T> { fn size(self: &Self) -> Int [{ }] [{ affirm return = 2; }] { return 2; }; fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < size(self); }] [{ }] { if i = 0 { return clone(self.a); }; return clone(self.b); }; fn getRef(self: &Self, i: Int) -> &T from self [{ affirm i >= 0; affirm i < size(self); }] [{ }] { if i = 0 { return &self.a; }; return &self.b; }; }; fn second<S: Sq<E>, E: Clone>(s: &S) -> E [{ affirm size(s) >= 2; }] [{ }] { r = s.getRef(1); return clone(*r); }; t = Two<Int> { a: 4, b: 5 }; return second(t) * 10 + t.get(0) + *t.getRef(1);" (Just (VInt 59)))
                , testCase "a type parameter named like the trait's parameter" (parseEvalProgramHelper "trait Ge<S> { fn ge(self: &Self) -> Int; }; struct C { }; impl Ge<Int> for C { fn ge(self: &Self) -> Int { return 4; }; }; fn f<S: Ge<Int>>(x: &S) -> Int { return x.ge() + Ge::ge(x); }; return f(C { });" (Just (VInt 8)))
                , testCase "and in a function's parameter" (parseEvalProgramHelper "trait Ge<T> { fn ge(self: &Self, t: T) -> Int; }; struct C { }; impl Ge<Int> for C { fn ge(self: &Self, t: Int) -> Int { return t; }; }; fn f<T: Ge<Int>>(x: &T) -> Int { return x.ge(4); }; return f(C { });" (Just (VInt 4)))
                , testCase "and in its result" (parseEvalProgramHelper "trait Ge<T> { fn ge(self: &Self) -> T; }; struct C { }; impl Ge<Int> for C { fn ge(self: &Self) -> Int { return 4; }; }; fn f<T: Ge<E>, E: Clone>(x: &T) -> List<E> { e = x.ge(); return push(push([], clone(e)), e); }; return size(f(C { }));" (Just (VInt 2)))
                , testCase "a function is not a type argument of a bounded function" (boundedRejected "fn g(x: Int) -> Int { return x; }; fn h<U>(x: U) -> Int { return 0; }; fn f<S: Show, T>(s: &S, x: T) -> Int { return h(x); }; return f(Cell { v: 0 }, g);" "the type T of f would be")
                , testCase "nor of a Clone bound's" (boundedRejected "fn g(x: Int) -> Int { return x; }; fn f<T: Clone>(x: T) -> Int { a = array(2, x); return 0; }; return f(g);" "and a type parameter is not a function")
                , testCase "an array too big for a frame in a copy is the call's refusal" (boundedRejected "fn f<T: Clone>(x: T) -> Int { a = array(3000, x); return 0; }; return f(#[1, 2, 3]);" "f cannot be made as f[Array<Int, 3>] for this call:")
                , testCase "a program's own Sequence is a trait like any other" (parseEvalProgramHelper "trait Sequence<E> { fn size(self: &Self) -> Int; }; impl Sequence<Int> for List<Int> { fn size(self: &Self) -> Int { return 99; }; }; fn f<S: Sequence<Int>>(s: &S) -> Int { return size(s); }; return f(push([], 1));" (Just (VInt 99)))
                , testCase "whatever its function's type" (parseEvalProgramHelper "trait Sequence { fn get(self: &Self, i: Int) -> Bool; }; impl Sequence for List<Int> { fn get(self: &Self, i: Int) -> Bool { return true; }; }; fn f<S: Sequence>(s: &S) -> Bool { return get(s, 0); }; if f(push([], 1)) { return 1; }; return 0;" (Just (VInt 1)))
                , testCase "and a program's own Growable" (parseEvalProgramHelper "trait Growable { fn push(self: Self, x: Int) -> Bool; }; impl Growable for List<Int> { fn push(self: Self, x: Int) -> Bool { return true; }; }; fn f<S: Growable>(s: S) -> Bool { return push(s, 3); }; if f(push([], 1)) { return 1; }; return 0;" (Just (VInt 1)))
                , testCase "a reference returned onward by a bound's method" (parseEvalProgramHelper "trait R<E> { fn first(self: &Self) -> &E from self; }; struct W { x: Int }; impl R<Int> for W { fn first(self: &Self) -> &Int from self { return &self.x; }; }; fn pick<T: R<Int>>(x: &T) -> &Int from x { return x.first(); }; w = W { x: 3 }; r = pick(w); return *r;" (Just (VInt 3)))
                , testCase "a function of a bounded impl calls another of it" (bounded "struct Pair<T> { a: T, b: T }; impl<T: Show> Pair<T> { fn both(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.a.show() + self.one(); }; fn one(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.b.show(); }; }; return Pair<Cell> { a: Cell { v: 0 }, b: Cell { v: 0 } }.both();" 2)
                , testCase "and one that is not Copy is moved once, whatever the types a call gives" (parseValidateFailProgramHelper "fn twice<T: Clone>(x: T) -> Int { a = push([], x); b = push(a, x); return size(b); }; return 0;" "Move error: in twice")
                , testCase "a function with bounds that nothing calls has no function in the program" (case lowerSource True "fn unused<T: Eq>(x: T) -> Bool { return x = x; }; return 0;" of
                    Ok p -> case [n | n <- Map.keys (M.progFunctions p), "unused" `isInfixOf` n] of
                        [] -> Nothing
                        names -> Just ("the program has " ++ show names)
                    Error e -> Just e)
                , testCase "a call with a type that holds a permission is refused where it is made" (boundedRejected "struct H { a: Addr<Int>, ghost b: Block<Int> }; trait Mark { }; impl Mark for H { }; fn f<T: Mark>(x: &T) -> Int { return 0; }; fn g(h: &H) -> Int { return f(h); }; return 0;" "the type T of f would be H, which holds a permission, and a type parameter is not one")
                , testCase "clone(x) of a word copies it, whatever the program's own trait Clone says" (parseEvalProgramHelper "trait Clone { fn clone(self: &Self) -> Self; }; impl Clone for Int { fn clone(self: &Self) -> Int { return *self + 1; }; }; fn c<T: Clone>(x: T) -> T { return clone(x); }; return c(5) * 10 + clone(5);" (Just (VInt 55)))
                , testCase "and so does x.clone()" (parseEvalProgramHelper "trait Clone { fn clone(self: &Self) -> Self; }; impl Clone for Int { fn clone(self: &Self) -> Int { return *self + 1; }; }; fn c<T: Clone>(x: T) -> T { return x.clone(); }; y = 5; return c(5) * 10 + y.clone();" (Just (VInt 55)))
                , testCase "and Clone::clone is the impl's, as for the type itself" (parseEvalProgramHelper "trait Clone { fn clone(self: &Self) -> Self; }; impl Clone for Int { fn clone(self: &Self) -> Int { return *self + 1; }; }; fn c<T: Clone>(x: T) -> T { return Clone::clone(x); }; y = 5; return c(5) * 10 + Clone::clone(y);" (Just (VInt 66)))
                , testCase "a Box of an array of no size is cloned by the program's own Clone when the library's is not there" (parseEvalProgramHelper "trait Clone { fn clone(self: &Self) -> Self; }; impl Clone for Box<Array<Int>> { fn clone(self: &Self) -> Box<Array<Int>> { return Array::boxed(1, 9); }; }; fn c<T: Clone>(x: &T) -> T { return x.clone(); }; b = Array::boxed(2, 7); d = c(b); e = b.clone(); return size(d) * 10 + size(e);" (Just (VInt 11)))
                , testCase "a copy with an array of structs too big for a frame is the call's refusal" (parseValidateFailProgramHelper "struct P { a: Int, b: Int, c: Int }; impl Clone for P { }; fn f<T: Clone>(x: T) -> Int { a = array(3000, x); return 0; }; return f(P { a: 1, b: 2, c: 3 });" "f cannot be made as f[P] for this call: Array<P, 3000> takes 9000 words")
                , testCase "and of tuples" (parseValidateFailProgramHelper "fn f<T: Clone>(x: T) -> Int { a = array(3000, (x, 1)); return 0; }; return f(#[1, 2, 3]);" "f cannot be made as f[Array<Int, 3>] for this call")
                , testCase "a copy's refusal is a refusal of the program, as the elaborator's is" (case lowerSource True "fn grow<T: Eq>(x: T, n: Int) -> Int [{ affirm n >= 0; }] [{ }] shrinks n { if n = 0 { return 0; }; return grow(push([], x), n - 1); }; return grow(1, 2);" of
                    Error e | "Validation failed: Type error: grow calls itself" `isPrefixOf` e -> Nothing
                    Error e -> Just e
                    Ok _ -> Just "the program was accepted")
                , testCase "a function written for any type still cannot call a bounded one with its own type" (boundedRejected "fn f<T: Show>(x: &T) -> Int { return x.show(); }; fn h<T>(x: &T) -> Int { return f(x); }; return h(Cell { v: 0 });" "f needs T to implement Show, and T does not")
                , testCase "a function nested in a bounded body does not clone its own type parameter" (boundedRejected "fn f<T: Show>(x: T) -> Int { fn inner<U>(y: U) -> List<U> { return push(push([], clone(y)), y); }; return size(inner(x)); }; return f(Cell { v: 0 });" "inner clones a U, and its bounds do not say U: Clone")
                , testCase "and is not given the bounds of the function it is in" (boundedRejected "fn f<T: Show>(x: &T) -> Int { fn inner<T>(y: &T) -> Int { return y.show(); }; return inner(x); }; return f(Cell { v: 0 });" "show is called on a T, which has no functions")
                , testCase "nor can it call a bounded function with a type of its own" (boundedRejected "fn g<S: Show>(s: &S) -> Int { return s.show(); }; fn f<T: Show>(x: &T) -> Int { fn inner<U>(y: &U) -> Int { return g(y); }; return inner(x); }; return f(Cell { v: 0 });" "g needs S to implement Show, and U does not")
                , testCase "a type named like a type parameter gives it none of its functions" (boundedRejected "struct T { n: Int }; impl Size for T { fn measure(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 5; }; }; fn f<T: Show>(x: &T) -> Int { return x.measure(); }; return f(Cell { v: 0 });" "f calls measure on a T, and no bound of it has a function measure")
                , testCase "nor its Clone" (boundedRejected "struct T { n: Int }; impl Clone for T { }; fn f<T: Show>(x: T) -> List<T> { return push(push([], clone(x)), x); }; return size(f(Cell { v: 0 }));" "f clones a T, and its bounds do not say T: Clone")
                , testCase "the functions a bound gives are not names a program writes" (boundedRejected "fn f<T: Show>(x: &T) -> Int { return Show::show(x) + <T as Show>::show(x); }; return f(Cell { v: 0 });" "<T as Show>::show is not defined before this call")
                , testCase "a copy calls the bound's function when the type has one of its own of that name" (bounded "impl Cell { fn show(self: &Self) -> Bool { return true; }; }; fn f<T: Show>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return x.show(); }; return f(Cell { v: 0 });" 1)
                , testCase "or another trait's" (bounded "trait Disp { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Disp for Cell { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 7; }; }; fn f<T: Show>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return x.show(); }; return f(Cell { v: 0 });" 1)
                , testCase "two type parameters given one type call each its own bound's function" (bounded "trait Disp { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Disp for Cell { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 7; }; }; fn f<A: Show, B: Disp>(a: &A, b: &B) -> Int [{ }] [{ affirm return >= 0; }] { return a.show() + b.show(); }; return f(Cell { v: 0 }, Cell { v: 0 });" 8)
                , testCase "and so do trait paths" (bounded "trait Disp { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Disp for Cell { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 7; }; }; fn f<A: Show, B: Disp>(a: &A, b: &B) -> Int [{ }] [{ affirm return >= 0; }] { return Show::show(a) + Disp::show(b); }; return f(Cell { v: 0 }, Cell { v: 0 });" 8)
                , testCase "a copy calls the bound's function on an array" (parseEvalProgramHelper "trait Show { fn show(self: &Self) -> Int; }; impl Show for Array<Int, 3> { fn show(self: &Self) -> Int { return 1; }; }; fn f<T: Show>(x: &T) -> Int { return x.show(); }; return f(#[1, 2, 3]);" (Just (VInt 1)))
                , testCase "and on a Box" (bounded "impl Show for Box<Cell> { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 3; }; }; fn f<T: Show>(x: &T) -> Int [{ }] [{ affirm return >= 0; }] { return x.show(); }; return f(Box::new(Cell { v: 0 }));" 3)
                , testCase "a bound's size on a list is the trait's, not the builtin" (parseEvalProgramHelper "trait Count { fn size(self: &Self) -> Int; }; impl Count for List<Int> { fn size(self: &Self) -> Int { return 42; }; }; fn f<T: Count>(x: &T) -> Int { return x.size(); }; return f(push([], 7));" (Just (VInt 42)))
                , testCase "even when its type is not the builtin's" (parseEvalProgramHelper "trait Count { fn size(self: &Self) -> Bool; }; impl Count for List<Int> { fn size(self: &Self) -> Bool { return true; }; }; fn f<T: Count>(x: &T) -> Bool { return x.size(); }; if f(push([], 7)) { return 1; }; return 0;" (Just (VInt 1)))
                , testCase "a method two bounds of one parameter have is ambiguous where it is written" (boundedRejected "trait Disp { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Disp for Cell { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 7; }; }; fn f<T: Show + Disp>(x: &T) -> Int { return x.show(); }; return f(Cell { v: 0 });" "show is ambiguous for T, whose bounds give several: write Show::show(...) or Disp::show(...)")
                , testCase "a refusal found before the first copy is an ordinary refusal of the program" (compiledRejected (showSize ++ "struct Plain { v: Int }; impl Show for Plain { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 3; }; }; fn f<T: Show>(x: &T) -> Int { return x.measure(); }; return f(Plain { v: 0 });") "Validation failed: Type error: f calls measure on a T, and no bound of it has a function measure")
                , testCase "and so is one of a function a copy calls" (compiledRejected (showSize ++ "fn g<T: Show>(x: &T) -> Int { return x.measure(); }; fn f<T: Show>(x: &T) -> Int { return g(x); }; return f(Cell { v: 0 });") "Validation failed: Type error: g calls measure on a T, and no bound of it has a function measure")
                , testCase "a copy made before the definition check reports the definition's error" (boundedRejected "struct Plain { v: Int }; impl Show for Plain { fn show(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 3; }; }; fn f<T: Show>(x: &T) -> Int { return x.measure(); }; return f(Plain { v: 0 });" "Type error: f calls measure on a T, and no bound of it has a function measure")
                , testCase "a size in a callee's bound is the caller's" (boundedRejected "trait Feed<E> { fn feed(self: &Self) -> E; }; struct Item { }; impl Feed<Array<Int, 3>> for Item { fn feed(self: &Self) -> Array<Int, 3> { return #[1, 2, 3]; }; }; fn make<T: Feed<Array<Int, n>>, n>(x: &T, a: &Array<Int, n>) -> Int { return size(a); }; fn outer<U: Feed<Array<Int, m>>, m>(x: &U, a: &Array<Int, m>) -> Int { b = #[1, 2, 3, 4]; return make(x, b); }; return outer(Item { }, #[4, 5, 6]);" "make needs T to implement Feed<Array<Int, 4>>, and U implements Feed<Array<Int, m>>")
                , testCase "a body compares a list of a type parameter only with an Eq bound" (boundedRejected "fn f<T: Show>(xs: &List<T>) -> Bool { return xs = xs; }; return 0;" "List<T> is compared with =, which needs it to implement Eq, and T does not")
                , testCase "and != too" (boundedRejected "fn f<T: Show>(a: T, b: T) -> Bool { return a != b; }; return 0;" "T is compared with =, which needs it to implement Eq: bound it, as in <T: Eq>")
                , testCase "array(n, x) of a type parameter asks for a Clone bound" (boundedRejected "fn f<T: Show>(x: T) -> Array<T, 2> { return array(2, x); }; return 0;" "T does not implement Clone: bound it, as in <T: Clone>")
                , testCase "a function of an impl can have bounds of its own, called as a method and by the type's name" (bounded "struct Acc { total: Int }; impl Acc { fn add<T: Size>(self: &Acc, t: &T) -> Acc { return Acc { total: self.total + t.measure() }; }; fn of<T: Size>(t: &T) -> Acc { return Acc { total: t.measure() }; }; fn plain(self: &Acc) -> Int { return self.total; }; }; a = Acc::of(Cell { v: 0 }); b = a.add(Cell { v: 0 }); c = Acc::add(b, Cell { v: 0 }); return c.plain();" 6)
                , testCase "its bounds join the impl's, with self lent, self taken, no self and a nested function" (bounded "struct Pair<T> { a: T, b: T }; impl<T: Show> Pair<T> { fn both(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return self.a.show() + self.b.show(); }; fn with<U: Size>(self: &Self, u: &U) -> Int [{ }] [{ affirm return >= 0; }] { return self.both() + u.measure(); }; fn take<U: Size>(self: Self, u: U) -> Int [{ }] [{ affirm return >= 0; }] { fn inner(x: Int) -> Int [{ affirm x >= 0; }] [{ affirm return >= 0; }] { return x + 1; }; return inner(self.a.show() + u.measure()); }; fn make<U: Size>(a: T, b: T, u: &U) -> Self { return Self { a: a, b: b }; }; }; p = Pair::make(Cell { v: 0 }, Cell { v: 1 }, Cell { v: 2 }); x = p.with(Cell { v: 3 }); y = Pair::with(p, Cell { v: 4 }); z = p.take(Cell { v: 5 }); return x * 100 + y * 10 + z;" 444)
                , testCase "and with self lent for updating" (bounded "struct Counter { n: Int }; impl Counter { fn bump<U: Size>(self: &mut Self, u: &U) -> Int writes(self.n) [{ }] [{ }] { (*self).n = (*self).n + u.measure(); return 0; }; }; c = Counter { n: 1 }; Counter::bump(&mut c, Cell { v: 0 }); Counter::bump(&mut c, Cell { v: 0 }); return c.n;" 5)
                , testCase "a call whose types do not meet a method's own bound is refused" (boundedRejected "struct Plain { v: Int }; struct B { v: Int }; impl B { fn f<U: Size>(self: &Self, u: &U) -> Int { return u.measure(); }; }; b = B { v: 0 }; return b.f(Plain { v: 1 });" "<B>::f needs U to implement Size, and Plain does not")
                , testCase "and one whose types do not meet the impl's" (boundedRejected "struct Plain { v: Int }; struct Pair<T> { a: T, b: T }; impl<T: Show> Pair<T> { fn with<U: Size>(self: &Self, u: &U) -> Int { return u.measure(); }; }; p = Pair<Plain> { a: Plain { v: 0 }, b: Plain { v: 0 } }; return p.with(Cell { v: 0 });" "<Pair>::with needs T to implement Show, and Plain does not")
                , testCase "a method's body is checked against its bounds alone" (boundedRejected "struct B { v: Int }; impl B { fn f<U: Size>(self: &Self, u: &U) -> Int { return u.show(); }; }; return 0;" "<B>::f calls show on a U, and no bound of it has a function show")
                , testCase "and against the impl's, which it is given" (boundedRejected "struct Pair<T> { a: T, b: T }; impl<T: Show> Pair<T> { fn with<U: Size>(self: &Self, u: &U) -> Int { return self.a.measure(); }; }; return 0;" "<Pair>::with calls measure on a T, and no bound of it has a function measure")
                , testCase "and for moves" (boundedRejected "struct B { v: Int }; impl B { fn f<U: Size>(self: &Self, u: U) -> Int { a = push([], u); b = push(a, u); return size(b); }; }; return 0;" "Move error: in <B>::f")
                , testCase "a method's own type parameter does not reuse a name of its impl's" (boundedRejected "struct W<T> { t: T }; impl<T: Show> W<T> { fn f<T: Size>(self: &Self, x: &T) -> Int { return x.measure(); }; }; return 0;" "<W>::f names T twice among its own type and size parameters and its impl's: give one of them another name")
                , testCase "nor does a function with bounds name a parameter twice" (boundedRejected "fn f<T: Size, T: Show>(x: &T) -> Int { return 0; }; return 0;" "f names T twice among its type and size parameters: give one of them another name")
                , testCase "a method with self lent for updating is called with &mut and the place, as any function is" (boundedRejected "struct Counter { n: Int }; impl Counter { fn bump<U: Size>(self: &mut Self, u: &U) -> Int writes(self.n) [{ }] [{ }] { (*self).n = (*self).n + u.measure(); return 0; }; }; c = Counter { n: 1 }; c.bump(Cell { v: 0 }); return c.n;" "an update reference (&mut T) is not lent silently: write &mut and the place, as in &mut x")
                , testCase "and so is one of a bounded impl" (boundedRejected "struct C<T> { n: Int, t: T }; impl<T: Show> C<T> { fn bump(self: &mut Self, u: Int) -> Int writes(self.n) [{ }] [{ }] { (*self).n = (*self).n + u; return 0; }; }; c = C<Cell> { n: 1, t: Cell { v: 0 } }; c.bump(5); return c.n;" "an update reference (&mut T) is not lent silently: write &mut and the place, as in &mut x")
                , testCase "and a read reference is not one for updating" (boundedRejected "struct Counter { n: Int }; impl Counter { fn bump<U: Size>(self: &mut Self, u: &U) -> Int writes(self.n) [{ }] [{ }] { (*self).n = (*self).n + u.measure(); return 0; }; }; c = Counter { n: 1 }; Counter::bump(&c, Cell { v: 0 }); return c.n;" "a read reference (&T) cannot be given where an update reference (&mut T) is wanted")
                , testCase "a function of an impl of a trait has no bounds of its own" (boundedRejected "struct B { v: Int }; impl Show for B { fn show<U: Size>(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; return 0;" "show in impl Show for B has bounds on its types, but a function of an impl of a trait has the types the trait declares")
                , testCase "nor of a bounded impl of a trait" (boundedRejected "struct Pair<T> { a: T, b: T }; impl<T: Show> Show for Pair<T> { fn show<U: Size>(self: &Self) -> Int [{ }] [{ affirm return >= 0; }] { return 1; }; }; return 0;" "show in impl Show for Pair has bounds on its types, but a function of an impl of a trait has the types the trait declares")
                , testCase "a function nested in another has no bounds" (boundedRejected "fn outer(x: Cell) -> Int { fn inner<U: Size>(u: &U) -> Int { return u.measure(); }; return inner(x); }; return 0;" "a function with bounds on its types can only be defined at the top of the program or in an impl of a type, not in a block or a function")
                , testCase "nor one in a block" (boundedRejected "{ fn inner<U: Size>(u: &U) -> Int { return u.measure(); }; }; return 0;" "a function with bounds on its types can only be defined at the top of the program or in an impl of a type, not in a block or a function")
                ]
            ]
