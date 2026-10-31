module TestTraits (testTraits) where

import MirEval (fromMirValue)
import Pipeline (parseSource, runStatements, validateStatements)
import TersusTypes
import TestHarness
import Utils

-- Traits and impls: the functions of a type, how they are called, and what an impl has to meet
testTraits :: Test
testTraits =
    let types =
            unlines
                [ "trait Clone { }; trait Copy { };"
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
                , testCase "stronger input" (rejected "trait Step { fn advance(self: Self, by: Int) -> Self [{ affirm by > 0; }]; }; impl Step for Counter { fn advance(self: Self, by: Int) -> Self [{ affirm by > 5; }] { return Self { value: self.value + by }; }; };" "impl Step for Counter: advance does not meet what Step declares")
                , testCase "stronger input names the contract" (rejected "trait Step { fn advance(self: Self, by: Int) -> Self [{ affirm by > 0; }]; }; impl Step for Counter { fn advance(self: Self, by: Int) -> Self [{ affirm by > 5; }] { return Self { value: self.value + by }; }; };" "Could not prove: by > 5")
                , testCase "an impl needs the output contract itself, not what its body happens to show" (rejected "trait Measure { fn measure(self: Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Measure for Counter { fn measure(self: Self) -> Int { return 4; }; };" "Could not prove: return >= 0")
                , testCase "weaker output" (rejected "trait Measure { fn measure(self: Self) -> Int [{ }] [{ affirm return >= 0; }]; }; impl Measure for Counter { fn measure(self: Self) -> Int { return self.value * self.value; }; };" "Could not prove: return >= 0")
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
                , testCase "a call by the type is ambiguous" (rejected (conflict ++ "x = Counter::label(Counter { value: 0 });") "Counter::label is ambiguous")
                , testCase "the error lists the paths" (rejected (conflict ++ "x = Counter::make();") "<Counter as Name>::make(...) or <Counter as Code>::make(...)")
                , testCase "the type's own function is a path too" (rejected (conflict ++ "x = Counter::label(Counter { value: 0 });") "<Counter>::label(...)")
                , testCase "a trait impl alone is reached by the type's name" (runs "trait Name { fn label(self: Self) -> Int; }; impl Name for Counter { fn label(self: Self) -> Int { return 4; }; }; return Counter { value: 0 }.label() + Counter::label(Counter { value: 0 });" 8)
                , testCase "a function of the type's own impl is not ambiguous without a clash" (runs "impl Counter { fn label(self: Self) -> Int { return 5; }; }; return Counter { value: 0 }.label();" 5)
                , testCase "Self::f is ambiguous in an impl too" (rejected (conflict ++ "impl Counter { fn twice(self: Self) -> Int { return Self::label(self); }; };") "Counter::label is ambiguous")
                , testCase "a full path to a function that is not there" (rejected "x = <Counter as Nothing>::f(1);" "<Counter as Nothing>::f is not defined before this call")
                , testCase "a full path inside the impl's own function" (runs "impl Counter { fn count(self: Self) -> Int [{ affirm self.value >= 0; }] shrinks self.value { if self.value = 0 { return 0; } else { return 1 + <Counter>::count(Self { value: self.value - 1 }); }; }; }; return Counter::count(Counter { value: 3 });" 3)
                , testCase "the impls of a type are checked against their traits as before" (rejected (conflict ++ "impl Name for Counter { };") "Counter already implements Name")
                ]
            , TestList
                "type errors"
                [ testCase "lacks a function" (rejected "trait Step { fn a() -> Int; fn b() -> Int; }; impl Step for Counter { fn a() -> Int { return 1; }; };" "impl Step for Counter lacks the function b")
                , testCase "has an extra function" (rejected "trait Step { fn a() -> Int; }; impl Step for Counter { fn a() -> Int { return 1; }; fn b() -> Int { return 2; }; };" "has a function b, which Step does not declare")
                , testCase "wrong parameter type" (rejected "trait Step { fn a(self: Self) -> Int; }; impl Step for Counter { fn a(self: Shape) -> Int { return 1; }; };" "a is fn(Shape) -> Int, but Step declares fn(Counter) -> Int")
                , testCase "wrong result type" (rejected "trait Step { fn a() -> Self; }; impl Step for Counter { fn a() -> Int { return 1; }; };" "a is fn() -> Int, but Step declares fn() -> Counter")
                , testCase "unknown trait" (rejected "impl Missing for Counter { };" "unknown trait Missing")
                , testCase "implemented twice" (rejected "trait Step { }; impl Step for Counter { }; impl Step for Counter { };" "Counter already implements Step")
                , testCase "two functions of one name" (rejected "impl Counter { fn a() -> Int { return 1; }; }; impl Counter { fn a() -> Int { return 2; }; };" "Function already defined: <Counter>::a")
                , testCase "a type does not implement the trait" (rejected (measure ++ "return Measure::sides(Counter { value: 1 });") "Counter does not implement Measure")
                , testCase "no function of the type" (rejected "x = Counter { value: 1 }.nothing();" "Counter::nothing is not defined before this call")
                , testCase "a function of the type is defined later" (rejected "c = Counter { value: 1 }; x = c.later(); impl Counter { fn later(self: Self) -> Int { return 1; }; };" "Counter::later is not defined before this call")
                , testCase "wrong argument" (rejected "impl Counter { fn plus(self: Self, by: Int) -> Int { return by; }; }; x = Counter { value: 1 }.plus(true);" "argument 2 of <Counter>::plus: expected Int, got Bool")
                , testCase "wrong number of arguments" (rejected "impl Counter { fn plus(self: Self, by: Int) -> Int { return by; }; }; x = Counter { value: 1 }.plus();" "<Counter>::plus takes 2 arguments, got 1")
                , testCase "a method of an integer" (rejected "x = 5; y = x.double();" "Int::double is not defined before this call")
                , testCase "a trait function with no Self parameter, through the trait" (rejected "trait Make { fn make() -> Self; }; impl Make for Counter { fn make() -> Self { return Self { value: 0 }; }; }; c = Make::make();" "has no Self parameter to tell the type by")
                , testCase "a function the trait lacks" (rejected "trait Make { }; x = Make::nothing(Counter { value: 1 });" "trait Make has no function nothing")
                , testCase "a trait cannot read a field of Self" (rejected "trait Step { fn a(self: Self) -> Int [{ affirm self.value > 0; }]; };" "a trait does not know the fields of Self")
                , testCase "a type error in a trait is found at the trait" (rejected "trait Step { fn a(n: Int) -> Int [{ affirm n < true; }]; };" "expected Int, got Bool")
                , testCase "a trait named like a type" (rejected "struct Same { a: Int }; trait Same { };" "Same is already defined")
                , testCase "a trait is defined once" (rejected "trait T { }; trait T { };" "T is already defined")
                , testCase "a trait inside a function" (rejected "fn f() -> Int { trait T { }; return 1; }; x = f();" "a trait can only be defined at the top")
                , testCase "an impl inside a function" (rejected "fn f() -> Int { impl Counter { }; return 1; }; x = f();" "an impl can only be written at the top")
                ]
            , TestList
                "parsing"
                [ testCase "an impl needs a declared type" (parseFails "impl Nothing { };")
                , testCase "a variant cannot also be a function" (parseFails "enum E { A, B }; impl E { fn A() -> Int { return 1; }; };")
                , testCase "Self is not a type name" (parseFails "struct Self { a: Int };")
                , testCase "Self is not an enum name" (parseFails "enum Self { A };")
                , testCase "Self is not a trait name" (parseFails "trait Self { };")
                , testCase "a trait function has no body" (parseFails "trait T { fn a() -> Int { return 1; }; };")
                , testCase "a trait repeats a function" (parseFails "trait T { fn a() -> Int; fn a() -> Int; };")
                , testCase "an impl is ended with a semicolon" (parseFails "struct S { a: Int }; impl S { } x = 1;")
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
                , testCase "bounds on a trait impl are refused" (parseValidateFailProgramHelper "trait H { fn hash(self: &Self) -> Int [{ }] [{ affirm return >= 0; }]; }; trait G { fn g(self: &Self) -> Int; }; struct M<K, V> { x: K, y: V }; impl<K: H, V> G for M<K, V> { fn g(self: &Self) -> Int { return 1; }; }; return 0;" "bounds on an impl of a trait are not yet supported")
                ]
            ]
