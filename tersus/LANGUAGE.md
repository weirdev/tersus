# Tersus Language Guide

Tersus is a small imperative language for writing ordinary computations next to proof and validation statements. The current implementation supports integers, booleans, lists, user-defined functions, nested blocks, and a proof validator built around an internal proof engine for equality, simple rewrites, and builtin function contracts.

This guide describes the Haskell implementation in this package. Runnable programs that demonstrate the features below are in [`examples/`](examples/README.md).

## Program Shape

A program is a block of statements separated by semicolons. The final semicolon is optional, and repeated semicolons are accepted.

```tersus
x = [3, 6, 9, 12];
y = size(x);
affirm y = 4;
```

Whitespace can be spaces, tabs, or newlines. Identifiers must start with a letter and may contain letters and digits.

## Comments

`//` starts a comment that runs to the end of the line. Comments are treated as whitespace, so they can appear anywhere whitespace can, including inside contracts and lists.

```tersus
// Whole-line comment
x = 5; // trailing comment
```

There are no block comments.

## Running Programs

From the `tersus/` directory:

```
stack run -- check program.tersus   # parse and validate; prints OK
stack run -- run program.tersus     # validate, then lower to the MIR, run that and print the return value
stack run -- mir program.tersus     # validate, then print the MIR
stack run -- owned program.tersus   # validate, then print the MIR with who owns each value (moves, copies, frees)
stack run -- llvm program.tersus    # validate, then print the LLVM IR
stack run -- build program.tersus -o program   # validate, then compile to an executable with clang
```

`run` never runs a program that fails validation. `mir` prints the program as the blocks the machine runs (see `MIR.md`). A program that does not `return` prints nothing. Integers print as digits, lists as `[1, 2]`, and booleans as `true`/`false`. Pass `-` instead of a file name to read the program from standard input.

`build` writes the IR and the C runtime to uniquely named files in the temporary directory, runs `clang -O2` on them, and removes those files; it needs `clang` on the path. The executable prints the return value as `run` does and stops on an `Integer overflow` with the same message and exit status. Native code handles every type of the language, and values print as `run` prints them. It does not check what validation proved (a divisor that is not 0, an index in range), so a program that validates cannot trip them, and a bug in the validator would be undefined behaviour here and an error in `run`.

## How Validation Works

Checking every proposition a real program could need is not feasible, so validation is a bounded search that is sound but incomplete:

1. **Heuristics do the common work.** The validator tries, without any help from the program: equalities between terms and their parts, integer comparisons (see Arithmetic), evaluation of builtins on known values, `forall` facts at the elements the program reads, the facts that function contracts export (and nothing else about a callee, see Function Contracts), and the invariants of a loop that follow from how its counters and lists start and change (see Inferred invariants). Each search is bounded: a fixed number of `forall` instantiation rounds, and a fixed number of case splits.
2. **Whatever they cannot prove is rejected.** A statement is never accepted on a guess. When the search runs out, the validator reports `Could not prove: P`, which means "not provable by these heuristics", not "false". The one definite failure is a `checkRel` over concrete values, which says `Relation does not hold`.
3. **The program supplies the rest.** You move the proof context closer to the goal until the heuristics can finish, with:
   - an intermediate `affirm` (proved, then available as a fact),
   - `define`, which names a term so it exists in the context,
   - `rewrite` with `eval`, `evalAll`, `refl`, `checkRel`, or your own `axiom` and `proof` rules,
   - a stronger input contract, output contract or loop invariant.

```tersus
fn f(l: List<Int>) -> Int [{ affirm size(l) > 3; affirm forall j in 0..size(l): get(l, j) = 0; }] [{ }] {
    define v = get(l, 1);   // puts the term get(l, 1) in the context, so the forall is used at 1
    affirm v = 0;           // without that term nothing mentions an element of l
    return 1;
};
```

A `forall` fact is only used at elements that appear in the context, so naming one with `define` or in an earlier `affirm` is how you ask for it. Facts you add with `axiom` are assumed, not checked, so they are the part of a program to review.

## Values

Tersus currently has four runtime value categories:

- Integers: `0`, `1`, `42`
- Lists of one element type: `[]`, `[1]`, `[3, 6, 9]`, `[true, false]`, `[[1, 2], [3]]`. List literals contain literals only.
- Booleans: `true`, `false`
- Functions: builtin functions from the standard library or user-defined functions

Boolean values can also be produced by relation expressions such as `x < y`. The condition of an `if` consumes them.

Integer literals can be negative: `-1`, `[-1, 2]`.

### Integers

`Int` is a 64-bit signed integer, from `-9223372036854775808` to `9223372036854775807`.

- A literal outside that range is a parse error (`Integer literal out of range`).
- `+`, `-`, `*` and `/` whose result is outside the range stop the program with `Integer overflow` (`9223372036854775807 + 1`, and `-9223372036854775808 / -1`, whose result is one too large). The program does not wrap, and compiled code traps in the same way. `%` cannot overflow.
- The validator reasons about unbounded integers, so a property it proves holds for every run that does not stop on an overflow. It does not prove that no overflow happens (`x + 1 > x` is provable, and `9223372036854775807 + 1` still stops the program); a program that has to be sure adds the bound it needs as a contract (`affirm n < 9223372036854775807;`).

## Types

Every value has a type, and programs are type checked before they are validated:

- A declared struct or enum, such as `Node` or `Shape`,
- `Int`, `Bool`, and `List<T>` for any element type `T`, such as `List<Int>`, `List<Bool>` or `List<List<Int>>`. All the elements of a list have the same type, and `[]` takes its element type from how it is used. A variable holding `[]` has one type for its whole life, so `e = []` cannot be pushed an `Int` once and a list later,
- `Array<T, N>`, a sequence of `N` elements of `Int`, `Bool` or arrays, held inline, with the size part of the type: `Array<Int, 3>`, `Array<Bool, 8>` or `Array<Array<Int, 3>, 2>` (see Arrays). Two arrays are of one type only if they have the same size, and an array is never a `List`,
- `fn(Int, Int) -> Int` for a function value.

A function writes the type of each parameter and of its return value. A local variable takes the type of its first assignment, and assigning a different type to it later is an error. Types exist only for checking: validation and evaluation never look at them. Every `return` of the program itself (outside any function) must have the type of the first, as `if c { return 1; } else { return false; };` has none.

```tersus
fn scale(values: List<Int>, factor: Int) -> List<Int> {
    out = [];
    i = 0;
    while i < size(values) [{ affirm i >= 0; }] shrinks size(values) - i {
        out = push(out, get(values, i) * factor);
        i = i + 1;
    };
    return out;
};
```

The builtins have these signatures: `size : fn(List<a>) -> Int` (`a` is any one type, chosen anew at each use), `first` and `last : fn(List<a>) -> a`, `get : fn(List<a>, Int) -> a`, `push : fn(List<a>, a) -> List<a>`, `set : fn(List<a>, Int, a) -> List<a>`, `array(n, x)` of type `Array<a, n>` for a constant `n` (a size that is a constant cannot be written as a signature), `+ - * /` on `Int`, `=` and `!=` on two values of the same type (any type but a function), and `< <= > >=` on `Int`. `size`, `first`, `last`, `get` and `set` also take an array in place of the list, with `Array<a, n>` for `List<a>` in the signature (and `set` giving the same `Array<a, n>`): which one is meant is decided by the type of the first argument. (A builtin used as a value, such as `h = size;`, is the one for lists.) A mismatch is reported before anything runs:

```
Type error: argument 1 of size: expected List<?>, got Int
Type error: returned value: expected Int, got List<Int>
```

A proof is a `Bool` expression and is checked the same way. The bodies of `axiom` and `proof` rules are not type checked (their parameters have no types), and a proof may name a proof variable exported by a called function's contract without the checker knowing its type.

## Structs

A struct is a named record whose fields are fixed at compile time. It is declared before it is used.

```tersus
struct Node { value: Int, prev: Int, next: Int };

n = Node { value: 1, prev: 0, next: 2 };   // every field, in any order
v = n.value;                               // read a field
m = Node { next: 3, ..n };                 // a new Node: next replaced, the rest copied from n
```

- A literal gives every field, or names the fields that change and ends with `..base` to copy the rest. The base must be a value of the same struct. A missing, repeated or unknown field is a parse error, so is a `..base` that has nothing to copy, and so is a struct named `Int`, `Bool` or `List`.
- Structs are values. Nothing is mutated: `Node { next: 3, ..n }` is a new struct and `n` is unchanged. There is no field assignment, so write `n = Node { next: 3, ..n };`. A struct is held where it is made, as its fields (natively, the words of its fields in the frame of the function, in another struct, or in a list), so a struct or an enum costs no allocation, and giving one to a function gives it a copy.
- `=` and `!=` compare structs field by field, and a struct can hold any type, including lists and other structs declared earlier. A struct cannot hold itself (it would have no size); it holds the recursion in a `Box` (see Box).
- Field reads and literals work in proofs too, so a contract can say `affirm return.next = target;`.
- The validator treats a literal as a constructor applied to its fields. Reading a field of a literal gives the field (`Node { next: 3, ..n }.value` is `n.value`), two equal constructions agree field by field, and so an update's other fields are known without a `forall`. It does not yet know that a struct equals a rebuilt copy of its own fields (`Node { value: n.value, prev: n.prev, next: n.next } = n`), so state that with the fields you need.

```tersus
fn relink(n: Node, target: Int) -> Node [{ }] [{ affirm return.next = target; affirm return.value = n.value; }] {
    return Node { next: target, ..n };
};
```

Lists of structs work like any list: `set(nodes, i, Node { next: 5, ..get(nodes, i) })` changes one element, and the `forall` frame of `set` says the others are unchanged. See `examples/structs.tersus`.

### Invariants

A struct can say what every value of it meets. The invariant is written after the fields, with the names of the fields, and is proved where a value is made and assumed for every value that is given:

```tersus
struct Range { lo: Int, hi: Int } invariant [{ affirm lo <= hi; }];

fn width(r: Range) -> Int [{ }] [{ affirm return >= 0; }] {    // r.lo <= r.hi is known, with no contract to say it
    return r.hi - r.lo;
};

fn widen(r: Range) -> Range [{ }] [{ }] {
    return Range { lo: r.hi + 1, ..r };                            // refused: A Range is made that does not meet its invariant: Could not prove: lo <= hi
};
```

- **Where it is proved**: at every literal, `..base` update and constant of the struct, with the names of the fields standing for the values it is made of (`A Counter is made that does not meet its invariant: Could not prove: n >= 0`). A struct is only ever made there, so no value breaks it.
- **Where it is assumed**: for a parameter, the result of a call, an assignment, a field that is read (a `Range` inside another struct has its own invariant) and in a loop, so a contract or a loop invariant never repeats it. It is also known to the contracts of a function, so `affirm width(r) >= 0` can be proved from it.
- **A struct with types** has one invariant for every type (`struct Vec<T> { ... } invariant [{ affirm len >= 0; }]`), and it can use `size`, `get` and the functions of the program (see Functions In Contracts). It cannot use the sizes of the struct (`Packet<n>`) yet.


## Enums

An enum is a type with several variants, each with its own named fields (or none). A variant is written `Enum::Variant`.

```tersus
enum Shape {
    Circle { radius: Int },
    Rect { width: Int, height: Int },
    Empty,
};

s = Shape::Circle { radius: 4 };
e = Shape::Empty;
affirm s is Shape::Circle;       // `is` tests the variant, in an expression or a proof
```

A `match` takes a value apart. Every variant needs an arm, and an arm binds the fields it names (it may leave fields out):

```tersus
fn area(s: Shape) -> Int {
    return match s {
        Shape::Circle { radius: r } => r * r * 3,
        Shape::Rect { width: w, height: h } => w * h,
        Shape::Empty => 0,
    };
};

match s {                                   // as a statement, the arms are blocks
    Shape::Circle { radius: r } => { total = r; },
    Shape::Rect { width: w, height: h } => { total = w; },
    Shape::Empty => { },
};
```

- `return match ...` and `variable = match ...` take an expression in each arm. A `match` is not an expression inside a larger expression, and `variable = match ...` needs the variable to exist already, like any variable assigned in a branch (declare it first: `area = 0;`).
- A `match` is rewritten into an `if` chain of `is` tests, with the last variant in the final `else`, so it is validated like an `if`: an arm that cannot run is vacuous, and the facts of the arms that can are joined. A match with a missing, repeated or foreign variant is a parse error.
- What an arm binds, and any variable first assigned in it, is local to the arm. A bound name hides a variable of the same name outside the match, which keeps its value. The value matched is read once.
- A struct can be matched as the only variant of its type: `match p { Point { x: a } => a }`.
- An enum cannot hold itself (it would have no size), but it can hold a `Box` of itself: `enum Tree { Leaf, Branch { left: Box<Tree>, value: Int, right: Box<Tree> } }`, and a function over a tree recurses on its parts (see Box).
- Equality `=` is structural, and `x != y` is proved for values built by different variants or with different fields.
- Fields of an enum value are read after a **cast** to the variant that has them: `(s as Shape::Circle).radius`. Several variants may have a field of the same name, so `s.radius` alone does not say which variant is meant, and it is a type error on an enum value (it works on a struct). The cast has the type `Shape::Circle`, which can be written as a parameter type (`fn r(c: Shape::Circle)`), and a value of that type can be passed where a `Shape` is wanted but not the other way round.
- A cast is checked by the validator and does nothing when the program runs. The validator demands the proof that the value is that variant, the way `get` demands an index in range: an `affirm s is Shape::Circle;` in a contract, an earlier `affirm`, an `if s is Shape::Circle`, or a value built as a `Shape::Circle`. A cast it cannot prove is a validation error (`Could not prove: value is Shape::Circle`). If a wrong cast reaches execution anyway, the behaviour is undefined: this interpreter does not check the cast, and reading a field that the value does not have is an error that says so. What a program computes never depends on the proofs, so proofs could be used to speed a program up but not to change what it does.
- A contract can demand a variant without a cast, `[{ affirm o is Opt::Some; }]`, and the caller has to show it. Updating a variant, `Shape::Rect { width: 10, ..s }`, copies the other fields from `s as Shape::Rect`, so it asks for the same proof.

See `examples/enums.tersus`.

## Box

`Box<T>` holds a value `T` of any type that has a size apart from where it is used, and is what a type that contains itself holds its recursion in. It also holds an array of no size, which can only be behind a pointer (see Arrays). A type cannot hold itself by value, since it would have no size; the declaration is refused (`Tree holds itself, so it would have no size: hold the recursion in a Box, as in Box<Tree>`). A `List<Tree>` would also do, since the elements of a list are kept apart.

```tersus
enum Tree {
    Leaf,
    Branch { left: Box<Tree>, value: Int, right: Box<Tree> },
};

fn sum(t: Box<Tree>) -> Int shrinks t {
    return match t {
        Tree::Leaf => 0,
        Tree::Branch { left: l, value: v, right: r } => v + sum(l) + sum(r),
    };
};

leaf = Box::new(Tree::Leaf);
return sum(Box::new(Tree::Branch { left: leaf, value: 2, right: Box::new(Tree::Leaf) }));
```

- **`Box::new(x)`** holds `x` in a Box; `Box::unbox(b)` gives back what a Box holds. They are written as calls and cannot be used as values (`h = Box::new` is an error).
- **A Box has the value of what it holds.** It changes where the value lives, not what it is: `Box::new(p) = Box::new(q)` compares `p` and `q`, the validator reasons about a Box as about its contents, and `Box::unbox(Box::new(x))` is `x`. `Box<Tree>` and `Tree` are different types, and neither is used for the other.
- **A Box is looked into where a struct or an enum is looked at.** A field of a boxed struct is read as `b.x`, the base of an update can be a Box (`P { x: 9, ..b }`), `b is Tree::Branch`, `b as Tree::Branch` and `match b { ... }` work on a Box, and `shrinks b` is the shrinking of a value that loses a field at a time. A function over the contents of a Box is called on `Box::unbox(b)`, as in `Box::unbox(b).total()`.
- **What a Box can hold.** Any type that has a size: a struct or an enum, an `Int` or a `Bool`, a list, an array of a size, another Box (`Box::unbox(Box::new(3))` is `3`). An array of no size, `Array<T>` or `Array<T, ?>`, is held only behind a Box (see Arrays), and `Box::unbox` cannot take one out, since it would not know how much to take.
- **A Box of an array is looked through by `size`, `first`, `last`, `get` and `set`**, which work on it as on the array (`set` gives the Box back with the element changed, in place when nothing else has the Box).
- **Where a Box lives.** Natively a struct or an enum is not on the heap: it is held where it is made, as the words of its fields (an enum a word that says the variant and then the fields of that variant), in the frame of a function, in a field, or in a list, and copied by value. A `Box` is what puts one on the heap, and the pointer to it is one word, so a type that holds itself holds it in a `Box`; the list is the other thing on the heap. A `Box` of an array of no size is two words held in line, the address and the number of elements (see Arrays).

## Traits And Impls

An `impl` gives a struct or enum functions of its own, and a `trait` names functions that several types provide, with the contracts every one of them must meet.

```tersus
struct Counter { value: Int };

impl Counter {                                   // functions of Counter that belong to no trait
    fn new(value: Int) -> Self { return Self { value: value }; };
    fn plus(self: Self, by: Int) -> Self { return Self { value: self.value + by }; };
};

trait Measure {                                  // signatures and contracts, no bodies
    fn size(self: Self) -> Int [{ }] [{ affirm return >= 0; }];
};

impl Measure for Counter {
    fn size(self: Self) -> Int [{ }] [{ affirm return = 1; }] { return 1; };
};

c = Counter::new(4).plus(1);                     // Type::function(...), and x.function(...)
n = c.size() + Measure::size(c);                 // through the trait
```

- **The functions of an impl are named in full**, `<Counter>::plus` for an impl of the type and `<Counter as Measure>::size` for an impl of a trait, and a call is an ordinary call of that function, checked and validated against its contracts like the call of any function. The short forms are resolved by the checker (below). An impl is written for a struct or an enum declared before it (not for `Int`, `Bool` or a list), and can be written only at the top of the program. A function sees the functions defined before it, so an impl comes before the code that calls its functions; the functions of an impl can call each other in the order they are written, and themselves. A function cannot be named like a variant (`Shape::Circle`), and defining the same full name twice is `Function already defined`.
- **`Type::function(...)` and `x.function(...)` need the name to be unambiguous.** If exactly one impl of the type defines `function`, that is the one called. If several do (the type's own impl and one of a trait, or two traits), the call is an error that lists the paths, and the program names the one it means:

  ```tersus
  c.label()                       // error: Counter::label is ambiguous
  Name::label(c)                  // the function of the trait Name, for the type of c
  <Counter as Name>::label(c)     // the function of the impl of Name for Counter, written in full
  <Counter>::label(c)             // the function of the impl of Counter itself
  ```

  The full form is also how a trait function with no `Self` parameter is called when it is ambiguous (`<Counter as Name>::make()`). Two functions of a type can have one name only when they come from different impls, and an ambiguity is only reported by a call that uses the short form.
- **`Self`** is the type the impl is for, in the signatures and the bodies of its functions: `Self`, `Self::Variant` (a variant of an enum), and `Self { ... }` as a literal. In a trait it is the type that implements the trait.
- **`x.function(a, b)` is `Type::function(x, a, b)`** where `Type` is the type of `x` (a value cast to a variant, `(s as Shape::Circle).area()`, is a value of its enum). The checker decides it from the type of `x`, and fails if there is no such function, or if `x` has no type with functions (an `Int`, a list). `x.f(a)` always calls a function of the type: it is not a call of a field that holds a function.
- **`Trait::function(x, ...)`** calls the function of the type of the argument that the trait's signature gives the type `Self` (the first, if several do), and the type must implement the trait. A trait function with no `Self` parameter (`fn start() -> Self`) cannot be called through the trait, since nothing says which type is meant: write `Counter::start()`.
- **An impl of a trait has exactly the trait's functions**, with the types the trait declares and `Self` replaced by the type. A missing function, an extra one and a different type are type errors, and so is implementing a trait twice for one type. A trait and a type cannot have the same name.
- **The contracts of the trait bind every impl.** An impl may ask for less than the trait does (a weaker input contract) and promise more (a stronger output contract), but not the other way round. The checker adds to the program, for each function of the impl, a function that has the trait's contracts and calls the impl's function, and the validator checks it like any other:

  ```tersus
  fn "Measure for Counter::size"(self: Counter) -> Int [{ }] [{ affirm return >= 0; }] { return Counter::size(self); };
  ```

  The call has to meet the impl's input contract, which the trait's input contract is assumed to give, and the impl's output contract has to give the trait's. The failure names the impl: `impl Step for Counter: advance does not meet what Step declares (...): Funct input validation failed: Could not prove: by > 5`. Only the impl's contracts count, not what its body happens to establish: an impl whose body returns `4` meets `affirm return >= 0;` only if its own output contract says so. These functions show in `mir` and are compiled, and nothing calls them.
- **A call is to the impl's function**, so the caller knows the impl's contracts, which may be stronger than the trait's (`examples/traits.tersus`). A function that may not end (`~`) can implement a trait, and the functions that call it have to be `~` as for any function.
- **A trait's contracts are type checked where the trait is written**, with `Self` as a type that has no fields, so they can mention the other parameters and `return` but not read a field of a `Self` value (`affirm self.value > 0;` in a trait is a type error). A contract calls the functions of the trait on `Self` (`size(self)`) and the functions of the program, and the check of an impl resolves them to the impl's.
- `trait`, `impl` and `Self` are reserved (`Self` cannot be the name of a type or a trait); `implement` and `traits` are still ordinary names. Trait and impl blocks end with `;` like every declaration.

### A trait with types

A trait can have types, which each impl gives, and a struct with types can implement it:

```tersus
trait Sequence<E> {
    fn size(self: &Self) -> Int [{ }] [{ affirm return >= 0; }];
    fn get(self: &Self, i: Int) -> E [{ affirm i >= 0; affirm i < size(self); }] [{ }];
};

trait Growable<E> {                             // a trait may call the functions of the traits before it
    fn push(self: Self, x: E) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }];
};

struct Two<T> { a: T, b: T, n: Int } invariant [{ affirm n >= 0; }];

impl<T> Sequence<T> for Two<T> {                // the types of the trait are given by the impl, in its own names
    fn size(self: &Self) -> Int [{ }] [{ affirm return = self.n; }] { return self.n; };
    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < size(self); }] [{ }] {
        if i = 0 { return self.a; };
        return self.b;
    };
};

impl<T> Growable<T> for Two<T> {
    fn push(self: Self, x: T) -> Self [{ }] [{ affirm size(return) = size(self) + 1; }] {
        return Self { a: self.a, b: x, n: self.n + 1 };
    };
};
```

- **The trait's types are written between the `<>`** (`trait Sequence<E>`), a type for each, and an impl gives the types the trait has (`impl<T> Sequence<T> for Two<T>`; `impl Sequence for Two<T>` and a wrong number are parse errors). An impl for a struct with parameters names them after `impl`, as in `impl<T> Two<T>`, and each of its functions is for any `T`.
- **A contract of a trait calls its functions on `Self`**: `size(self)` is the function `size` of the type that implements the trait, whichever it is. In an impl, and in the code that uses it, `size(self)` is that type's function, so a contract that is written with it means what the impl promises: `size(v) = self.n` here. The check that the impl meets the trait (the function the checker adds, see above) calls the impl and proves the trait's output contract from the impl's, with `size(return)` and the other calls resolved to the impl's functions.
- **The invariant of the struct is what makes a promise like `affirm return >= 0` provable** for `size`: without `invariant [{ affirm n >= 0; }]` the impl's `size` could return a negative `n` and is refused (`impl Sequence for Two: size does not meet what Sequence declares ... Could not prove: return >= 0`).
- **`size(v)`, `get(v, i)`, `set(v, i, x)`, `push(v, x)`, `first(v)` and `last(v)` on a struct are calls of its impl's function of that name**, in the code and in contracts, so a library type is used with the names of the lists. `v.size()` and `Sequence::size(v)` are the same call. A struct without the function is an error (`Plain::size is not defined before this call`).
- **Not yet**: a function over any type that implements a trait (`fn total<S: Sequence<Int>>(s: &S)`), a trait with sizes, and a default body. A function that wants one type writes it (`fn firstOf<T>(v: &Vec<T>)`).

A wrong call reads like this:

```
Type error: Counter::nothing is not defined before this call (there is no such function, or its impl comes later)
Type error: Counter does not implement Measure
Type error: Counter::label is ambiguous, several impls define it. Call the one that is meant by its path: <Counter as Name>::label(...) or <Counter as Code>::label(...)
Type error: impl Step for Counter lacks the function start
Type error: impl Step for Counter: start is fn() -> Int, but Step declares fn() -> Counter
```

See `examples/traits.tersus`, and `examples/rejected/` for `trait_input_stronger`, `trait_output_weaker`, `trait_missing_function` and `trait_ambiguous_call`.

## Expressions

Expressions can be literals, variables, function calls, parenthesized expressions, or infix operations.

```tersus
5
[1, 2, 3]
x
size(x)
first(xs) + last(xs)
(10 - 5) - 5
```

The current infix operators are:

- Arithmetic: `*`, `/`, `%`, `+`, `-`
- Relations: `=`, `!=`, `<`, `>`, `<=`, `>=`

Infix operators bind in three levels, tightest first: `*`, `/` and `%`, then `+` and `-`, then the relations. Each level associates left, so `return = n + 1` reads as `return = (n + 1)` and `a + 1 < b * 2` as `(a + 1) < (b * 2)`. Use parentheses when the intended grouping is not clear.

## Builtins

The standard library seeds these builtin functions:

- `size(list)`: returns the length of a list.
- `first(list)`: returns the first element of a non-empty list.
- `last(list)`: returns the last element of a non-empty list.
- `get(list, index)`: returns the element at `index`, counting from 0. The index must satisfy `0 <= index < size(list)`.
- `push(list, x)`: returns a new list with `x` added at the end. Lists are values, so the argument list is unchanged.
- `pop(list)`: returns a new list without the last element. The list must not be empty (`Relation does not hold` otherwise), the result is one shorter and keeps the others in their places. There is no `pop` of an array, whose size never changes.
- **Methods.** The functions of a list can be written as methods: `l.push(x)`, `l.pop()`, `l.size()`, `l.get(i)`, `l.set(i, x)`, `l.first()`, `l.last()` are `push(l, x)` and so on, and `size`, `first`, `last`, `get` and `set` are methods of an array and of a Box of an array too (`examples/list_methods.tersus`). A list literal is not given a method (`[1, 2].size()` does not parse): name it first.
- `set(list, index, x)`: returns a new list with the element at `index` replaced by `x`. The index must satisfy `0 <= index < size(list)`, and the argument list is unchanged.
- `array(n, x)`: returns an array of `n` copies of `x`, an `Array<T, n>`. The size is a constant that is not negative (see Arrays).
- `#[1, 2, 3]`: an array written out, the elements being literals, an `Array<Int, 3>`.
- `+` and `-`: integer arithmetic.
- `*`, `/` and `%`: integer arithmetic. `/` rounds down and `x % y` is what is left, `x = (x / y) * y + x % y`, so it has the sign of `y` (`-7 % 3` is `2`, `7 % -3` is `-2`). Like `/`, a divisor must be shown to be non-zero.
- `=`, `!=`, `<`, `>`, `<=`, `>=`: integer relations returning booleans.

`first` and `last` have builtin input contracts requiring the list size to be greater than zero. The validator checks that with the arithmetic (see Arithmetic), so a call such as `first(l)` needs `size(l) > 0` to be known (from a literal list, a guard or an earlier `affirm`) and fails with `Could not prove: size(list) > 0` otherwise. They also export `return = get(list, 0)` and `return = get(list, size(list) - 1)`, so facts about the elements of a list (a `forall`, or `get(l, 0) = x`) reach `first(l)` and `last(l)`. Concrete evaluation still rejects empty lists and wrong argument types.

`get` and `set` have a builtin input contract requiring `index >= 0` and `index < size(list)`. It is checked with the primitive `checkRel` rewrite, so a call with a concrete list and index needs no proof, while a symbolic index must already be provable at the call site, usually from the enclosing function's contract or a loop invariant:

```tersus
a = [5, 6, 7];
x = get(a, 2);          // fine: 0 <= 2 < 3
// y = get(a, 3);       // rejected: 3 < 3 does not hold

// The contract has to show both bounds, since the body can only assume them.
fn at(lst: List<Int>, i: Int) -> Int [{
    rewrite checkRel i >= 0;
    rewrite checkRel i < size(lst);
    affirm i >= 0;
    affirm i < size(lst);
}] [{ }] {
    return get(lst, i);
};
```

`push` has a builtin output contract, `size(return) = size(list) + 1` and `get(return, size(list)) = x` (the new element sits at the old size), which is instantiated at every call. That is what lets a function that builds a list state its size in its own output contract (see `examples/build_list.tersus`). An empty list is the literal `[]`.

A call can be nested in the arguments of another (`push(push(l, 1), 2)`, `n + f(n - 1)`), and the output contract of the inner call is known for its result, so `size(return) = size(l) + 2` holds for the first and `r >= n` follows from `f`'s contract in the second.

`set` has the same input contract as `get`, and a builtin output contract, `size(return) = size(list)` and `get(return, index) = x`. Since lists are values, `set` does not change its argument: update a variable by assigning the result back to it.

```tersus
a = [1, 2, 3];
b = set(a, 1, 20);      // [1, 20, 3]; a is still [1, 2, 3]
a = set(a, 0, 9);       // [9, 2, 3]
// c = set(a, 3, 0);    // rejected: 3 < size(a) does not hold
```

So `push` and `set` say what they wrote, and a function can repeat it in its own output contract (see `examples/element_facts.tersus`):

```tersus
l = [4, 5];
r = push(l, 9);
define n = size(l);
affirm get(r, n) = 9;         // the new last element

a = [1, 2, 3];
i = 1;
b = set(a, i, 20);
affirm get(b, i) = 20;        // the element just written
// affirm get(b, 0) = get(a, 0);   // rejected: the other elements are not covered yet
```

Every other element is unchanged, which the contracts state with a `forall` (see `forall` below). `push(l, x)` exports `forall j in 0..size(l): get(return, j) = get(l, j)`, and `set(l, i, x)` exports the same with the guard `j != i`. Like any `forall`, they are used at the elements a program reads:

```
a = [10, 20, 30];
b = set(a, 1, 99);
affirm get(b, 0) = get(a, 0);   // an element before the one written
affirm get(b, 2) = get(a, 2);   // and one after it
// affirm get(b, 1) = get(a, 1);   // rejected: set changed this one
```

See `examples/frame_facts.tersus`. `examples/update_list.tersus` updates every element of a list in a loop.

Lists are built with `push`, updated with `set`, and read by `get`, `first` and `last`. A list holds elements of one type, and the element type is part of the list's type (`List<Bool>`).

## Statements

### Assignment

Assignments bind a variable in the current scope. If a variable already exists in the current or parent scope, assignment updates that existing binding.

```tersus
x = 5;
xs = [3, 6, 9];
n = size(xs);
```

### Return

`return` evaluates an expression, stores it as the return value of the program or function call, and ends it. Statements after a `return` do not run, including when the `return` is inside a nested block, `if` or `while`; since nothing can run them, the validator does not check them either (an `affirm` there is not proved).

```tersus
return size(xs);
```

A program that ends without `return` has no return value, and a function that does so fails evaluation.

### Blocks

Blocks introduce a nested statement queue and parent scope.

```tersus
x = [3, 6, 9];
{
    x = [1];
};
return size(x);
```

In the current implementation, assignment searches parent scopes before creating a new local binding. Reassigning `x` inside the nested block updates the outer `x` if it already exists.

### If / Else

`if` runs one of two blocks depending on a boolean condition. `else` is optional, and `else if` chains.

```tersus
x = 5;
label = 0;
if x < 4 {
    label = 1;
} else if x < 9 {
    label = 2;
} else {
    label = 3;
};
return label;
```

- The condition is any expression that evaluates to a boolean; anything else fails evaluation with `Condition must be a boolean`.
- Like `fn` definitions and blocks, an `if` statement is ended with `;`.
- Each branch is a block. Assignments to variables that already exist outside update them, and a variable first assigned inside a branch is local to it. Declare the variable before the `if` (`label = 0;` above) to use it afterwards.
- `if`, `else` and `while` are reserved words; `iffy` and `elsewhere` are still ordinary names.
- `return` is allowed inside an `if` body (see Early return below).
- Loops are described in the next section.

#### Validating branches

The validator checks each branch assuming the condition holds (or, for `else`, that it does not), so a guard can make a builtin's contract provable:

```tersus
fn firstOr(lst: List<Int>, fallback: Int) -> Int {
    r = fallback;
    if size(lst) > 0 {
        define s = size(lst);
        rewrite eqToGtZero s;
        r = first(lst);
    };
    return r;
};
```

For a relation condition the branch assumes the relation (`size(lst) > 0`), and the `else` branch assumes its negation (`<` becomes `>=`, `>` becomes `<=`, and so on). Equality has no negation to record, so the `else` branch of `x = y` learns only that the condition is false. Every condition also records whether its boolean is `true` or `false`.

After the `if`, only facts that **both** branches establish are kept. For each outer variable a branch assigned, the validator introduces a fresh value that equals the variable's final value in either branch, and keeps a fact about it only if both branches prove it. A fact that holds only under the condition, including the condition itself, is not known after the `if`:

```tersus
fn f(n: Int) -> Int {
    y = 0;
    if n < 6 {
        y = 1;
        rewrite eqToGtZero y;
    } else {
        y = 2;
        rewrite eqToGtZero y;
    };
    affirm y > 0;   // both branches proved it, so this validates
    affirm n < 6;   // rejected: only the then-branch knew this
    return y;
};
```

The facts the join tries are not only the ones a branch stated. It also tries what the program is about to need, and keeps each if both branches entail it:

- the `affirm`s that follow in the same block or in the blocks around it, and the invariant of a loop that follows,
- the invariant and the variant check at the end of the loop body that the `if` is in (the variant must be smaller than at the start of the iteration),
- the facts that held before the `if`, about a variable the branches assign, now about its new value, and
- the facts the else branch stated, which the then branch may entail.

```tersus
fn f(c: Int) -> Int {
    x = 0;
    if c > 0 { x = 1; } else { x = 2; };
    affirm x > 0;           // neither branch says so; both entail it, and the affirm that follows asked
    return x;
};
```

In a loop, an `if` in the body does not have to restate the invariant or the variant in each branch (`examples/linear.tersus` searches by halving a range with an `if` that moves one end, and writes neither). A fact is only tried if the program asks for it as above, and it is checked with congruence and arithmetic only, with no `forall` instantiated and no case split, so a fact that needs those still has to be stated in each branch.

This is sound but incomplete. A fact about values that existed before the `if` that nothing later asks for, and that the branches do not both state, is dropped, so state it in both branches or after the `if` when you need it. The output contract of the function is asked for too, about the value of the `return` that follows the `if` in the same block or in the blocks around it, so `r = n; if c > 0 { r = r + 1; } else { r = r + 2; }; return r;` meets `affirm return > 0;` when `n > 0`.

#### Early return

A `return` inside an `if` body ends the function there, so a guard clause can handle a case and leave the rest of the function to the others:

```tersus
fn firstOr(lst: List<Int>, fallback: Int) -> Int {
    if size(lst) > 0 {
    } else {
        return fallback;
    };
    // Only reached when size(lst) > 0
    define s = size(lst);
    rewrite eqToGtZero s;
    return first(lst);
};
```

A branch that returned does not reach the statements after the `if`, so they are validated only under the paths that fall through. In the example above, `first(lst)` is checked assuming `size(lst) > 0`, since the else-branch returned, and the guard `if size(lst) > 0 { return fallback; };` would be rejected because the code after it only knows `size(lst) <= 0`.

Each `return` checks the function's output contract on its own path (for example `affirm return > 0;`, and what a `rewrite` in it needs, such as the input contract of a rule), so every path that returns has to entail it. What the function promises its callers is what the paths that return all establish about the returned value and the parameters. If some path reaches the end without returning, there is no return value: a program may do that, and a function that does so is rejected with `Return value not found`.

A `return` inside a `while` body works the same way, see Returning from a loop below.

### While

`while` repeats a block for as long as its condition is true.

```tersus
i = 0;
n = 0;
while i < 3 shrinks 3 - i {
    i = i + 1;
    n = n + 2;
};
return n;
```

The condition must evaluate to a boolean, the body is a block with the same scoping as an `if` branch, and the statement ends with `;`. A loop has to say why it ends, here with `shrinks 3 - i`, see Termination below; evaluation ignores that, and a loop whose condition never becomes false runs forever. A `return` inside the body ends the function or program, and stops the loop.

#### Loop invariants

The validator does not unroll loops. A loop can carry an invariant, written with the same `[{ ... }]` contract syntax as functions, between the condition and the body:

```tersus
while i < 3 [{ affirm i <= 3; }] shrinks 3 - i {
    rewrite stepWithinBound i;
    i = i + 1;
};
```

The invariant is optional; without one the loop still validates but proves nothing about the variables it changes. Validation works like this:

1. The invariant must hold before the first iteration.
2. Every outer variable the body assigns is treated as an unknown value from then on. Facts about its earlier values are not carried over, but facts about variables the body does not assign are.
3. Assuming the invariant and the loop condition, the body must establish the invariant again at its end. The invariant's `rewrite` statements run when it is being checked, and are skipped when it is assumed, exactly as for function contracts.
4. After the loop the invariant holds and the condition does not. An invariant `i <= 3` on `while i < 3` therefore gives `i >= 3` afterwards.

The invariant is about what is true if the loop ends; that it ends is shown by the termination clause that follows it, see Termination below. The validator reasons about integer comparisons itself (see Arithmetic below), so a counting loop needs no helper rules:

```tersus
i = 0;
while i < 3 [{ affirm i <= 3; }] shrinks 3 - i {
    i = i + 1;
};
affirm i >= 3;
```

`i = 0` gives the invariant on entry, `i < 3` gives `i + 1 <= 3` at the end of the body, and the negated condition gives `i >= 3` afterwards.

An invariant can use `forall` to describe a list that is built or updated element by element. The validator proves it for the new element and, with the frame facts of `push` and `set`, for the old ones:

```tersus
fn doubled(a: List<Int>) -> List<Int> [{ }] [{ affirm forall j in 0..size(a): get(return, j) = (get(a, j) + get(a, j)); }] {
    n = size(a);
    i = 0;
    out = [];
    while i < n [{
        affirm i >= 0; affirm i <= n; affirm size(out) = i;
        affirm forall j in 0..i: get(out, j) = (get(a, j) + get(a, j));
    }] shrinks n - i {
        out = push(out, get(a, i) + get(a, i));
        i = i + 1;
    };
    return out;
};
```

See `examples/parallel_sum.tersus`, `examples/build_list.tersus` and `examples/update_list.tersus`.

`while` is a reserved word; `whiley` is still an ordinary name.

#### Inferred invariants

The invariants of a loop are completed by the validator. For each variable the body assigns, it starts from what is known when the loop is entered:

- a variable that is a number there is at least and at most that number, the size of a list likewise (a list that is not a literal can still have a size the facts know, such as `push(push([], a), b)`, which has size 2), and two of these differ by what they differed by on entry;
- the first three elements of a list whose size is known on entry are terms of their own, so an element the loop leaves alone (the length field at index 1 of a buffer that only grows by `push`) keeps its value;
- a term that starts at a variable the loop does not assign, next to a term that starts at a number, differ by that variable: `i = size(out) + lo` for a loop that starts at `lo` and pushes once per iteration (`slice` in `examples/packet_parser.tersus`);
- a variable (or the size of a list) that is not known to be a number is compared with the variables the loop does not assign, and the comparison (`=`, `<=` or `>=`) is a candidate if the facts already imply it: `i <= n` when `i` starts at `0` and `n` is `size(a)`, or `size(out) = size(a)` when `out` starts as a copy of `a`.

It keeps a candidate only if the body establishes it again, assuming the ones that are left. For a body without a `return` this is repeated until none is dropped (at most four rounds); for a body with one, a candidate that is not preserved is found from the error and dropped, one at a time (at most twelve). What is kept is an invariant like one the program wrote: it holds on entry, is preserved, and holds after the loop together with the negated condition. Eight terms (the numbers and sizes before the elements of lists), twelve variables to compare with and thirty-two candidates at most are tried.

```tersus
out = [];
i = 0;
while i < 3 [{ affirm i <= 3; }] shrinks 3 - i {
    out = push(out, i);
    i = i + 1;
};
affirm size(out) = 3;       // size(out) = i was inferred: both start at 0 and grow by one
```

This is what makes `size(return) = size(a)` follow from a loop that pushes once per element, with no `affirm size(out) = i`, and `size(out) = size(a)` follow from a loop that `set`s the elements of a copy (`examples/update_list.tersus`). A sum of two variables that stays equal to another variable (`s + i = n`, or `s + i = n + 5` when `s` starts at `5`) is inferred too; a relation that is not a constant distance, a plain comparison or such a sum still has to be written, such as a list that grows by the size of another list per iteration. If a loop is refused because one of its inferred invariants is not preserved, the error is about the invariant the program wrote instead.

#### Returning from a loop

A body that contains `return` is validated as paths, in the same way as an `if` with a `return`:

```tersus
fn firstOver(n: Int) -> Int [{ }] [{ affirm return <= 3; }] {
    i = 0;
    rewrite zeroWithinBound i;
    while i < 3 [{ affirm i <= 3; }] shrinks 3 - i {
        if (i + i) > n {
            return i;
        };
        rewrite stepWithinBound i;
        i = i + 1;
    };
    return i;
};
```

- The invariant must hold on entry, as before.
- Every way of reaching the end of the body without returning must re-establish the invariant. A `return` does not excuse the paths that keep looping, so removing the `rewrite stepWithinBound i;` above is rejected with `Loop invariant is not preserved`.
- A path that returns assumes the invariant, the loop condition and whatever its own `if` conditions say. It checks the output contract on its own path, so the contract holds only if every returning path entails it. Above, `return <= 3` holds for the `return i` in the body (from the invariant) and for the one after the loop.
- The statements after the loop are validated once, from the state where the invariant holds and the condition is false. Facts that only a returning path knew, such as an `if` condition inside the body, are not known there.
- As for an `if`, a function where some path (including leaving the loop) does not return has no return value and is rejected with `Return value not found`.
- The variant of a loop with a `shrinks` clause must also be smaller on every path that keeps looping.

### For

`for i in lo..hi { ... }` counts `i` from `lo` up to, but not including, `hi`:

```tersus
fn total(a: List<Int>) -> Int {
    s = 0;
    for i in 0..size(a) {
        s = s + get(a, i);
    };
    return s;
};
```

It is a `while` loop and is validated as one: `lo` and `hi` are evaluated once, before the loop, and kept; `i` is set to `lo`; the loop runs while `i < hi` and adds `1` to `i` after the body; its invariant has `i >= lo` and `i <= hi`; and it shrinks `hi - i`, so no invariant or termination clause is needed. Inside the body `i < hi` holds, so `get(a, i)` above is in range, and after the loop `i = hi` (the variable stays in scope, and has the value `hi`). Written out, with names the program cannot use for `lo` and `hi`:

```tersus
lo = 0; hi = size(a); i = lo;
while i < hi [{ affirm i >= lo; affirm i <= hi; }] shrinks hi - i {
    s = s + get(a, i);
    i = i + 1;
};
```

An invariant of the program's own goes between the range and the body, `for i in 0..n [{ affirm ... }] { ... }`, and is added to those; the loop also gets the inferred invariants above. A `return` in the body leaves the function. A body that assigns `i`, in a branch or a nested loop too, is refused when the program is read (`The body of a for loop cannot assign its loop variable i`), so `i` is always the counter the loop advances; `lo` and `hi` must be integers. A range with `hi < lo` runs the body no times when the program runs, but the validator wants `lo <= hi` to be known, as the bounds of `i` are an invariant that has to hold on entry and that is what gives `i = hi` afterwards: `for i in 0..n` needs `affirm n >= 0` in the contract (`size(l)` is known to be at least 0), and is refused otherwise with `Loop invariant does not hold on entry`. `for` is a reserved word; `form` is still an ordinary name. See `examples/for_loops.tersus`.

#### Through the elements of a list

`for x in list { ... }` goes through the elements, and `for i, x in list { ... }` also has the index:

```tersus
fn total(a: List<Int>) -> Int {
    s = 0;
    for x in a {
        s = s + x;
    };
    return s;
};

for i, x in a {
    affirm x = get(a, i);
};
```

It is the range loop `for i in 0..size(list)`, with `x` bound to `get(list, i)` at the start of each iteration. The list is read once, before the loop, so a body that assigns the variable the list came from does not change what is looped over. `x` is local to the body: it is not defined after the loop, and a body may assign it, which changes only that iteration's copy. `i` is the loop variable of the range loop (it stays in scope, is `size(list)` afterwards, and cannot be assigned); without it, the index is a variable the program cannot write. An invariant goes between the list and the body and can mention `i`, but not `x`. Nested loops, a `return` in the body and lists of lists work as they do for a range.

### Termination

Statements that are not loops or calls end by themselves. A loop and a function that calls itself have to say why they end, or say that they may not. The validator checks what they say, or reports the code that is not guaranteed to terminate.

**`shrinks e`** names what gets smaller, here called the variant. Which kind of shrinking it means depends on the type of `e`, which the type checker resolves before validation:

- An `Int` counts down to a bound. For a loop, `e` must be at least `0` where an iteration starts (assuming the invariant and the condition), and smaller where the iteration ends, on every path that reaches the end of the body. A path that returns does not need to. For a function, `e` is evaluated in the parameters. It must be at least `0` for any arguments that meet the input contract, and at every call the function makes to itself the variant of the arguments must be smaller than the variant of the call it is in (the arguments of the function when it started, even if the body has assigned its parameters since).
- A struct or enum value must be a part of the one before it: a field, or a field of a field, which a `match` binding or `(t as Tree::Branch).left` is. Such values are finite, so this ends, and there is no bound to prove.
- Any other type is an error: `shrinks needs an Int, an enum or a struct`.

`i` can be counted up or down: `shrinks n - i` needs `i <= n` to be known where the iteration starts, and the condition `i < n` supplies it. The validator compares a difference such as `n - i` by its two sides, so `n - i >= 0` is `n >= i`, `n - (i + 1) < n - i` holds because `i + 1 > i`, and when both sides move (`k - i` with `i = i + 1; k = k - 1`, which shrinks by 2) or the variant is a sum (`shrinks i + j`) linear arithmetic decides it.

```tersus
fn sumTo(n: Int) -> Int [{ affirm n >= 0; }] shrinks n {
    if n < 1 { return 0; } else { return n + sumTo(n - 1); };
};

fn countDown(n: Int) -> Int [{ affirm n >= 0; }] [{ affirm return >= 0; }] {
    i = n;
    steps = 0;
    while i > 0 [{ affirm i >= 0; affirm steps >= 0; }] shrinks i {
        i = i - 1;
        steps = steps + 1;
    };
    return steps;
};

fn leaves(t: Box<Tree>) -> Int shrinks t {
    return match t {
        Tree::Leaf => 1,
        Tree::Branch { left: l, value: v, right: r } => leaves(l) + leaves(r),
    };
};
```

**`~`** says that no guarantee is given. A loop or function that has it validates as before, apart from that, so its invariant and contracts are still checked (partial correctness). A function that contains a loop declared `~`, or that calls a function declared `~`, is not guaranteed to terminate either, and has to say so with `~` itself, or it is rejected with `Not guaranteed to terminate`. The program outside of functions may contain such code.

```tersus
fn settle(n: Int) -> Int ~ {
    while n != 1 ~ {
        if n > 1 { n = n - 1; } else { n = n + 1; };
    };
    return n;
};

fn settleTwice(n: Int) -> Int ~ {
    return settle(n) + settle(n + 1);
};
```

The clause is written after the invariant of a loop, and after the contracts of a function, before the body. Leaving it out is an error for a loop (`Loop must say how it ends`) and for a function that calls itself (`Not guaranteed to terminate: it calls itself`); a function that has no loop of its own and does not call itself needs nothing, and a call to it ends. Only code that can be reached counts: where the facts are contradictory, as in `if n > 0 { if n < 0 { return settle(n); }; }`, a call to a function that may not end is not an error. The variant (and so `Recursive call does not shrink the variant`) is only checked for a function that calls itself, which can only be a function defined at the top level, by its name or through another name for it. A call cycle is always a function calling itself: there is no mutual recursion, because a function sees only the functions defined before it, and a function defined inside another can call the one around it only if both are declared `~`.

`shrinks` only means something in these places and is otherwise an ordinary name. See `examples/termination.tersus`, and `examples/rejected/` for `loop_without_termination`, `loop_variant_not_shrinking`, `loop_variant_unbounded`, `recursion_without_variant`, `recursion_variant_not_shrinking`, `recursion_shrinks_not_a_part`, `diverging_call` and `diverging_loop`.

#### Where this is going

`shrinks e` is meant to be sugar. The intended general form is a termination proof that the program writes out in the validation language, in the style of proof rules and loop invariants: a block of `affirm`s about the state at the start of an iteration or call and the state at its end, which together show that the code cannot go on for ever. `shrinks` would then expand to the block for its type (a bound and a strict decrease for an `Int`, a part-of relation for a struct or enum), and programs whose argument is not a single shrinking value (a lexicographic pair, a list that loses an element, mutually recursive functions) could write their own. That needs obligations that relate two states, which nothing in the language does yet, so it is not implemented. A syntax for code that is known never to terminate may be added later.

### Functions

Functions are defined with `fn` and assigned to the given name. Each parameter and the return value has a type: `fn name(param: Type, ...) -> Type { ... }`.

```tersus
fn add1(i: Int) -> Int {
    return i + 1;
};

x = add1(4);
```

Function arguments are comma-separated. Function bodies are ordinary statement blocks.

A function defined at the top level can be called by the functions defined after it, by name. A call is checked against the callee's contract, as it is in the main program, so a caller must establish the callee's input contract and can use its output contract.

```tersus
fn positive(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; };
fn inc(n: Int) -> Int [{ }] [{ affirm return = n + 1; }] { return n + 1; };
fn bump(n: Int) -> Int [{ affirm n >= 5; }] [{ affirm return > 5; }] { return positive(inc(n)); };
```

A function sees only the functions defined before it and itself, so there is no mutual recursion, and calling a later function is a validation error (`Undefined variable`).

A function can call itself. Its body is validated assuming its own output contract, and the contract is then checked against the body, so every recursive call must meet the input contract and the base cases must establish the output contract. It also has to say why it ends: `shrinks` followed by an expression that gets smaller at each call, or `~`, see Termination. A function declared `~` is only partially correct: `fn spin(n: Int) -> Int [{ }] [{ affirm return = 0; }] ~ { return spin(n); }` validates.

```tersus
fn upTo(i: Int, n: Int) -> Int [{ affirm i <= n; }] [{ affirm return = n; }] shrinks n - i {
    if i < n { return upTo(i + 1, n); } else { return n; };
};
```
 A function name can be defined only once. A function defined inside another function's body is local to that body: functions defined after it there cannot call it. The definition order is enforced by the type checker and the validator. An argument or local variable with the same name hides the function. See `examples/helper_functions.tersus` and `examples/recursion.tersus`.

A function body runs with its argument bindings and is expected to set a return value. If a function completes without `return`, the run fails (`Function did not return a value`), and the validator rejects a function that can do so.

### Argument Passing

Arguments are passed by value. Each argument expression is evaluated before the call and bound to the matching parameter in a fresh scope. The caller's variable is not moved and is still usable afterwards, and nothing the function does to a parameter, including reassigning it, is visible to the caller.

```tersus
fn reset(xs: List<Int>) -> Int {
    xs = [];
    return size(xs);
};

xs = [1, 2, 3];
n = reset(xs);
return size(xs) - n; // 3, because the caller's xs is unchanged
```

A function body's scope has no parent scope, so assignments inside it never reach caller variables, unlike assignments in nested blocks. The number of arguments must match the number of parameters exactly, for both user-defined functions and builtins. A mismatch fails evaluation and validation.

#### Lent parameters

A parameter written `&T` is *lent*: the function only reads it, and a call does not copy it for the function. It is for a parameter only (a result, a field, a local or a `Box` is never a `&T`).

```tersus
fn total(a: &List<Int>) -> Int {
    sum = 0;
    i = 0;
    while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i {
        sum = sum + get(a, i);
        i = i + 1;
    };
    return sum;
};

xs = [1, 2, 3];
return total(xs) + total(xs) + size(xs);   // 6 + 6 + 3: xs is lent each time, and is still xs
```

- **The call does not say it.** `total(xs)` lends `xs` because the function says so; the arguments are checked against `T` (`argument 1 of f: expected List<Int>, got Int`).
- **In the function the parameter is a `T`** that it cannot assign (`a = push(a, 1)` is an error: assign a copy to another variable). Everything that reads it works as usual, and the validator treats it as the value it is, so contracts and proofs are unchanged.
- **What the function needs for itself it copies.** Returning the parameter, giving it to a parameter that is not lent, or using it where a value is taken (`push(a, 9)`) uses a copy, and the caller's value is as it was. A lent parameter given on to another lent one costs nothing.
- **What it saves.** An argument for a parameter that is not lent is copied when the caller uses it again after the call (a list, or a struct or array that owns one) and, held inline, is copied into the function (an array of 1000 words, a struct). A lent one is neither: natively the function reads the caller's words where they are.
- **A function that lends is a different type** from one that does not (`fn(&List<Int>) -> Int` and `fn(List<Int>) -> Int`), since a call is made differently.

See `examples/borrowing.tersus`.

During validation, arguments are symbolic values. Proofs the caller has established about an argument are visible to the callee's input contract, which is how a call such as `spread(x)` can rely on `size(x) > 0` proven at the call site.

## Validation Statements

Validation statements are ordinary statements syntactically, but they are used by the validator rather than by concrete evaluation. Concrete evaluation skips them.

### `affirm`

`affirm` requires a proof to be entailed by the current proof context, and once proved it is added to the context as a fact. That matters when the proof links terms that the heuristics only know are related by arithmetic: after `affirm i = size(l) - 1;`, `get(l, i)` and `get(l, size(l) - 1)` are the same term. The proof may be present directly or match through known equalities, including equalities between the parts of a term: if `s = k` and `size(k) = l` are known then `size(s) + 1` is known to equal `l + 1`, with no `rewrite` needed to say so.

```tersus
x = 5;
affirm x = 5;
```

Proofs use expression-like syntax. Variables refer to symbolic values tracked by the validator. Concrete values can appear directly.

```tersus
affirm size(xs) > 0;
affirm y = (x + 1);
```

When an `affirm` (or a contract check) cannot be proved, the error shows the failed proof in this same syntax:

```
Validation failed: Could not prove: forall j in 0..size(l): get(l, j) = 0
```

### `forall`

`forall` states a fact about every index in a range, for use in `affirm`, contracts and loop invariants. The validator can both prove and use a `forall`. Evaluation ignores it like any validation statement.

```tersus
affirm forall j in 0..size(l): get(l, j) = 0;            // 0 <= j < size(l)
affirm forall j where j >= 0, j < n, j != 2: get(l, j) = 0;
```

- `forall j in lo..hi: P` is shorthand for `forall j where j >= lo, j < hi: P`, so the range is half open.
- `forall j where g1, g2, ...: P` holds `P` for every `j` for which all the guards hold. A guard is any relation.
- To prove a `forall` (in `affirm`, an output contract, or a loop invariant) the validator takes an index that meets the guards, and proves the body for it from everything it knows. So `affirm forall j in 0..3: j < 3;` holds, a narrower range of a known `forall` holds when its bound is known to be within the original one, and an empty range holds for any body. If the body does not follow directly, the validator splits cases. It looks at the instances of known foralls that are missing one guard (a `set` leaves out its index: `j != p`; a `push` leaves out the new element: `j < size(l)`), splits on that guard, and the body must follow in every case (`i = p` and `i != p`, or below, equal to and above); a case can leave another guard missing, so this repeats up to four levels and 300 entailments. Failing that, the index is compared with the indexes the program reads with `get` (below, equal to, and above). That is how a list that grew by one and had two elements replaced is shown to keep its other elements, with no help from the program. The name of the index does not matter. A `forall` cannot be passed to a rewrite rule as an argument.
- A `forall` is used at the elements the program reads. For every `get(l, t)` in the proof context whose list is equal to the list of a `get(l, j)` in `P`, the validator instantiates `j := t`. If the guards hold for `t` it adds `P` for `t` as a fact. So with `forall j in 0..size(l): get(l, j) = 0` and `0 <= i < size(l)` known, `get(l, i) = 0` follows. A `forall` whose `P` has no `get(l, j)` is never used. `get(l, i)` is equal to the proof term `get(l, i)`, so `x = get(l, i)` gives `x = get(l, i)` as a fact.
- `j` is bound in the guards and in `P`. Other names refer to variables as usual, and `forall` does not nest.

### `define`

`define` introduces a proof variable by validating an expression and recording equality between the new proof variable and that expression.

```tersus
define s = size(xs);
affirm s > 0;
```

Proof variables are especially useful in function contracts, where they can be exported from input or output validation sections.

### `rewrite`

`rewrite` applies a named proof-engine rewrite rule or a user-defined axiom/proof rule.

```tersus
rewrite eqToGtZero s;
rewrite myRule x;
rewrite refl x = 5;
rewrite eval y;
rewrite evalAll;
```

Primitive rewrite rules:

- `rewrite refl <proof>`: uses known equalities to derive reflected/substituted proofs, which are added to the context as facts. `affirm` already sees through equalities, so it is rarely needed for that, but it is a legitimate way to put a substituted fact in the context when a proof needs one. A function's output contract exports the facts that are recorded in the context, not what the equalities imply, so `refl` can still add a fact that a caller then receives.
- `rewrite eval <var>`: evaluates builtin-function proofs related to a variable when concrete inputs are known.
- `rewrite evalAll`: attempts builtin evaluation for all available evaluable proofs.
- `rewrite checkGtZero <proof>`: validates and inserts `<proof> > 0` when that proof is already entailed or when the proof term has a concrete positive integer value.
- `rewrite checkRel <relation>`: validates and inserts a relation such as `i < size(l)` when it is already entailed or when both sides have concrete values and the relation holds between them. It fails otherwise. `get`'s contract uses it.

The standard library also provides trusted axiom rules:

- `rewrite eqToLtPlus1 <proof>`: assumes the argument is less than itself plus one.
- `rewrite eqToGtZero <proof>`: exports the argument as greater than zero after its input contract validates through `checkGtZero`.

Unknown rule names parse as user rewrites and fail during validation if no matching rule has been defined.

## Axioms And Proof Rules

User-defined rules are validation-only declarations. Concrete evaluation skips them.

`axiom` registers trusted output proofs. Its input contract is checked at each rewrite site, but its output contract is assumed rather than validated:

```tersus
axiom positiveMeansOne(x) [{
    affirm x > 0;
}] [{
    affirm x = 1;
}];

x = 5;
rewrite eqToGtZero x;
rewrite positiveMeansOne x;
affirm x = 1;
```

`proof` has the same input/output contract shape, but the body must validate when the rule is defined. Only validated exported output proofs are made available to callers:

```tersus
proof keepPositive(x) [{
    affirm x > 0;
}] [{
    affirm x > 0;
}] {
    affirm x > 0;
};

x = 5;
rewrite eqToGtZero x;
rewrite keepPositive x;
affirm x > 0;
```

Rule names share one validation rule namespace. Defining the same name twice fails validation. Rule bodies contain validation statements only.

## Function Contracts

Function definitions can include validation contract sections between the argument list and body:

```tersus
fn name(arg1: Type1, arg2: Type2) -> ReturnType [{ input validation }] [{ output validation }] shrinks e {
    body
};
```

Both contract sections are optional. If one contract section is present, it is treated as the input contract. To specify only an output contract, write an empty input contract first:

```tersus
fn add1(i: Int) -> Int [{}] [{
    affirm return = (i + 1);
}] {
    return i + 1;
};
```

A caller knows a function by its contracts alone. The validator does not read the body of a callee for facts, and it does not run a callee when the arguments are known, so `fn id(n: Int) -> Int { return n; }` promises nothing and `x = id(3); affirm x = 3;` is refused until `id` says `affirm return = n;`. The body is checked against the contracts once, where the function is defined, and can change without changing which callers are valid. (The builtins are the exception: their contracts are in the standard library, and a builtin on known values is evaluated.)

Input contracts are checked at call sites before the function body's exported proofs are instantiated. They are also assumed while validating the function body.

Output contracts are validated after the body has been validated. Proofs involving argument names, `return`, and proof variables defined in the input or output contract can be exported to callers.

Example:

```tersus
fn getFirstWithSize(lst: List<Int>) -> Int [{
    define s = size(lst);
    rewrite eqToGtZero s;
    affirm s > 0;
}] [{
    affirm s > 0;
}] {
    return first(lst);
};

x = [3, 6, 9, 12];
y = getFirstWithSize(x);
affirm y = 3;
affirm s > 0;
```

A contract can contain a `forall` (see `forall` above). In an input contract it is proved at every call, and assumed in the body. In an output contract it is proved after the body, and instantiated for the caller with the actual arguments and the result:

```tersus
fn keep(l: List<Int>) -> List<Int> [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] {
    return l;
};
```

See `examples/forall_facts.tersus`.

### Functions In Contracts

A contract can call a function of the program. The call is checked and used exactly as a call in the code is: its arguments have to meet the input contract of the function, and the value of the call has the facts the function promises about its result.

```tersus
fn double(x: Int) -> Int [{ }] [{ affirm return = x * 2; }] { return x * 2; };

fn quadruple(a: Int) -> Int [{ affirm double(a) > 4; }] [{ affirm return = double(double(a)); }] {
    return a * 4;
};

return quadruple(3);              // double(3) > 4 is proved from double's promise: return = x * 2
```

- **What it knows about the call is the promise of the function**, never the body: `double(a)` is a term with the facts `double(a) = a * 2` that `double`'s output contract gives, as `x = double(a)` in the code would be. A function that promises nothing leaves `double(a)` unknown.
- **The arguments meet the input contract where the call is written.** `affirm pos(a) > 4;` with a `pos` that asks for `x > 0` needs `a > 0` first (`Funct input validation failed: Could not prove: x > 0`), in an input contract, an output contract, an `affirm` or a loop invariant. The function must have been defined before, and a function that may not end (`~`) cannot be called, since it gives no value.
- **The name is a function of the program**: `f(x)`, `Type::f(x)` and `Trait::f(x)` for an impl (the first when the function is not in an impl, the other two as in the code; `<Type as Trait>::f(x)` is written in full). A function with types or sizes (`fn count<T>(s: &V<T>)`) is called without them, as in the code. `x.f()` is not written in a contract.
- **`size`, `first`, `last`, `get`, `set` and `push` on a struct** are the functions of that name that its impl defines (`size(v)` for a `Vec<T>` is `Vec::size(v)`). On a list or an array they are the builtins, as before. In a contract of a trait, on a value of the type `Self`, they are the functions of the trait.
- **What a promise can say of a result stays true for any caller**: the function's output contract is exported with the calls it makes, so a caller learns `count(return) = count(s) + 1` from a function that promises it.

### A linked list in an array

Lists of structs hold data structures without references: the links are indexes. A doubly linked list is a `List<Node>` whose nodes name their neighbours by index, and what the validator can establish about it is that it is well formed. If every link of every node is a valid index, following a link with `get` can never fail, and an operation that keeps that true can be called safely. If the two directions agree, the node after `i` has `i` before it, and the node before `i` has `i` after it.

```tersus
struct Node { value: Int, prev: Int, next: Int };

fn walk(nodes: List<Node>, start: Int, steps: Int) -> Int
    [{
        affirm start >= 0; affirm start < size(nodes);
        affirm forall i in 0..size(nodes): get(nodes, i).next >= 0;
        affirm forall i in 0..size(nodes): get(nodes, i).next < size(nodes);
    }]
    [{ affirm return >= 0; affirm return < size(nodes); }]
{
    cur = start;
    taken = 0;
    while taken < steps [{ affirm taken >= 0; affirm cur >= 0; affirm cur < size(nodes); }] shrinks steps - taken {
        cur = get(nodes, cur).next;
        taken = taken + 1;
    };
    return cur;
};
```

`examples/linked_list.tersus` also inserts a node after another one (a `push` and two `set`s). Its input and output contracts are six foralls: the four range foralls above, and the agreement of the links in both directions:

```tersus
affirm forall i in 0..size(nodes): get(nodes, get(nodes, i).next).prev = i;
affirm forall i in 0..size(nodes): get(nodes, get(nodes, i).prev).next = i;
```

The validator proves that the insertion keeps all six, without help from the program, in a few seconds. The proof is a case analysis: for an arbitrary `i`, its neighbour is compared with `p`, `q` and the new index `n` (about six nested splits), and in each case the facts about the updated elements decide the goal. `examples/rejected/linked_list_link_out_of_range.tersus` is an insertion whose new node links one past its own index, and `examples/rejected/linked_list_link_disagrees.tersus` is one that forgets to point the old next node back at the new node, which keeps every link in range but breaks the agreement.

A forall is instantiated at the indexes the program reads, and an instance that mentions a further `get(l, k)` could be instantiated again at `k` without end. The search therefore instantiates foralls only at indexes that appear in the facts and the goal, or in one instance of a forall (the instance an agreement forall makes at `i` contains `get(l, i).next`, which is used, but the instance made at that is not). A proof that needs a deeper chain of instances needs the middle step as an `affirm`.

## Arithmetic

The validator decides integer comparisons itself, so `affirm`, loop invariants, `checkRel` and `if` guards need no helper rewrites for them. It treats `x - y <= c` facts as a graph and answers a goal by the shortest path between the two sides. The facts come from:

- relations in the context (`i < n`, `a <= b`, and `x != y`, which with `x <= y` or `x >= y` gives the strict relation),
- `x + c` and `x - c` where `c` has a known integer value,
- any term with a known integer value, and
- `size(l) >= 0`, and
- `x * 0`, `x * 1` and `x / 1`,
- `c * x` and `x * c` for any other known constant `c`: it is a node of its own, and whatever the graph says about two nodes `x` and `y` (or `x` and `0`) is said about `c * x` and `c * y` multiplied by `c`, so `n > 0` gives `2 * n > 0` and `n < m` gives `2 * n < 2 * m - 1` (any other product or quotient is an uninterpreted term, folded to a number only when both operands are known). Different constants are different nodes in the graph, so `2 * n` is not compared with `3 * n` there (linear arithmetic below does compare them).

A difference `x - y` of two unknown terms is a term of its own, which the graph says nothing about. A comparison of a difference with `0`, or with another difference that has a side in common, is decided by the other sides, which is what a loop variant such as `n - i` needs: `n - i >= 0` follows from `i <= n`, and `n - (i + 1) < n - i` from `i + 1 > i`. Other facts about a difference, such as `x - y = z` giving `x = y + z`, are left to linear arithmetic.

### Linear arithmetic

What the graph cannot say goes to a second step that solves the arithmetic of the facts as a system of linear equations and inequalities (`Linear`, Fourier-Motzkin elimination with rounding for whole numbers): sums of two variables, multiples of a variable next to other variables, and division by a constant. The step is only run for a goal the graph did not decide, and only when some fact has a `+`, `-`, `*` or `/` that the graph could not take (otherwise the graph is already complete). The goal is entailed when the facts together with its negation have no whole-number solution.

```tersus
fn f(a: Int, b: Int) -> Int [{ affirm a >= 0; affirm b >= 0; affirm a + b <= 10; }] [{ affirm return <= 10; affirm return >= a; }] {
    return a + b;            // a + b <= 10, and a + b >= a because b >= 0
};
fn g(x: Int, y: Int) -> Int [{ affirm x >= 1; affirm 2 * x <= y; }] [{ affirm return >= x; }] {
    return y - x;            // y - x >= 2 * x - x
};
```

- `t = a + b`, `t = a - b` and `t = c * a` (`c` a known integer, `a` anything) are equations between the terms, so `i + j <= n` and `j >= 0` give `i <= n`, and `i + j = n` with `i = m` gives `j = n - m`.
- `t = a % c` for a known `c` is `a - c * (a / c)`: from `0` to `c - 1` for a positive `c`, from `c + 1` to `0` for a negative one. So `n % 4 < 4`, `(n + m) % 2 = 0` when both are odd, and `n % 8 = n` when `n` is from `0` to `7` follow. A divisor that is not a known number but is known to be positive (or negative), such as `size(l)` under `size(l) > 0`, still bounds the remainder, which makes `get(l, i % size(l))` safe for any `i`.
- `t = a / c` for a known `c` other than `1` rounds down: for `c > 0`, `c * t <= a <= c * t + c - 1`, and for `c < 0`, `a <= c * t <= a - c - 1`. So `n / 2 >= 0` and `n / 2 < n` follow from `n > 0`, `(i + j) / 2` is between `i` and `j` when `i < j`, and `n / 2 * 2 <= n <= n / 2 * 2 + 1` (but not `n / 2 * 2 = n`).
- Whole numbers: `2 * x <= 1` gives `x <= 0`, and `2 * x = 2 * y + 1` has no solution (the facts contradict each other, so everything after it is vacuously true).
- A product of two unknowns, `x * y`, and a division by an unknown, stay opaque. The step gives up, proving nothing, on a system of more than 300 constraints after elimination, so a long chain of sums with a goal that does not follow is slower and then refused.

```tersus
s = 3;
affirm s > 0;           // no rewrite eqToGtZero needed
y = s + 1;
affirm y != s;
```

`*` and `/` bind tighter than `+` and `-`: `2 + 3 * 4` is `14`. `/` rounds down (`-7 / 2` is `-4`). Integer literals can be negative (`x = -4;`, `[-1, 2]`, `3 - -2`). Dividing needs a divisor the validator can show is non-zero, checked like the index of `get`; evaluating `1 / 0` is an error, and so is a result that does not fit in `Int` (see Integers).

```tersus
fn average(total: Int, count: Int) -> Int [{ affirm count > 0; }] [{ }] {
    return total / count;
};
```

See `examples/arithmetic.tersus`.

A goal `x != y` is proved when `x < y` or `x > y` is, and a fact `x != y` is used the other way: when `x <= y` is known too, `x < y` is, which an `i != n` loop condition needs to keep `i` below `n`. Contradictory facts, such as the guard of an unreachable branch, prove every comparison.

## Arrays

`Array<T, N>` is the builtin for a sequence of `N` elements of one type. The size is a constant and part of the type, and the array is held inline, wherever it is made: in the frame of the function that has it, with no pointer to it, so making one costs no allocation and a copy is a copy of the words. The elements are any value that has a size: `Int`, `Bool`, a list, a struct, an enum, a `Box`, or another array (see Elements that own something).

```tersus
a = array(4, 0);          // #[0, 0, 0, 0]: four copies of 0, an Array<Int, 4>
b = #[5, 6, 7];           // an array written out (the elements are literals), an Array<Int, 3>
c = set(a, 1, 9);         // a new array, #[0, 9, 0, 0]; a is unchanged
return get(c, 1) + size(b) + first(b);
```

- **The size is a constant.** `array(n, x)` makes `n` copies of `x`, and `n` has to be a number or arithmetic on numbers (`array(2 * 3, 0)`), so that the compiler knows how much room the array takes. `n = 3; array(n, 0)` is an error. The arithmetic is the program's, so each step has to fit in an `Int` and a divisor cannot be 0 (`array(9223372036854775807 + 1 - 9223372036854775807, 0)` is refused for the overflow, not folded to 1). The size cannot be negative, and an array is limited to 8192 words (64 KB), counting the arrays inside it, since it lives in a frame. `array` cannot be used as a value (`h = array;`).
- **The type says the size, and so does the validator.** The validator knows `size(a) = N` for every local of the type `Array<T, N>` wherever it came from (a parameter, a result, a loop that sets it, a row of a grid), so a contract or a loop invariant never has to repeat it, and `get(a, 3)` on an `Array<Int, 4>` needs no proof.
- **The same operations as a list, minus `push`.** `size`, `get`, `first`, `last` and `set` work on an array with the same contracts and facts (an index in range for `get` and `set`, an array that is not empty for `first` and `last`; `set` gives a new array, in place on the local when the result is assigned back to it). `array(n, x)` also says `forall j in 0..n: get(return, j) = x`. `=` and `!=` compare two arrays of the same type structurally. An array has no `push`: its size never changes.
- **Arrays nest.** `Array<Array<Int, 3>, 2>` is two rows of three, six words in one block. `get(m, 1)` is a row (a copy of it), and `set(m, 1, row)` replaces one.
- **A value, not a reference.** Giving an array to a function gives the function a copy, so it cannot change the caller's array, and a function returns an array by value.

A function names the size in the types of its parameters and result:

```tersus
fn dot(a: Array<Int, 5>, b: Array<Int, 5>) -> Int {
    total = 0;
    i = 0;
    while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i {
        total = total + get(a, i) * get(b, i);
        i = i + 1;
    };
    return total;
};

fn squares() -> Array<Int, 5> {
    out = array(5, 0);
    i = 0;
    while i < 5 [{ affirm i >= 0; affirm i <= 5; }] shrinks 5 - i {
        out = set(out, i, i * i);
        i = i + 1;
    };
    return out;
};

x = squares();
dot(x, x);                   // fine
// dot(x, array(4, 1));      // rejected: argument 2 of dot: expected Array<Int, 5>, got Array<Int, 4>
```

See `examples/arrays.tersus`. Natively an array is `N` 8-byte words in the slot of its local (an element that is an array is its words, in line), an array given to a function is its address and the function copies it, and an array that a function returns is written into room the caller gives it. A result is printed as a list is, `[0, 9, 0, 0]`.

The size can be written `?`, or left out (`Array<Int>` is `Array<Int, ?>`), for an array whose size the type does not say. Such an array is *unsized*: it is not a value of its own, and can only be used behind a pointer that carries the size. The pointer is `Box`: `Box<Array<Int>>` is the address of the elements and how many there are, and it is the type of an array on the heap whose size the program works out.

```tersus
fn total(a: Box<Array<Int>>) -> Int [{ define s = size(a); affirm s >= 0; }] [{ }] {
    sum = 0;
    i = 0;
    while i < size(a) [{ affirm i >= 0; affirm i <= size(a); }] shrinks size(a) - i {
        sum = sum + get(a, i);
        i = i + 1;
    };
    return sum;
};

n = 3 + 2;
five = Array::boxed(n, 2);          // n is any Int that is not negative: Box<Array<Int>>
fixed = Box::new(#[1, 2, 3, 4]);    // Box<Array<Int, 4>>: the size is in the type
return total(five) + total(fixed);  // 20
```

- **`Array::boxed(n, x)`** makes `n` copies of `x` on the heap, with an `n` that the program works out (`array(n, x)` needs a constant, since it is held inline). It has the contract of `array`: `n` must not be negative, the size is `n`, and every element is `x`. It is written as a call and cannot be used as a value.
- **`Array::empty()`** is the Box of an array of no elements (`size` 0), of the element type that the program decides: no element is needed, since there is none. It is how an empty list is made without a value of its type, and is written as a call.
- **A Box of an array of a size is a Box of an array of any size where one is wanted** (`Box<Array<Int, 4>>` is given to a parameter of type `Box<Array<Int>>`): the unsizing conversion, which keeps the value and makes the size part of the Box. It is made where a value is given to something that has a type: an argument, a field of a struct or enum, a returned value, and a variable that already has the type. It does not go the other way (`Box<Array<Int>>` is not a `Box<Array<Int, 3>>`), since the size is then only known when the program runs.
- **What the validator knows.** A `Box<Array<T, N>>` has the size `N` from its type, as an array has, and the size carried by a `Box<Array<T>>` is the `size` of it, so a function over any size says what it needs of it in a contract (`get(a, 0)` needs `size(a) > 0`) and the caller proves it.
- **What it holds.** The elements are any value that has a size, as for any array.

An array is a value like a number, so it can be a field of a struct or an enum and an element of a list (`examples/array_data.tersus`): `struct Image { id: Int, pixels: Array<Int, 4> }`, `enum Tile { Row { cells: Array<Int, 2> }, Block { id: Int, cells: Array<Int, 4> } }`, `List<Array<Int, 2>>`. Reading a field or an element gives a copy of the array, which the program can change without changing the struct or the list (`set` gives a new array), and a struct is updated around a new one with `..base`. The array's words are in line, in the struct (the variants of an enum are as wide as their fields) or one after another in the list, so no array is allocated apart.

### Size parameters

A function can be written for arrays of any size. `fn dot<n>(...)` declares a size `n` (any number of them: `fn grid<rows, columns>(...)`), which a call gives and which the types of the parameters use:

```tersus
fn dot<n>(a: Array<Int, n>, b: Array<Int, n>) -> Int {
    total = 0;
    i = 0;
    while i < n [{ affirm i >= 0; affirm i <= n; }] shrinks n - i {
        total = total + get(a, i) * get(b, i);
        i = i + 1;
    };
    return total;
};

return dot(#[1, 2, 3], #[4, 5, 6]) + dot(#[2], #[5]);   // 42
```

- **A call does not write the sizes.** The arguments decide them: `dot(#[1, 2, 3], ...)` makes `n` 3, every other use of `n` has to agree (`dot(#[1, 2], #[1, 2, 3])` is rejected: `argument 2 of dot: expected Array<Int, 2>, got Array<Int, 3>`), and a size that no argument decides is an error (`fn f<n>() -> Int` cannot be called). The sizes are the last parameters of the function, so a function value cannot have them, and `h = dot` is an error (a function with sizes is called). A function of an impl can have them (`impl S { fn f<n>(a: Array<Int, n>) -> Int { ... } }`), after those of the impl, but not one of an impl of a trait yet.
- **A size is an `Int` in the function.** The body and the contracts read it as a variable (`i < n`, `affirm n > 0`), and `array(n, x)` makes an array of it, with the size `n` in its type (the result type can say so: `-> Array<Int, n>`). It cannot be assigned, and a size in a type takes no arithmetic: `array(n + 1, 0)` is an error, since a size is a constant or a size parameter, which also keeps the number of copies finite.
- **It is validated once.** The validator knows of `n` that it is the size of every array whose type says `n` (`size(a) = n`), as it knows the constant of an array of a size, and nothing else: a caller proves what the contract asks of `n` for its own size. Callers know the function by its contract, as for any function.
- **Native code is made for each size.** An array is held inline, so a program that runs has a copy of the function for each list of sizes it is called with (`dot<3>` and `dot<1>` above), with the sizes replaced by the constants (`MirMono`). A size that a function passes on to another it calls is one of its own sizes, which the copy of it has replaced.

The limit of an array held in a frame (8192 words) is checked for a size that is a constant when the program is checked, and for one that comes from a size parameter when native code is made for that size (`tersus run` has no frame): `fn f<n>(a: Array<Int, n>) { b = array(n, a); ... }` called with `array(8192, 0)` builds an array of 8192 arrays of 8192 words, which `tersus build` refuses, naming the copy of the function (`f<8192>`).

See `examples/array_sizes.tersus`.

### Type parameters

A function can also be written for any type. A name that starts with a capital letter between the `<>` is a type; any other is a size:

```tersus
fn head<T>(items: &List<T>) -> T [{ define s = size(items); rewrite eqToGtZero s; affirm s > 0; }] [{ }] {
    return get(items, 0);
};

fn pair<T>(a: T, b: T) -> Array<T, 2> {
    return set(array(2, a), 1, b);
};

return head(push([], 40)) + size(head(push([], push([], 1))));   // head of a List<Int>, and of a List<List<Int>>
```

- **The arguments decide the types.** `head(push([], 40))` makes `T` an `Int`, the other `T` a `List<Int>`; every use of `T` in the signature has to agree (`pair(1, true)` is `argument 2 of pair: expected Int, got Bool`). A type that nothing decides, as `nil()` for `fn nil<T>() -> List<T>`, is an `Int`, as the element of `[]` is when nothing decides it. A call does not write the types, and a function with type parameters is called, not named (`h = head` is an error).
- **The function knows nothing of `T`.** It is validated once, with `T` a type of its own: a value of it can be passed around, kept in a list, an array or a `Box`, and compared with `=`, and `a + 1` for a `T` is an error. Contracts can speak of the values (`size(items)`, `get(items, 0)`) as usual.
- **A function that calls itself** gives each of its type parameters as it is, in any order, or a type that does not use them (`f(b, a, n - 1)`, `f(1, n - 1)`). `f(push([], a), n - 1)` is an error: native code has a copy of the function for each type, and a type that grows at each call would need one for each depth.
- **Not a function.** A type parameter is a type of value: `id(inc)` for a function `inc` is an error, since native code has no copy of a function for it.
- **Native code is made for each type.** A program that runs has a copy of the function for each list of types (and sizes) it is called with, `head<Int>` and `head<List<Int>>` (`MirMono` finds them by matching the types of the parameters with the types of the arguments and of the local that gets the result), and so a `T` that owns something (a list) is moved, copied and freed in the copy for it, and one that does not is a plain copy.
- **Not yet**: type parameters of an enum, or of a function of an impl of a trait. A struct can have them (see below), and so can a function of an impl that is not of a trait.

See `examples/type_parameters.tersus`.

### Structs with types

A struct can have types as well as sizes: `struct Pair<T>` is a struct for each type, and `struct Vec<T, n>` one for each type and size. A parameter that starts with a capital letter is a type and any other is a size, as for a function; a type gives them in the order the struct declares them, and so does a literal.

```tersus
struct Pair<T> {
    a: T,
    b: T,
};

fn swap<U>(p: &Pair<U>) -> Pair<U> {
    return Pair<U> { a: p.b, b: p.a };
};

struct Holder<T> {
    items: Box<Array<T>>,
    len: Int,
};

q = swap(Pair<List<Int>> { a: push([], 1), b: push(push([], 2), 3) });
return size(q.a);   // 2
```

- **Each list of types and sizes is a struct of its own.** `Pair<Int>` and `Pair<Bool>` cannot be compared or given for each other (`argument 1 of f: expected Pair<Int>, got Pair<Bool>`), and the fields have the types (`field b of Pair<Int>: expected Int, got Bool`). A struct written with none (`fn f(p: Pair)`) is an error, as is a type that is a function.
- **A function with type parameters takes any of them**: `swap(Pair<List<Int>> { ... })` makes `U` a `List<Int>`, as it does for a list (`MirMono` matches the types of the instance's arguments), and native code is made for each type, so a `Pair<List<Int>>` owns its lists and is moved, copied and freed as a struct with them.
- **It is an ordinary struct otherwise**: held inline, read with `.`, updated with `..base`, held in a `Box`, a list or an array, compared, and printed as `Pair { a: ..., b: ... }`. It may hold itself in a `Box` or a list (`next: Box<Node<T>>`), not by value. A field can be a `Box<Array<T>>` and a contract can speak of it (`size(return.items) = n`), which is the shape of a list that is a library type.
- **What it cannot be yet**: an enum with parameters, a size of `?`, and a literal that leaves the types out (`Pair { a: 1, b: 2 }`): the types are written. Their functions are written in an `impl<T>` (below).

See `examples/generic_structs.tersus`.

### Impl for a struct with parameters

An `impl` for a struct with types and sizes names them after `impl`, and gives them to the struct the way a type does:

```
struct Pair<A, B> { a: A, b: B };

impl<X, Y> Pair<X, Y> {
    fn make(x: X, y: Y) -> Self { return Self { a: x, b: y }; };
    fn first(self: &Self) -> X { return self.a; };
    fn flip(self: &Self) -> Pair<Y, X> { return Pair<Y, X> { a: self.b, b: self.a }; };
    fn again(self: &Self) -> Self { return Self::make(self.a, self.b); };
};

q = Pair::make(push([], 4), true).flip();     // Pair<Bool, List<Int>>
return size(q.b);                             // 1
```

- **Each function has the parameters of the impl** after its own, so `first` is a function `fn first<X, Y>(...)` that the arguments decide, and a copy of it is made for each list of types and sizes it is called with (`Pair<List<Int>, Bool>` and `Pair<Int, Int>` each get theirs). The names of the parameters belong to the impl: `impl<U> Box2<U>` is as good as `impl<T> Box2<T>`.
- **`Self` is the struct with the parameters of the impl** (`Pair<X, Y>` here): in the signatures, the literal `Self { ... }`, and `Self::make(...)`. A size of the impl (`impl<n> Packet<n>`) is a value in the body and the contracts, as it is for a function.
- **A call is written as for any impl**: `x.first()`, `Pair::make(1, true)` and `Pair::first(x)`, with the types of the instance deciding which copy, and a struct that is not given the types of the impl is a type error. An impl for a struct that has parameters has to name them (`impl Pair { ... }` is a parse error), and an impl with parameters for a struct that has none is one too.
- **A trait can be implemented for one** (`impl<T> Sequence<T> for Vec<T>`, see Traits And Impls). Not yet: a bound on a parameter (`T: Trait`).

### A list written in Tersus

The pieces above are enough to write a growable list as a library: a `Box` of an array that holds the elements, and the number in use, with an invariant that every function relies on and the trait of a sequence that it implements.

```
struct Vec<T> {
    data: Box<Array<T>>,
    len: Int,
} invariant [{ affirm len >= 0; affirm len <= size(data); affirm size(data) >= 1; }];

impl<T> Vec<T> {
    fn new(filler: T) -> Self [{ }] [{ affirm return.len = 0; }] {
        return Self { data: Array::boxed(4, filler), len: 0 };
    };
};

impl<T> Sequence<T> for Vec<T> {                  // Sequence is the trait above, with size, get and set (push is Growable's)
    fn size(self: &Self) -> Int [{ }] [{ affirm return = self.len; }] { return self.len; };
    fn get(self: &Self, i: Int) -> T [{ affirm i >= 0; affirm i < self.len; }] [{ affirm return = get(self.data, i); }] {
        return get(self.data, i);
    };
    ...
};

v = Vec::new(0).push(5).push(6);
return v.get(1) + size(v);                      // 8
```

`push` writes into the array while `len < size(data)`, and otherwise makes an array twice the size, copies the elements over in a loop and writes the new one, so a Vec is native code with no support from the runtime that a list does not have (`examples/vec.tersus` has all of `new`, `size`, `get`, `set`, `push` and `pop`).

- **The invariant keeps `0 <= len <= size(data)` and a capacity of at least 1.** It is proved where a Vec is made (the literals in `new`, `set`, `push` and `pop`) and assumed for every Vec a function is given, so no function asks for it. `get` asks for an index in use (`affirm i < self.len;`), so `v.get(1)` on a Vec with one element is refused (`Could not prove: i < self.len`), and so is `pop` of an empty one (`Could not prove: self.len >= 1`).
- **A loop that pushes says what it keeps in terms of `size`**: `affirm size(v) = i;`, since `push` promises `size(return) = size(self) + 1` and the invariant says the rest.
- **The elements may own things.** The array clones the filler into every slot, `set` and the growth move and free what they replace, and a `Vec<List<Int>>`, a `Vec<Vec<Int>>` or a Vec of structs that own lists is freed once (the native tests run these with the checks of the runtime on).
- **What it is not yet**: a list. There is no list literal or `for` over it, no function over any `Sequence` (it takes a `Vec`), and `=` compares the unused slots of the arrays too.

**The prelude.** The traits `Sequence` (`size`, `get`, `set`) and `Growable` (`push`, for the sequences that can grow, which an array cannot) are in `lib/prelude.tersus`, and every program that mentions `Sequence` or `Growable` has them in front of it, so a struct that implements it needs nothing declared. A program that declares a `Sequence` or a `Growable` of its own does not get the library, and a program that does not mention it is unchanged. The library is parsed before the program with the declarations it makes known to it, so the line numbers in an error are the program's own, and it is checked and validated with the program.

`Vec` itself is not in the prelude: a `List` is the same thing (see Lists In Native Code), with the literals, the methods and the proof facts of a list, so a program uses a list. `examples/vec.tersus` writes the library out in full as a program of its own: it is what the features of this part of the guide are for.


### Lists In Native Code

A `List<T>` is checked and validated as a list, and run by the executor (`tersus run`) as a list. Native code (`llvm`, `build`) has no list of its own: a list is a struct of a Box of an array and a count, written in Tersus (`lib/lists.tersus`), and a program is changed to use it after it is validated.

```
struct StdList<T> {
    data: Box<Array<T>>,
    len: Int,
} invariant [{ affirm len >= 0; affirm len <= size(data); }];

fn stdListPush<T>(l: StdList<T>, x: T) -> StdList<T> [{ }] [{ affirm return.len = l.len + 1; affirm get(return.data, l.len) = x; affirm forall j in 0..l.len: get(return.data, j) = get(l.data, j); }] { ... };
```

- **What a list operation becomes** (`MirLists`): `size(l)` reads `len`; `get`, `first` and `last` read the element out of the array where it is, so a part that is only read is not copied; `push` and `set` are calls of `stdListPush` and `stdListSet`, which change the array where it is when nothing else holds the list; a list written as `[1, 2]` is a call of `stdListNew` and one of `stdListPush` for each element; an empty list holds an `Array::empty()` and allocates nothing. A `List<T>` in a type is a `StdList<T>`, in a struct, an enum, an array, a Box or another list. A push into a full array makes one of twice the room and four more and moves the elements over, so a list built by pushing is built in time and room in proportion to its length.
- **Comparing and printing** a list are done as a list is: `=` compares the first `len` elements and not the room that is left, and the result of a program that is a list prints as `[1, 2, 3]`. (The runtime knows a `StdList` by its name.)
- **What is proved, and where.** The proofs about a program's lists are those of lists: the validator never sees the struct. The library is validated on its own, with contracts that say what a list does (`get` gives what `set` put, `push` adds one at the end and leaves the others, and the size changes by the right amount), so the form that native code uses has been shown to do what a list does. That the change itself is right is checked by running: every test program that has a list is built and run, and its output has to be the executor's.
- **Reserved names.** A program may not declare a struct, an enum or a trait named `StdList`, or a function whose name starts with `stdList` (`Type error: stdListNew is reserved`), since native code calls the functions of the library by those names.
- **See it** with `tersus owned <file>`, which prints the program after the change, with the moves, copies and frees: `l = push(l, i)` is `_1 = call stdListPush<Int>(move _1, _2)`.
- **Not changed**: the executor runs the list as a list, and the checker, the validator and the proof engine know lists as they did. A struct with `size`, `get`, `set` and `push` of its own (`Vec`, see A list written in Tersus) is a program's own type, and is used the same way.

### Structs with sizes

A struct can have sizes too: `struct Packet<n>` is a struct for each size, and a type gives them, as `Packet<4>`. A field can use the size, or hold another struct of the same size:

```tersus
struct Packet<n> {
    id: Int,
    body: Array<Int, n>,
};

struct Frame<n> {
    kind: Int,
    packet: Packet<n>,
};

fn total<m>(p: Packet<m>) -> Int {
    sum = p.id;
    i = 0;
    while i < m [{ affirm i >= 0; affirm i <= m; }] shrinks m - i {
        sum = sum + get(p.body, i);
        i = i + 1;
    };
    return sum;
};

a = Packet<3> { id: 7, body: #[1, 2, 3] };
return total(a) + total(Packet<1> { id: 1, body: #[10] });   // 13 + 11
```

- **Each size is a type of its own.** `Packet<3>` and `Packet<2>` cannot be compared or given for each other (`argument 1 of first: expected Packet<3>, got Packet<2>`). The sizes are written in a type and in a literal (`Packet<3> { ... }`, `Packet<m> { ... }` in a function that has the size `m`), as many as the declaration has, each a number or a size of the function. A struct with sizes written with none (`fn f(p: Packet)`) or with `?` is an error.
- **A function with sizes takes any of them.** `fn total<m>(p: Packet<m>)` is called with a `Packet<3>` and its `m` is 3, as it is for an array; the size is decided by the arguments.
- **It is an ordinary struct otherwise**: held inline (a `Packet<4>` is the words of its fields), read with `.`, updated with `..base`, held in a `Box` or a list, compared, and printed as `Packet { id: 7, body: [1, 2, 3] }`. A struct with sizes may hold itself in a `Box` (`next: Box<L<n>>`), not by value.
- **What it cannot be yet**: an enum with sizes, methods and traits for a struct with sizes (`impl Packet<4>`), a size of `?` (a struct whose last field has a size that a `Box` carries, as `Box<Array<T>>` does), and type parameters (`struct Packet<T, n>`).
- **How it is made.** A struct with sizes is declared once and is a struct of its own, named by the sizes (`Packet<4>`), for each list that the program uses: the checker makes it the first time the name is looked at, the lowering declares the ones the program mentions (`completeInstances`), and a function with sizes is made for each size by `MirMono`, which renames the structs it uses with the sizes put in. The executor treats `Packet<n>` and `Packet<3>` as the one struct `Packet`.

See `examples/sized_structs.tersus`.

### Elements that own something

An element can be a list, a struct, an enum, a `Box`, or an array of those. An array that holds one owns it as a struct owns its fields: it is moved with the array, copied with it (a copy shares nothing with the original), and freed with it, and replacing an element frees the one it held.

```tersus
a = array(3, push([], 1));            // Array<List<Int>, 3>: three lists, each [1]
a = set(a, 1, push(push([], 2), 3));  // the second is replaced, and the list it held is freed
l = get(a, 0);                        // a copy of the first
l = push(l, 9);                       // does not change a
return a;                             // [[1], [2, 3], [1]]
```

- **`array(n, x)` copies `x` into each slot** (a list or a struct that owns one is cloned `n` times); `set(a, i, x)` takes `x`. `get`, `first` and `last` give a copy of the element, as for a list. Equality and printing go through the elements.
- **A literal is for Int, Bool and arrays of them**: `#[[1], [2]]` is an error (make the array with `array(n, x)` and `set`), since a literal is a constant that is written out.
- **Not a function**: an array of functions is an error.
- **Frame limit.** The 8192 words an array held in a frame can have are counted in words of the elements (`Array<P, 3000>` for a struct of 3 words takes 9000).
- **On the heap.** `Array::boxed(n, x)` and a `Box<Array<T>>` hold elements of any of these types too; the Box frees them when it is freed.

## Current Limitations

- No `break` or `continue`. `for` goes through a range or the elements of a list, not by a step other than `1` or backwards.
- Termination is checked for loops and for a function that calls itself, but only for a single `shrinks` value: an integer that counts to a bound, or a struct or enum value that loses a field at each step. Nothing else is a variant: not a lexicographic pair of integers, and not the length of a list that shrinks (`size(l)` is an integer that can be used, but one that shrinks only if the program says so). The intended direction is a termination proof written out with `affirm`s, of which `shrinks` is the sugar (see Termination). A program that cannot show termination is declared `~`, can loop forever, and `run` will not return. Validation does not hang on this: it never runs a function of the program (see Function Contracts).
- A condition is one relation or boolean: there is no `&&` or `||`, so a guard with several parts is nested `if`s or sequential early returns (see `parse` in `examples/packet_parser.tersus`). The intended form is short-circuit sugar for nested `if`s, with a boolean value that a proof can mention left out.
- An output contract cannot depend on which variant is returned, so "if `parse` returns `Parsed::Message`, its payload fits in the buffer" cannot be stated to a caller. The intended form is an implication in contracts, `affirm return is Parsed::Message => ...;`, proved for each way out of the function and assumed by a caller once it knows the variant.
- No declarations separate from assignment.
- `Array<T, N>` is a second sequence type beside `List<T>`: an array is held inline with its size in the type (or on the heap, in a Box), and `h = size;` is the function for lists, so `h` cannot be applied to an array. An array literal holds literals only (`#[1, 2]`); an array of variables is made with `array` and `set`. A list is what `push` makes, and in native code it is made of an array (see Lists In Native Code).
- No strings or floats yet (see DATA_MODEL.md). Lists can be read with `get`, extended with `push` and updated with `set`, which return new lists. List literals contain literals only, so a list of variables is built with `push`.
- Arithmetic is linear (see Arithmetic): comparisons, sums and differences, multiples by a known constant and division by a known constant. A product of two unknowns, and a division by an unknown, are evaluated when their operands are known, but otherwise opaque. `x / c` is rounded down, so `x / c * c = x` is not known.
- The size of a list is known for a literal, after `push` and `set`, and after a loop that grows it by a constant amount per iteration of a counter (see Inferred invariants). A list that a loop builds in a way that is not a constant per iteration needs its size in the invariant.
- `rewrite refl` adds a substituted copy of every fact, so it gets slow as the number of known facts grows (inside a loop body it took over a minute in one list-building program). `affirm` and loop invariants do not need it, so use it sparingly and on a context that is not large.
- `forall` is only used at the elements a program reads with `get`; a body without a `get(l, j)` is never instantiated, and there is no `exists`. When a proof needs an element the program does not read, mention it in an `affirm` (see How Validation Works).
- No block comments; only `//` line comments.
- Function bodies are evaluated with their argument bindings, the standard library, and the top-level functions defined before them. They do not capture other variables (no lexical closures), a function can call only itself and the functions defined before it, and a function name can be defined only once.
- Traits are checked and called, not used as types: a function cannot take "any type that implements `Measure`" (a type parameter has no bounds yet), so `Measure::size(x)` is `Type::size(x)` for the type of `x`, decided when the program is checked. Impls are for structs and enums only, with no default bodies, no associated types or constants, and the contracts of a trait speak of `Self` only through the functions of the trait. A trait does not say whether its functions end, so a generic function over a trait would have to assume the worst, which is why generics are not in this step.
- The CLI runs one file at a time and has no REPL or multi-file programs; the one library there is, the prelude with the trait `Sequence`, is put in front of a program that mentions it.
- The validator does not follow a call of a function that is a value: a function that takes `g: fn(Int) -> Int` and calls `g(n)` is refused (`Function object not validated`), though it type checks and runs. A function can still be passed around, stored in a list or a struct, and returned.
- The source file is read in the encoding of the locale, so a program with a letter that is not ASCII in a name (the parser accepts any letter) needs a UTF-8 locale to load.
- A program has no input or output: it computes and returns one value, which `run` and an executable print.
- Native code (`build`) copies an argument that is passed to a function and used again afterwards, and recursion that is very deep, or a recursive value that is very long to free or copy, can overflow the stack of the process (see the roadmap in `README.md`).
