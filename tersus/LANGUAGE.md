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
stack run -- run program.tersus     # validate, then evaluate and print the return value
```

`run` never evaluates a program that fails validation. A program that does not `return` prints nothing. Integers print as digits, lists as `[1, 2]`, and booleans as `true`/`false`. Pass `-` instead of a file name to read the program from standard input.

## How Validation Works

Checking every proposition a real program could need is not feasible, so validation is a bounded search that is sound but incomplete:

1. **Heuristics do the common work.** The validator tries, without any help from the program: equalities between terms and their parts, integer comparisons (see Arithmetic), evaluation of builtins on known values, `forall` facts at the elements the program reads, the facts that function contracts export, and the invariants of a loop that follow from how its counters and lists start and change (see Inferred invariants). Each search is bounded: a fixed number of `forall` instantiation rounds, a fixed number of case splits, and a fixed budget of statements when a call with known arguments is evaluated.
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

## Types

Every value has a type, and programs are type checked before they are validated:

- A declared struct or enum, such as `Node` or `Shape`,
- `Int`, `Bool`, and `List<T>` for any element type `T`, such as `List<Int>`, `List<Bool>` or `List<List<Int>>`. All the elements of a list have the same type, and `[]` takes its element type from how it is used. A variable holding `[]` has one type for its whole life, so `e = []` cannot be pushed an `Int` once and a list later,
- `fn(Int, Int) -> Int` for a function value.

A function writes the type of each parameter and of its return value. A local variable takes the type of its first assignment, and assigning a different type to it later is an error. Types exist only for checking: validation and evaluation never look at them.

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

The builtins have these signatures: `size : fn(List<a>) -> Int` (`a` is any one type, chosen anew at each use), `first` and `last : fn(List<a>) -> a`, `get : fn(List<a>, Int) -> a`, `push : fn(List<a>, a) -> List<a>`, `set : fn(List<a>, Int, a) -> List<a>`, `+ - * /` on `Int`, `=` and `!=` on two values of the same type (any type but a function), and `< <= > >=` on `Int`. A mismatch is reported before anything runs:

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
- Structs are values. Nothing is mutated: `Node { next: 3, ..n }` is a new struct and `n` is unchanged. There is no field assignment, so write `n = Node { next: 3, ..n };`.
- `=` and `!=` compare structs field by field, and a struct can hold any type, including lists and other structs declared earlier. A struct cannot contain itself yet.
- Field reads and literals work in proofs too, so a contract can say `affirm return.next = target;`.
- The validator treats a literal as a constructor applied to its fields. Reading a field of a literal gives the field (`Node { next: 3, ..n }.value` is `n.value`), two equal constructions agree field by field, and so an update's other fields are known without a `forall`. It does not yet know that a struct equals a rebuilt copy of its own fields (`Node { value: n.value, prev: n.prev, next: n.next } = n`), so state that with the fields you need.

```tersus
fn relink(n: Node, target: Int) -> Node [{ }] [{ affirm return.next = target; affirm return.value = n.value; }] {
    return Node { next: target, ..n };
};
```

Lists of structs work like any list: `set(nodes, i, Node { next: 5, ..get(nodes, i) })` changes one element, and the `forall` frame of `set` says the others are unchanged. See `examples/structs.tersus`.

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
- Enums can contain themselves: `enum Tree { Leaf, Branch { left: Tree, value: Int, right: Tree } }`, and a function over a tree recurses on its parts. (A compiled Tersus would have to put such fields behind a pointer; the language does not mention it.)
- Equality `=` is structural, and `x != y` is proved for values built by different variants or with different fields.
- Fields of an enum value are read after a **cast** to the variant that has them: `(s as Shape::Circle).radius`. Several variants may have a field of the same name, so `s.radius` alone does not say which variant is meant, and it is a type error on an enum value (it works on a struct). The cast has the type `Shape::Circle`, which can be written as a parameter type (`fn r(c: Shape::Circle)`), and a value of that type can be passed where a `Shape` is wanted but not the other way round.
- A cast is checked by the validator and does nothing when the program runs. The validator demands the proof that the value is that variant, the way `get` demands an index in range: an `affirm s is Shape::Circle;` in a contract, an earlier `affirm`, an `if s is Shape::Circle`, or a value built as a `Shape::Circle`. A cast it cannot prove is a validation error (`Could not prove: value is Shape::Circle`). If a wrong cast reaches execution anyway, the behaviour is undefined: this interpreter does not check the cast, and reading a field that the value does not have is an error that says so. What a program computes never depends on the proofs, so proofs could be used to speed a program up but not to change what it does.
- A contract can demand a variant without a cast, `[{ affirm o is Opt::Some; }]`, and the caller has to show it. Updating a variant, `Shape::Rect { width: 10, ..s }`, copies the other fields from `s as Shape::Rect`, so it asks for the same proof.

See `examples/enums.tersus`.

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

- Arithmetic: `*`, `/`, `+`, `-`
- Relations: `=`, `!=`, `<`, `>`, `<=`, `>=`

Infix operators bind in three levels, tightest first: `*` and `/`, then `+` and `-`, then the relations. Each level associates left, so `return = n + 1` reads as `return = (n + 1)` and `a + 1 < b * 2` as `(a + 1) < (b * 2)`. Use parentheses when the intended grouping is not clear.

## Builtins

The standard library seeds these builtin functions:

- `size(list)`: returns the length of a list.
- `first(list)`: returns the first element of a non-empty list.
- `last(list)`: returns the last element of a non-empty list.
- `get(list, index)`: returns the element at `index`, counting from 0. The index must satisfy `0 <= index < size(list)`.
- `push(list, x)`: returns a new list with `x` added at the end. Lists are values, so the argument list is unchanged.
- `set(list, index, x)`: returns a new list with the element at `index` replaced by `x`. The index must satisfy `0 <= index < size(list)`, and the argument list is unchanged.
- `+` and `-`: integer arithmetic.
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

`return` evaluates an expression, stores it as the return value of the program or function call, and ends it. Statements after a `return` do not run, including when the `return` is inside a nested block, `if` or `while`.

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

This is sound but incomplete. Facts a branch derives about values that existed before the `if`, and that the other branch does not also derive, are dropped, so re-derive them after the `if` when you need them.

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

The validator cannot join a branch that returned with one that did not, because the statements after the `if` do not run on the path that returned. Instead it validates each path to the end of the function separately: the then-branch followed by the rest of the function, and the else-branch followed by the rest of the function, each assuming its own condition. A path that returns ends there, so the rest of the function is only validated under the paths that reach it. In the example above, `first(lst)` is checked assuming `size(lst) > 0`, and the guard `if size(lst) > 0 { return fallback; };` would be rejected because the code after it only knows `size(lst) <= 0`.

The paths are then joined. If they all return, the return value becomes one new value, and a fact about it (for example an output contract `affirm return > 0;`) is known only if every returning path established it. If some path reaches the end without returning, there is no return value: a program may do that, and a function that does so is rejected with `Return value not found in top scope`.

Because each path validates the rest of the function again, an `if` whose branches both fall through and contain a `return` somewhere inside doubles the work for the statements after it. Ordinary guard clauses do not, since the path that returns has nothing left to validate.

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

The invariants of a loop that does not `return` are completed by the validator. For each variable the body assigns that is a number or a list when the loop is entered, it starts from what is known on entry: a number is at least and at most its value there, the size of a list likewise, and two of these differ by what they differed by on entry. It keeps a candidate only if the body establishes it again, assuming the ones that are left, and repeats until none is dropped (at most four rounds), so what is kept is an invariant like one the program wrote: it holds on entry, is preserved, and holds after the loop together with the negated condition.

```tersus
out = [];
i = 0;
while i < 3 [{ affirm i <= 3; }] shrinks 3 - i {
    out = push(out, i);
    i = i + 1;
};
affirm size(out) = 3;       // size(out) = i was inferred: both start at 0 and grow by one
```

This is what makes `size(return) = size(a)` follow from a loop that pushes once per element, with no `affirm size(out) = i`. It covers differences of constants only: a list that starts as a copy of an argument, or a counter that starts at a variable, has no value to compare with on entry, so its invariant is written as before (`examples/update_list.tersus` does this for `size(out) = size(a)`). A loop with a `return` in its body infers nothing. If a loop is refused, the error is about the invariant the program wrote, never about an inferred one.

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
- A path that returns assumes the invariant, the loop condition and whatever its own `if` conditions say. Its return value is joined with the value returned after the loop, so an output contract holds only if every returning path establishes it. Above, `return <= 3` holds for the `return i` in the body (from the invariant) and for the one after the loop.
- The statements after the loop are validated once, from the state where the invariant holds and the condition is false. Facts that only a returning path knew, such as an `if` condition inside the body, are not known there.
- As for an `if`, a function where some path (including leaving the loop) does not return has no return value and is rejected with `Return value not found in top scope`.
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

### Termination

Statements that are not loops or calls end by themselves. A loop and a function that calls itself have to say why they end, or say that they may not. The validator checks what they say, or reports the code that is not guaranteed to terminate.

**`shrinks e`** names what gets smaller, here called the variant. Which kind of shrinking it means depends on the type of `e`, which the type checker resolves before validation:

- An `Int` counts down to a bound. For a loop, `e` must be at least `0` where an iteration starts (assuming the invariant and the condition), and smaller where the iteration ends, on every path that reaches the end of the body. A path that returns does not need to. For a function, `e` is evaluated in the parameters. It must be at least `0` for any arguments that meet the input contract, and at every call the function makes to itself the variant of the arguments must be smaller than the variant of the call it is in (the arguments of the function when it started, even if the body has assigned its parameters since).
- A struct or enum value must be a part of the one before it: a field, or a field of a field, which a `match` binding or `(t as Tree::Branch).left` is. Such values are finite, so this ends, and there is no bound to prove.
- Any other type is an error: `shrinks needs an Int, an enum or a struct`.

`i` can be counted up or down: `shrinks n - i` needs `i <= n` to be known where the iteration starts, and the condition `i < n` supplies it. The validator compares a difference such as `n - i` by its two sides, so `n - i >= 0` is `n >= i`, `n - (i + 1) < n - i` holds because `i + 1 > i`, and it works when one side of the difference is the same in the two. When both sides move, say so with two steps or a different variant.

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

fn leaves(t: Tree) -> Int shrinks t {
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
 A function name can be defined only once. A function defined inside another function's body is local to that body: functions defined after it there cannot call it. The definition order is enforced by validation (the type checker and the validator), while `evaluate` alone looks a function up when it is called, so run `check` (or `run`, which validates first) rather than relying on evaluation to reject a program. An argument or local variable with the same name hides the function. See `examples/helper_functions.tersus` and `examples/recursion.tersus`.

The evaluator runs a function body with its argument bindings and expects the body to set a return value. If a function completes without `return`, evaluation fails.

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
- `c * x` and `x * c` for any other known constant `c`: it is a node of its own, and whatever the graph says about two nodes `x` and `y` (or `x` and `0`) is said about `c * x` and `c * y` multiplied by `c`, so `n > 0` gives `2 * n > 0` and `n < m` gives `2 * n < 2 * m - 1` (any other product or quotient is an uninterpreted term, folded to a number only when both operands are known). Different constants are different nodes: `2 * n` is not compared with `3 * n`, and `x / 2` is not related to `x`.

A difference `x - y` of two unknown terms is a term of its own, which the graph says nothing about. A comparison of a difference with `0`, or with another difference that has a side in common, is decided by the other sides, which is what a loop variant such as `n - i` needs: `n - i >= 0` follows from `i <= n`, and `n - (i + 1) < n - i` from `i + 1 > i`. Other facts about a difference, such as `x - y = z` giving `x = y + z`, are not known.

```tersus
s = 3;
affirm s > 0;           // no rewrite eqToGtZero needed
y = s + 1;
affirm y != s;
```

`*` and `/` bind tighter than `+` and `-`: `2 + 3 * 4` is `14`. `/` rounds down (`-7 / 2` is `-4`). Integer literals can be negative (`x = -4;`, `[-1, 2]`, `3 - -2`). Dividing needs a divisor the validator can show is non-zero, checked like the index of `get`; evaluating `1 / 0` is an error.

```tersus
fn average(total: Int, count: Int) -> Int [{ affirm count > 0; }] [{ }] {
    return total / count;
};
```

See `examples/arithmetic.tersus`.

A goal `x != y` is proved when `x < y` or `x > y` is, and a fact `x != y` is used the other way: when `x <= y` is known too, `x < y` is, which an `i != n` loop condition needs to keep `i` below `n`. Contradictory facts, such as the guard of an unreachable branch, prove every comparison.

## Current Limitations

- No `break` or `continue`. `for` counts through a range only, not through the elements of a list or by a step other than `1`.
- Termination is checked for loops and for a function that calls itself, but only for a single `shrinks` value: an integer that counts to a bound, or a struct or enum value that loses a field at each step. Nothing else is a variant: not a lexicographic pair of integers, not the length of a list that shrinks, and a variant that changes both sides of a difference (`n - i` where `n` and `i` both move) has to be split. The intended direction is a termination proof written out with `affirm`s, of which `shrinks` is the sugar (see Termination). A program that cannot show termination is declared `~`, can loop forever, and `run` will not return. Validation does not hang on this: when it evaluates a call with known arguments it gives up after 100000 statements, and the call's result is then simply not known.
- No declarations separate from assignment.
- No strings or floats yet (see DATA_MODEL.md). Lists can be read with `get`, extended with `push` and updated with `set`, which return new lists. List literals contain literals only, so a list of variables is built with `push`.
- Arithmetic is limited to comparisons, adding or subtracting a known constant, multiplying by a known constant, and dividing by 1 (see Arithmetic). Other products and quotients are evaluated when their operands are known, but otherwise opaque, as is a relation between `x + y` terms where neither is known, or between differences that have no side in common.
- The size of a list is known for a literal, after `push` and `set`, and after a loop that grows it by a constant amount per iteration of a counter (see Inferred invariants). A list that a loop builds in a way that is not a constant per iteration, or that starts as an argument, needs its size in the invariant.
- `rewrite refl` adds a substituted copy of every fact, so it gets slow as the number of known facts grows (inside a loop body it took over a minute in one list-building program). `affirm` and loop invariants do not need it, so use it sparingly and on a context that is not large.
- `forall` is only used at the elements a program reads with `get`; a body without a `get(l, j)` is never instantiated, and there is no `exists`. When a proof needs an element the program does not read, mention it in an `affirm` (see How Validation Works).
- No block comments; only `//` line comments.
- Function bodies are evaluated with their argument bindings, the standard library, and the top-level functions defined before them. They do not capture other variables (no lexical closures), a function can call only itself and the functions defined before it, and a function name can be defined only once.
- The CLI runs one file at a time and has no REPL or multi-file programs.
