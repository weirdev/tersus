# Tersus Language Guide

Tersus is a small imperative language for writing ordinary computations next to proof and validation statements. The current implementation supports integers, integer lists, user-defined functions, nested blocks, and a proof validator built around an internal proof engine for equality, simple rewrites, and builtin function contracts.

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

## Values

Tersus currently has four runtime value categories:

- Integers: `0`, `1`, `42`
- Integer lists: `[]`, `[1]`, `[3, 6, 9]`
- Booleans: `true`, `false`
- Functions: builtin functions from the standard library or user-defined functions

Boolean values can also be produced by relation expressions such as `x < y`. The condition of an `if` consumes them.

Negative literals are not parsed directly. Use subtraction instead, for example `0 - 1`.

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

- Arithmetic: `+`, `-`
- Relations: `=`, `!=`, `<`, `>`, `<=`, `>=`

All infix operators currently share one precedence level and associate left. Use parentheses when the intended grouping matters.

## Builtins

The standard library seeds these builtin functions:

- `size(list)`: returns the length of an integer list.
- `first(list)`: returns the first element of a non-empty integer list.
- `last(list)`: returns the last element of a non-empty integer list.
- `get(list, index)`: returns the element at `index`, counting from 0. The index must satisfy `0 <= index < size(list)`.
- `push(list, x)`: returns a new list with `x` added at the end. Lists are values, so the argument list is unchanged.
- `set(list, index, x)`: returns a new list with the element at `index` replaced by `x`. The index must satisfy `0 <= index < size(list)`, and the argument list is unchanged.
- `+` and `-`: integer arithmetic.
- `=`, `!=`, `<`, `>`, `<=`, `>=`: integer relations returning booleans.

`first` and `last` have builtin input contracts requiring the list size to be greater than zero. Their current validation proof relies on the standard-library `eqToGtZero` axiom, whose input contract is checked by the primitive `checkGtZero` rewrite. Concrete evaluation still rejects empty lists and wrong argument types.

`get` and `set` have a builtin input contract requiring `index >= 0` and `index < size(list)`. It is checked with the primitive `checkRel` rewrite, so a call with a concrete list and index needs no proof, while a symbolic index must already be provable at the call site, usually from the enclosing function's contract or a loop invariant:

```tersus
a = [5, 6, 7];
x = get(a, 2);          // fine: 0 <= 2 < 3
// y = get(a, 3);       // rejected: 3 < 3 does not hold

// The contract has to show both bounds, since the body can only assume them.
fn at(lst, i) [{
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

Lists are built with `push`, updated with `set`, and read by `get`, `first` and `last`. Lists hold integers only.

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
fn firstOr(lst, fallback) {
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
fn f(n) {
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
fn firstOr(lst, fallback) {
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
while i < 3 {
    i = i + 1;
    n = n + 2;
};
return n;
```

The condition must evaluate to a boolean, the body is a block with the same scoping as an `if` branch, and the statement ends with `;`. Nothing checks that the loop ends, and a loop whose condition never becomes false runs forever. A `return` inside the body ends the function or program, and stops the loop.

#### Loop invariants

The validator does not unroll loops. A loop can carry an invariant, written with the same `[{ ... }]` contract syntax as functions, between the condition and the body:

```tersus
while i < 3 [{ affirm i <= 3; }] {
    rewrite stepWithinBound i;
    i = i + 1;
};
```

The invariant is optional; without one the loop still validates but proves nothing about the variables it changes. Validation works like this:

1. The invariant must hold before the first iteration.
2. Every outer variable the body assigns is treated as an unknown value from then on. Facts about its earlier values are not carried over, but facts about variables the body does not assign are.
3. Assuming the invariant and the loop condition, the body must establish the invariant again at its end. The invariant's `rewrite` statements run when it is being checked, and are skipped when it is assumed, exactly as for function contracts.
4. After the loop the invariant holds and the condition does not. An invariant `i <= 3` on `while i < 3` therefore gives `i >= 3` afterwards.

This proves partial correctness only: nothing shows that the loop ends. The validator reasons about integer comparisons itself (see Arithmetic below), so a counting loop needs no helper rules:

```tersus
i = 0;
while i < 3 [{ affirm i <= 3; }] {
    i = i + 1;
};
affirm i >= 3;
```

`i = 0` gives the invariant on entry, `i < 3` gives `i + 1 <= 3` at the end of the body, and the negated condition gives `i >= 3` afterwards.

An invariant can use `forall` to describe a list that is built or updated element by element. The validator proves it for the new element and, with the frame facts of `push` and `set`, for the old ones:

```tersus
fn doubled(a) [{ }] [{ affirm forall j in 0..size(a): get(return, j) = (get(a, j) + get(a, j)); }] {
    n = size(a);
    i = 0;
    out = [];
    while i < n [{
        affirm i >= 0; affirm i <= n; affirm size(out) = i;
        affirm forall j in 0..i: get(out, j) = (get(a, j) + get(a, j));
    }] {
        out = push(out, get(a, i) + get(a, i));
        i = i + 1;
    };
    return out;
};
```

See `examples/parallel_sum.tersus`, `examples/build_list.tersus` and `examples/update_list.tersus`.

`while` is a reserved word; `whiley` is still an ordinary name.

#### Returning from a loop

A body that contains `return` is validated as paths, in the same way as an `if` with a `return`:

```tersus
fn firstOver(n) [{ }] [{ affirm return <= 3; }] {
    i = 0;
    rewrite zeroWithinBound i;
    while i < 3 [{ affirm i <= 3; }] {
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

### Functions

Functions are defined with `fn` and assigned to the given name.

```tersus
fn add1(i) {
    return i + 1;
};

x = add1(4);
```

Function arguments are comma-separated. Function bodies are ordinary statement blocks.

The evaluator runs a function body with its argument bindings and expects the body to set a return value. If a function completes without `return`, evaluation fails.

### Argument Passing

Arguments are passed by value. Each argument expression is evaluated before the call and bound to the matching parameter in a fresh scope. The caller's variable is not moved and is still usable afterwards, and nothing the function does to a parameter, including reassigning it, is visible to the caller.

```tersus
fn reset(xs) {
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

`affirm` requires a proof to be entailed by the current proof context. The proof may be present directly or match through known equalities, including equalities between the parts of a term: if `s = k` and `size(k) = l` are known then `size(s) + 1` is known to equal `l + 1`, with no `rewrite` needed to say so.

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
Validation failed: Assertion failed: forall j in 0..size(l): get(l, j) = 0
```

### `forall`

`forall` states a fact about every index in a range, for use in `affirm`, contracts and loop invariants. The validator can both prove and use a `forall`. Evaluation ignores it like any validation statement.

```tersus
affirm forall j in 0..size(l): get(l, j) = 0;            // 0 <= j < size(l)
affirm forall j where j >= 0, j < n, j != 2: get(l, j) = 0;
```

- `forall j in lo..hi: P` is shorthand for `forall j where j >= lo, j < hi: P`, so the range is half open.
- `forall j where g1, g2, ...: P` holds `P` for every `j` for which all the guards hold. A guard is any relation.
- To prove a `forall` (in `affirm`, an output contract, or a loop invariant) the validator takes an index that meets the guards, and proves the body for it from everything it knows. So `affirm forall j in 0..3: j < 3;` holds, a narrower range of a known `forall` holds when its bound is known to be within the original one, and an empty range holds for any body. If the body does not follow directly, the index is also compared with the indexes the program reads with `get` (below, equal to, and above), and the body must follow in each case. That is how a list that grew by one is shown to keep its old elements and have the new one at the end. The name of the index does not matter. A `forall` cannot be passed to a rewrite rule as an argument.
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

- `rewrite refl <proof>`: uses known equalities to derive reflected/substituted proofs, which are added to the context as facts. `affirm` already sees through equalities, so this is rarely needed. A function's output contract exports the facts that are recorded in the context, not what the equalities imply, so `refl` can still add a fact that a caller then receives.
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
fn name(arg1, arg2) [{ input validation }] [{ output validation }] {
    body
};
```

Both contract sections are optional. If one contract section is present, it is treated as the input contract. To specify only an output contract, write an empty input contract first:

```tersus
fn add1(i) [{}] [{
    affirm return = (i + 1);
}] {
    return i + 1;
};
```

Input contracts are checked at call sites before the function body's exported proofs are instantiated. They are also assumed while validating the function body.

Output contracts are validated after the body has been validated. Proofs involving argument names, `return`, and proof variables defined in the input or output contract can be exported to callers.

Example:

```tersus
fn getFirstWithSize(lst) [{
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
fn keep(l) [{ affirm forall j in 0..size(l): get(l, j) = 0; }] [{ affirm forall j in 0..size(return): get(return, j) = 0; }] {
    return l;
};
```

See `examples/forall_facts.tersus`.

## Arithmetic

The validator decides integer comparisons itself, so `affirm`, loop invariants, `checkRel` and `if` guards need no helper rewrites for them. It treats `x - y <= c` facts as a graph and answers a goal by the shortest path between the two sides. The facts come from:

- relations in the context (`i < n`, `a <= b`, and `x != y` only as a goal),
- `x + c` and `x - c` where `c` has a known integer value,
- any term with a known integer value, and
- `size(l) >= 0`.

```tersus
s = 3;
affirm s > 0;           // no rewrite eqToGtZero needed
y = s + 1;
affirm y != s;
```

A goal `x != y` is proved when `x < y` or `x > y` is. Contradictory facts, such as the guard of an unreachable branch, prove every comparison.

## Current Limitations

- No `for` loops, `break` or `continue`.
- Loops are validated for partial correctness only, and termination is not checked: a program can loop forever, and `run` (and validation of a call with known arguments, which evaluates it) will not return.
- No declarations separate from assignment.
- No strings, floats, records, or generic lists. Integer lists can be read with `get`, extended with `push` and updated with `set`, which return new lists.
- Arithmetic is limited to comparisons and adding or subtracting a known constant (see Arithmetic). There is no `*` or `/`, and a relation between `x + y` terms where neither is known is not understood.
- The size of a list built by a literal or loop is not computed by the validator on its own: `out = []; define s0 = size(out);` is how `examples/build_list.tersus` gets `size(out) = 0`.
- `rewrite refl` adds a substituted copy of every fact, so it gets slow as the number of known facts grows (inside a loop body it took over a minute in one list-building program). `affirm` and loop invariants do not need it.
- `forall` is only used at the elements a program reads with `get`; a body without a `get(l, j)` is never instantiated, and there is no `exists`.
- No block comments; only `//` line comments.
- Function calls do not capture lexical closures; function bodies are evaluated with argument bindings plus the standard library context.
- The CLI runs one file at a time and has no REPL or multi-file programs.
