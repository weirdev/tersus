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
- Relations: `=`, `<`, `>`, `<=`, `>=`

All infix operators currently share one precedence level and associate left. Use parentheses when the intended grouping matters.

## Builtins

The standard library seeds these builtin functions:

- `size(list)`: returns the length of an integer list.
- `first(list)`: returns the first element of a non-empty integer list.
- `last(list)`: returns the last element of a non-empty integer list.
- `get(list, index)`: returns the element at `index`, counting from 0. The index must satisfy `0 <= index < size(list)`.
- `push(list, x)`: returns a new list with `x` added at the end. Lists are values, so the argument list is unchanged.
- `+` and `-`: integer arithmetic.
- `=`, `<`, `>`, `<=`, `>=`: integer relations returning booleans.

`first` and `last` have builtin input contracts requiring the list size to be greater than zero. Their current validation proof relies on the standard-library `eqToGtZero` axiom, whose input contract is checked by the primitive `checkGtZero` rewrite. Concrete evaluation still rejects empty lists and wrong argument types.

`get` has a builtin input contract requiring `index >= 0` and `index < size(list)`. It is checked with the primitive `checkRel` rewrite, so a call with a concrete list and index needs no proof, while a symbolic index must already be provable at the call site, usually from the enclosing function's contract or a loop invariant:

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

`push` has a builtin output contract, `size(return) = size(list) + 1`, which is instantiated at every call. That is what lets a function that builds a list state its size in its own output contract (see `examples/build_list.tersus`). An empty list is the literal `[]`.

Lists can only be built by `push` and read by `get`, `first` and `last`. There is no way to update an element in place, and lists hold integers only.

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

This proves partial correctness only: nothing shows that the loop ends. The validator also does no arithmetic, so a counting loop needs the arithmetic facts from somewhere, usually trusted `axiom` rules:

```tersus
axiom zeroWithinBound(i) [{ affirm i = 0; }] [{ affirm i <= 3; }];
axiom stepWithinBound(i) [{ affirm i < 3; }] [{ affirm (i + 1) <= 3; }];

i = 0;
rewrite zeroWithinBound i;
while i < 3 [{ affirm i <= 3; }] {
    rewrite stepWithinBound i;
    i = i + 1;
};
affirm i >= 3;
```

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

`affirm` requires a proof to be entailed by the current proof context. The proof may be present directly or match through known equality-equivalent terms.

```tersus
x = 5;
affirm x = 5;
```

Proofs use expression-like syntax. Variables refer to symbolic values tracked by the validator. Concrete values can appear directly.

```tersus
affirm size(xs) > 0;
affirm y = (x + 1);
```

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

- `rewrite refl <proof>`: uses known equalities to derive reflected/substituted proofs.
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

## Current Limitations

- No `for` loops, `break` or `continue`.
- Loops are validated for partial correctness only, and termination is not checked: a program can loop forever, and `run` (and validation of a call with known arguments, which evaluates it) will not return.
- No declarations separate from assignment.
- No strings, floats, records, or generic lists. Integer lists can be read with `get` and extended with `push`, but not updated in place.
- The validator has no arithmetic, so a counting loop over a list needs trusted `axiom` rules for its index facts (`i >= 0` after `i = i + 1`, and so on). `examples/parallel_sum.tersus` and `examples/build_list.tersus` show the shape.
- `rewrite refl` gets slow as the number of known facts grows (a `refl` inside a loop body took over a minute in one list-building program), so use it sparingly inside loops.
- No block comments; only `//` line comments.
- Function calls do not capture lexical closures; function bodies are evaluated with argument bindings plus the standard library context.
- The CLI runs one file at a time and has no REPL or multi-file programs.
