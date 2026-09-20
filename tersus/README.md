Well typed implementation of ideas I wrote in black FB notebook.

See [LANGUAGE.md](LANGUAGE.md) for the current syntax and language constructs.

## Interpreter flow

The Haskell implementation has two main execution paths after parsing:

1. `Parse.parseStatementBlock` converts source text into the AST types in `TersusTypes`. `//` line comments are skipped as whitespace.
2. `Proof.evaluate` executes statements concretely with a `State` containing lexical scopes plus the standard library value context. Assignments evaluate expressions and update bindings, `return` writes the top-level return slot and ends the program or function body (the remaining statements are dropped), blocks push a child scope, function calls run a native body or builtin (and must pass exactly as many arguments as the function has parameters), and validation statements are skipped. `if` runs the chosen branch as a block, and `while` runs its body as a block and then puts itself back at the front of the remaining statements until the condition is false. Evaluation stops with an error after `stepLimit` (1,000,000) statements, so a loop that never ends does not hang.
3. `Proof.validate` symbolically validates the same statements with a `VState`. Runtime values are represented by fresh iotas, assignments add equality proofs, function calls check input contracts and instantiate exported output proofs, `axiom` and `proof` declarations register validation-only rewrite rules, `affirm` asks the internal `ProofEngine` whether a proof is entailed by the current context, and `rewrite` applies primitive or user-defined rules to expand that context. `if` validates each branch from the state after the condition with the condition (or its negation) assumed, then joins them by keeping only the facts both branches establish about the variables they assign. `while` checks its invariant on entry, treats the variables its body assigns as unknown, checks the invariant is preserved, and afterwards assumes the invariant and the negated condition. An `if` with a `return` in a branch cannot be joined, since the statements after it do not run on the path that returned. Instead each branch is validated followed by the rest of the program (`valReturningIf`), and the two ends are joined by keeping the facts both establish and merging the return values (`joinReturnPaths`). A `while` whose body contains `return` works the same way (`valReturningWhile`): the body is validated as a path that ends in a `LoopEnd` statement checking the invariant (such paths only go back to the condition, so joins ignore them), and the program after the loop is the other path, starting from the state where the condition is false.

The CLI in `app/Main.hs` drives these paths over a source file (logic in `src/Cli.hs`):

- `stack run -- check <file>` parses and validates the program, printing `OK` on success.
- `stack run -- run <file>` validates the program, and only if that succeeds evaluates it and prints its return value (nothing is printed when the program does not `return`).
- Use `-` as the file to read the program from standard input.
- Errors go to standard error, prefixed with `Parse error:`, `Validation failed:` or `Evaluation failed:`. The exit code is 1 for a failed program and 2 for bad command-line usage.

Next steps, roughly in priority order:
1. Control flow
    `if`/`else`, `while` and early-exit `return` are done (see LANGUAGE.md). Branches are validated under the condition and joined by keeping only the facts both establish; loops are validated by a contract-style invariant, `while cond [{ invariant }] { body }`; `return` in an `if` branch or a `while` body (guard clauses such as `if n < 1 { return 0; }`, search loops) is validated path by path; concrete evaluation stops after 1,000,000 statements
    Remaining: loop termination (loops are checked for partial correctness only). A decreasing measure (variant) that the body must reduce, checked with the same axiom-based arithmetic as invariants
    The parallel-iteration and linked-list motivating cases (item 10) also need indexable/updatable data (see item 2)
2. List element access and construction
    `get(list, i)` with an input contract requiring `i >= 0` and `i < size(list)`, following the `first`/`last` pattern
    `push(list, x)` and an empty-list builtin, with output contracts on `size`, so a function can build a result list
    Unlocks the parallel-iteration motivating case: a function taking two lists of the same length (`affirm size(a) = size(b)`) and summing each element pair in an index loop, with a loop invariant on `i`
    Write the example with trusted `axiom` rules for the index arithmetic first (as in `examples/loops.tersus`), to see whether validator arithmetic (item 8) is needed before it is readable
3. Let user functions call other user functions
    Function bodies currently see only their arguments and the standard library, and argument passing is by value (see LANGUAGE.md)
    Decide the closure/scoping rules before adding mutable data, since by-value vs by-reference only becomes observable then
4. Let declarations
5. Property objects
    includes arrays
    Since data, as refed by iotas, not vars, is immutable, should all "properties" just be functions?
6. Support setting proofs in parent scope when they only correspond to declared there
    Control flow blocks will need to have their own rules
7. Functions
    Apply input-contract rewrites during assumption/instantiation instead of ignoring them
    Dont fully evaluate immediately in validation? ie. rewrite to get result?
8. Proof transformation v2
    Validator arithmetic, so `s = 3` implies `s > 0` without a manual `rewrite eqToGtZero s`
9. Widen operators and literals
    `*` and `/` (the parser has a TODO for `*`), and negative literals
10. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
    Safe access is covered by examples/safe_access.tersus
11. Distinguish between proof only vars and regular vars
12. Introduce a small type layer
    Cover ints, bools, int lists, and functions to catch builtin/type misuse earlier
13. Pretty-print proofs in error messages
    A failed `affirm x < 4` currently reports the raw AST (`Assertion failed: FApp (CTerm (VFunct ["a","b"] ...`); render it in source syntax instead (`x < 4`)
    Also applies to the other validation errors that embed proofs or iotas
14. Maintenance
    Remove the redundant-pattern warning in `Proof.hs` (`valExpression _ _ e`)
    Check whether `deriveRefl` still lets the proof context grow quickly; the equivalence search is bounded, but the number of facts is not
    Check that the parser handles CRLF line endings, since files may be checked out with them on Windows

Running (from this (tersus/) directory):
    0. stack run -- run examples/basics.tersus
    1. stack run -- check <file>
Tests:
    0. stack test
Examples:
    0. See examples/README.md; `stack test` checks every program in examples/
Interactive use:
    0. `ghci` from this (tersus/) directory
    1. `:load Proof`
    2. Call `evaluate` or `validate` on the result of `parseStatementBlock`

Notes:
- Input validation statements form the function's contract
  - Similar to swapping out a function with the same signature for eval,
  should be able to swap out a function with the same input and output
  validation statements
    
