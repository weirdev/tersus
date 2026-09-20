Well typed implementation of ideas I wrote in black FB notebook.

See [LANGUAGE.md](LANGUAGE.md) for the current syntax and language constructs.

## Interpreter flow

The Haskell implementation has two main execution paths after parsing:

1. `Parse.parseStatementBlock` converts source text into the AST types in `TersusTypes`. `//` line comments are skipped as whitespace.
2. `Proof.evaluate` executes statements concretely with a `State` containing lexical scopes plus the standard library value context. Assignments evaluate expressions and update bindings, `return` writes the top-level return slot, blocks push a child scope, function calls run a native body or builtin, and validation statements are skipped.
3. `Proof.validate` symbolically validates the same statements with a `VState`. Runtime values are represented by fresh iotas, assignments add equality proofs, function calls check input contracts and instantiate exported output proofs, `axiom` and `proof` declarations register validation-only rewrite rules, `affirm` asks the internal `ProofEngine` whether a proof is entailed by the current context, and `rewrite` applies primitive or user-defined rules to expand that context.

The CLI in `app/Main.hs` drives these paths over a source file (logic in `src/Cli.hs`):

- `stack run -- check <file>` parses and validates the program, printing `OK` on success.
- `stack run -- run <file>` validates the program, and only if that succeeds evaluates it and prints its return value (nothing is printed when the program does not `return`).
- Use `-` as the file to read the program from standard input.
- Errors go to standard error, prefixed with `Parse error:`, `Validation failed:` or `Evaluation failed:`. The exit code is 1 for a failed program and 2 for bad command-line usage.

Next steps, roughly in priority order:
1. Control flow
    if/else/while
    The biggest gap: booleans have no consumer, and the parallel-iteration and linked-list motivating cases (item 9) are not expressible without it
    Needs a design pass first: does `if` merge the proof contexts of its branches, and how is a loop invariant written?
2. Let user functions call other user functions
    Function bodies currently see only their arguments and the standard library, and argument passing is by value (see LANGUAGE.md)
    Decide the closure/scoping rules before adding mutable data, since by-value vs by-reference only becomes observable then
3. Let declarations
4. Property objects
    includes arrays
    Since data, as refed by iotas, not vars, is immutable, should all "properties" just be functions?
5. Support setting proofs in parent scope when they only correspond to declared there
    Control flow blocks will need to have their own rules
6. Functions
    Apply input-contract rewrites during assumption/instantiation instead of ignoring them
    Dont fully evaluate immediately in validation? ie. rewrite to get result?
7. Proof transformation v2
    Validator arithmetic, so `s = 3` implies `s > 0` without a manual `rewrite eqToGtZero s`
8. Widen operators and literals
    `*` and `/` (the parser has a TODO for `*`), and negative literals
9. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
    Safe access is covered by examples/safe_access.tersus
10. Distinguish between proof only vars and regular vars
11. Introduce a small type layer
    Cover ints, bools, int lists, and functions to catch builtin/type misuse earlier
12. Pretty-print proofs in error messages
    A failed `affirm x < 4` currently reports the raw AST (`Assertion failed: FApp (CTerm (VFunct ["a","b"] ...`); render it in source syntax instead (`x < 4`)
    Also applies to the other validation errors that embed proofs or iotas
13. Maintenance
    Remove the redundant-pattern warning in `Proof.hs` (`valExpression _ _ e`)
    Check whether `deriveRefl` still lets the proof context grow quickly; the equivalence search is bounded, but the number of facts is not
    Check that the parser handles CRLF line endings, since files may be checked out with them on Windows

Running:
    0. stack run -- run examples/basics.tersus
    1. stack run -- check <file>
Tests:
    0. stack test
Examples:
    0. See examples/README.md; `stack test` checks every program in examples/
OR:
    0. From this (tersus/) directory
    1. `ghci`
    2. `:load Proof`
    3. Enter one of the cases below

Notes:
- Input validation statements form the function's contract
  - Similar to swapping out a function with the same signature for eval,
  should be able to swap out a function with the same input and output
  validation statements
    
