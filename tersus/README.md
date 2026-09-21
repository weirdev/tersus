Well typed implementation of ideas I wrote in black FB notebook.

See [LANGUAGE.md](LANGUAGE.md) for the current syntax and language constructs.

## Interpreter flow

The Haskell implementation has two main execution paths after parsing:

1. `Parse.parseStatementBlock` converts source text into the AST types in `TersusTypes`. `//` line comments are skipped as whitespace.
2. `Proof.evaluate` executes statements concretely with a `State` containing lexical scopes plus the standard library value context. Assignments evaluate expressions and update bindings, `return` writes the top-level return slot and ends the program or function body (the remaining statements are dropped), blocks push a child scope, function calls run a native body or builtin (and must pass exactly as many arguments as the function has parameters), and validation statements are skipped. `if` runs the chosen branch as a block, and `while` runs its body as a block and then puts itself back at the front of the remaining statements until the condition is false. Nothing bounds evaluation, so a loop that never ends never returns.
3. `Proof.validate` symbolically validates the same statements with a `VState`. Runtime values are represented by fresh iotas, assignments add equality proofs, function calls check input contracts and instantiate exported output proofs (tied to the caller's variables by equalities between each argument's fresh iota and the variable, so a contract like `push`'s `size(return) = size(list) + 1` is usable), `axiom` and `proof` declarations register validation-only rewrite rules, `affirm` asks the internal `ProofEngine` whether a proof is entailed by the current context (a congruence closure over the known equalities, so equal arguments give equal results without any rewriting), and `rewrite` applies primitive or user-defined rules to expand that context. `if` validates each branch from the state after the condition with the condition (or its negation) assumed, then joins them by keeping only the facts both branches establish about the variables they assign. `while` checks its invariant on entry, treats the variables its body assigns as unknown, checks the invariant is preserved, and afterwards assumes the invariant and the negated condition. An `if` with a `return` in a branch cannot be joined, since the statements after it do not run on the path that returned. Instead each branch is validated followed by the rest of the program (`valReturningIf`), and the two ends are joined by keeping the facts both establish and merging the return values (`joinReturnPaths`). A `while` whose body contains `return` works the same way (`valReturningWhile`): the body is validated as a path that ends in a `LoopEnd` statement checking the invariant (such paths only go back to the condition, so joins ignore them), and the program after the loop is the other path, starting from the state where the condition is false.

The CLI in `app/Main.hs` drives these paths over a source file (logic in `src/Cli.hs`):

- `stack run -- check <file>` parses and validates the program, printing `OK` on success.
- `stack run -- run <file>` validates the program, and only if that succeeds evaluates it and prints its return value (nothing is printed when the program does not `return`).
- Use `-` as the file to read the program from standard input.
- Errors go to standard error, prefixed with `Parse error:`, `Validation failed:` or `Evaluation failed:`. The exit code is 1 for a failed program and 2 for bad command-line usage.

Next steps, roughly in priority order:
1. List element updates
    `get` and `push` are done (see LANGUAGE.md), and the parallel-iteration case is `examples/parallel_sum.tersus`. There is still no way to replace an element of a list, which the linked-list motivating case (item 10) needs
    Reading the two list examples, validator arithmetic (item 8) is what they need most: every index counter needs trusted axioms for `i >= 0`, `i <= n` and `i = n` after the loop
2. Element-level facts about lists
    Contracts can only state sizes today: `push` and `get` say nothing about elements, and there is no way to say something about every index, so `pairSums` (examples/parallel_sum.tersus) cannot state that each result element is the sum of the corresponding pair
    Give `push` output facts (`get(return, size(list)) = x`, and `get(return, j) = get(list, j)` for `j < size(list)`)
    Some way to state a fact for every index, usable in output contracts and loop invariants (design left open)
    Carrying such an invariant through a loop needs index arithmetic (item 8)
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
    Safe access is covered by examples/safe_access.tersus, and parallel iteration of two lists by examples/parallel_sum.tersus
11. Distinguish between proof only vars and regular vars
12. Introduce a small type layer
    Cover ints, bools, int lists, and functions to catch builtin/type misuse earlier
13. Pretty-print proofs in error messages
    A failed `affirm x < 4` currently reports the raw AST (`Assertion failed: FApp (CTerm (VFunct ["a","b"] ...`); render it in source syntax instead (`x < 4`)
    Also applies to the other validation errors that embed proofs or iotas
14. Maintenance
    Remove the redundant-pattern warning in `Proof.hs` (`valExpression _ _ e`)
    Entailment no longer needs `rewrite refl`, but `deriveRefl` still copies every fact and is used for exporting contract facts; export from the closure instead, then `refl` and `reflectProofsByProofs` can go
    Improve the performance of the congruence closure in `ProofEngine.entails`. It is fine at the current sizes (the loop examples validate in about 0.2s) but has not been benchmarked on large contexts. With n terms, F facts and A applications:
    The closure is rebuilt from the facts on every `affirm`, invariant check and `if` join, so cost grows with statements times facts; keep it in the proof context and update it as facts are added
    `insertProofs` and `proofContextFromFacts` use `nub`, which is O(F^2) with deep comparisons and probably dominates before the closure does; use a set keyed on the interned terms
    The fixpoint loop regroups every application each round, O(n + A log A) per round and up to O(n) rounds (roughly the nesting depth in practice); use-list propagation (Downey-Sethi-Tarjan) gets O(n log n)
    The union-find has no rank or path compression, and constants are found by a linear scan with deep `Eq` (the standard library functions make that heavy); intern them by a cheaper key
    The context carries the standard library facts twice
    Benchmark on a synthetic context of a few thousand facts before choosing which of these to do
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
    
