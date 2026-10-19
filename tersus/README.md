Well typed implementation of ideas I wrote in black FB notebook.

See [LANGUAGE.md](LANGUAGE.md) for the current syntax and language constructs.

## Interpreter flow

The Haskell implementation has two main execution paths after parsing:

1. `Parse.parseStatementBlock` converts source text into the AST types in `TersusTypes`. The parser remembers the structs declared so far, so a struct literal becomes the application of a `Ctor` builtin to the fields in declaration order, and `x.f` the application of `Field f`; the checker, evaluator and proof engine see structs as ordinary builtin applications. `//` line comments are skipped as whitespace.
2. `TypeCheck.typeCheck` infers and checks types (unification inside a function body, with the declared parameter and return types and the builtin signatures), and `Proof.validate` runs it before validating. `Proof.evaluate` does not check types, since the CLI validates first.
3. `Proof.evaluate` executes statements concretely with a `State` containing lexical scopes plus the standard library value context. Assignments evaluate expressions and update bindings, `return` writes the top-level return slot and ends the program or function body (the remaining statements are dropped), blocks push a child scope, function calls run a native body or builtin (and must pass exactly as many arguments as the function has parameters), and validation statements are skipped. `if` runs the chosen branch as a block, and `while` runs its body as a block and then puts itself back at the front of the remaining statements until the condition is false. Nothing bounds evaluation, so a loop that never ends never returns.
4. `Proof.validate` symbolically validates the same statements with a `VState`. Runtime values are represented by fresh iotas, assignments add equality proofs, function calls whose arguments are all known are also evaluated for their result, with a budget of `validationFuel` statements so validation cannot hang on a long or endless callee, and check input contracts and instantiate exported output proofs (tied to the caller's variables by equalities between each argument's fresh iota and the variable, or the literal when the argument is one and the output contract mentions it, so a contract like `push`'s `size(return) = size(list) + 1` or `set`'s `size(return) = size(list)` is usable), `axiom` and `proof` declarations register validation-only rewrite rules, `affirm` asks the internal `ProofEngine` whether a proof is entailed by the current context (validation is a bounded search that is sound but incomplete: what it cannot prove is rejected as `Could not prove: P`, and the program adds `affirm`s, `define`s and `rewrite`s until it can, see LANGUAGE.md; `*` and `/` bind tighter than the other infix operators, and `/` must have a divisor proved non-zero; a failure reports the proof in source syntax, rendered by `Pretty.renderVarProof`) (a congruence closure over the known equalities, so equal arguments give equal results without any rewriting, plus difference constraints over its classes for integer comparisons, so `s = 3` gives `s > 0` and `i < n` gives `i + 1 <= n`), and `rewrite` applies primitive or user-defined rules to expand that context (applying a rule only adds its outputs, with no `refl` copy of the other facts). A `forall` is a proof form `Forall index guards body` whose index is a `BVar`, interned as one term in the closure; `entailsAll` proves a `forall` goal for a fresh index meeting the guards, and instantiates `forall` facts at the `get(L, t)` terms it finds (`forallInstances`). `push` and `set` also export `return = push(list, x)` or `set(list, index, x)`, which the standard library rules `pushKeeps`, `setKeeps` use to say a given index is unchanged. `if` validates each branch from the state after the condition with the condition (or its negation) assumed, then joins them by keeping only the facts both branches establish about the variables they assign. `while` checks its invariant on entry, treats the variables its body assigns as unknown, checks the invariant is preserved, and afterwards assumes the invariant and the negated condition. An `if` with a `return` in a branch cannot be joined, since the statements after it do not run on the path that returned. Instead each branch is validated followed by the rest of the program (`valReturningIf`), and the two ends are joined by keeping the facts both establish and merging the return values (`joinReturnPaths`). A `while` whose body contains `return` works the same way (`valReturningWhile`): the body is validated as a path that ends in a `LoopEnd` statement checking the invariant (such paths only go back to the condition, so joins ignore them), and the program after the loop is the other path, starting from the state where the condition is false.

The CLI in `app/Main.hs` drives these paths over a source file (logic in `src/Cli.hs`):

- `stack run -- check <file>` parses and validates the program, printing `OK` on success.
- `stack run -- run <file>` validates the program, and only if that succeeds evaluates it and prints its return value (nothing is printed when the program does not `return`).
- Use `-` as the file to read the program from standard input.
- Errors go to standard error, prefixed with `Parse error:`, `Validation failed:` or `Evaluation failed:`. The exit code is 1 for a failed program and 2 for bad command-line usage.

Next steps, roughly in priority order:
1. Element-level facts about lists (mostly done)
    `forall j in lo..hi: P` is implemented (see LANGUAGE.md): it is a proof form `Forall index guards body` whose index is a `BVar`, proved for a fresh index and instantiated at the `get(L, t)` terms of the closure, and `push`/`set` export frame foralls, so `examples/parallel_sum.tersus` states that each result element is the sum of its pair
    Instances come only from `get(L, j)` terms in the body, so a body that does not read elements is never used; `exists` is not implemented; and `forall` does not nest
    Proving a `forall` over a range that grew by one splits the index on the indexes the program reads, up to `maxSplitIndexes`; a program with many reads may need a smarter choice
    Benchmark `entailsAll` on large contexts: `frame_facts.tersus` takes about 0.2s because every `affirm` re-solves the closure and instantiates the frame foralls again
2. Let user functions call other user functions (done for earlier functions and self-recursion, see examples/helper_functions.tersus and examples/recursion.tersus)
    A top-level `fn` is also registered in the global evaluation context and, for validation, in the global iota and proof contexts (`registerGlobalFunction`, `registerGlobalFunctionProof`), so the bodies of later functions find it by name like a standard library function. A name can be defined once
    Self-recursion is done (`bindFunctionToItself`): the body is validated with its name bound to a copy that exports the output contract's assertions, and the contract is then checked, so this is partial correctness like loops. Mutual recursion needs a forward declaration, and there is no termination check (for instance a decreasing measure in the contract)
    Argument passing is by value and bodies capture no variables (see LANGUAGE.md); decide the closure rules before adding mutable data
3. Let declarations
4. Property objects (see DATA_MODEL.md: structs, algebraic data types and generalized lists replace this item; structs are done)
    includes arrays
    Since data, as refed by iotas, not vars, is immutable, should all "properties" just be functions?
5. Support setting proofs in parent scope when they only correspond to declared there
    Control flow blocks will need to have their own rules
6. Functions
    Apply input-contract rewrites during assumption/instantiation instead of ignoring them
    Dont fully evaluate immediately in validation? ie. rewrite to get result?
7. Proof transformation v2
    Validator arithmetic is done for comparisons and for adding or subtracting a known constant (`ProofEngine.arithmeticEdges`); `*` and `/` (item 8) and relations between sums of two unknown terms are not
    Evaluate builtins on concrete terms inside the closure, so `out = []` gives `size(out) = 0` without `define s0 = size(out)`
8. Widen operators and literals (done: `*`, `/`, negative literals; see examples/arithmetic.tersus)
    The validator only understands `x * 0`, `x * 1` and `x / 1`; other products and quotients are opaque terms (folded when both operands are known). Nonlinear facts such as `n > 0` giving `n * 2 > 0` would need a rule or a solver step
9. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
    Safe access is covered by examples/safe_access.tersus, and parallel iteration of two lists by examples/parallel_sum.tersus
    The doubly linked list needs lists that can be updated (`set`, done, see examples/update_list.tersus) plus element-level facts (item 1) to say what each link points to
10. Distinguish between proof only vars and regular vars
11. Introduce a small type layer (done: phase 1 of DATA_MODEL.md, see `TypeCheck.hs`)
    Covers ints, bools, lists of any element type, and functions to catch builtin/type misuse earlier
12. Pretty-print proofs in error messages (done for failed `affirm`s, see `Pretty.hs`)
    Other validation errors that embed iotas, proof contexts or whole states (`Function object not validated`, trace output) still use `show`
13. Maintenance (done: `nub` replaced by sets, reflection indexed by subterm, `Value` comparison cheap for builtins, CRLF line endings, redundant pattern, `eqToGtZero` out of `first`/`last`)
    Entailment no longer needs `rewrite refl`, but `deriveRefl` still copies every fact and is used for exporting contract facts; export from the closure instead, then `refl` and `reflectProofsByProofs` can go
    Benchmarked on programs of N `push` calls followed by an `affirm` (at `-O1`): N=20 takes 0.3s, N=40 0.9s and N=80 4.4s, from 1.1s, 9.5s and over 80s before. Plain arithmetic chains of 80 statements take 0.04s. Growth is still about N^2, from these remaining costs:
    The closure is rebuilt from the facts on every `affirm`, invariant check and `if` join, so cost grows with statements times facts; keep it in the proof context and update it as facts are added
    `valFunctExprHelper` reflects the call's input proofs through every equality in the context at each call
    The fixpoint loop regroups every application each round, O(n + A log A) per round and up to O(n) rounds (roughly the nesting depth in practice); use-list propagation (Downey-Sethi-Tarjan) gets O(n log n)
    The union-find has no rank or path compression, and constants are found by a linear scan
    The context carries the standard library facts twice

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
    
