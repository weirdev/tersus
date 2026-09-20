Well typed implementation of ideas I wrote in black FB notebook.

See [LANGUAGE.md](LANGUAGE.md) for the current syntax and language constructs.

## Interpreter flow

The Haskell implementation has two main execution paths after parsing:

1. `Parse.parseStatementBlock` converts source text into the AST types in `TersusTypes`.
2. `Proof.evaluate` executes statements concretely with a `State` containing lexical scopes plus the standard library value context. Assignments evaluate expressions and update bindings, `return` writes the top-level return slot, blocks push a child scope, function calls run a native body or builtin, and validation statements are skipped.
3. `Proof.validate` symbolically validates the same statements with a `VState`. Runtime values are represented by fresh iotas, assignments add equality proofs, function calls check input contracts and instantiate exported output proofs, `axiom` and `proof` declarations register validation-only rewrite rules, `affirm` asks the internal `ProofEngine` whether a proof is entailed by the current context, and `rewrite` applies primitive or user-defined rules to expand that context.

`stack run` currently exposes only the parser CLI in `app/Main.hs`: it reads one line, parses a statement block, and prints the parsed AST. The evaluator and validator are exercised directly from tests and GHCi.

Next steps:
1. Control flow
    if/else/while
2. Let declarations
3. Property objects
    includes arrays
    Since data, as refed by iotas, not vars, is immutable, should all "properties" just be functions?
4. Support setting proofs in parent scope when they only correspond to declared there
    Control flow blocks will need to have their own rules
5. Functions
    Apply input-contract rewrites during assumption/instantiation instead of ignoring them
    Dont fully evaluate immediately in validation? ie. rewrite to get result?
6. Proof transformation v2
7. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
8. Distinguish between proof only vars and regular vars
9. Introduce a small type layer
    Cover ints, bools, int lists, and functions to catch builtin/type misuse earlier

Running:
    0. stack run
Tests:
    0. stack test
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
    
