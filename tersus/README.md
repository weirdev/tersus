Well typed implementation of ideas I wrote in black FB notebook.

Next steps:
1. Upgrade the test harness
    Add crash-regression tests, stronger negative cases, and warning cleanup
2. Control flow
    if/else/while
3. Let declarations
4. Improved proof representation, proof engine
    Proof engine would be able to apply generalized rewritings supplied by functions
    Axioms, replace EqToLtPlus1 with a standard lib impl
    Easier ways to rewrite
5. Property objects
    includes arrays
    Since data, as refed by iotas, not vars, is immutable, should all "properties" just be functions?
6. Support setting proofs in parent scope when they only correspond to declared there
    Control flow blocks will need to have their own rules
7. Functions
    Apply input-contract rewrites during assumption/instantiation instead of ignoring them
    Dont fully evaluate immediately in validation? ie. rewrite to get result?
8. Proof transformation v2
9. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
10. Distinguish between proof only vars and regular vars
11. Introduce a small type layer
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
    
