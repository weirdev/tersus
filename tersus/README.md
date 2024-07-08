Well typed implementation of ideas I wrote in black FB notebook.

Next steps:
0. Validate functions
    Validation udf function bodies (not just eval them)
    Export assertions to caller
    Should input validation vars be available for validation exports
    Syntax
1. Control flow
    if/else/while
1.5. Let declarations
2. Improved proof representation, proof engine
    How are we handling proofs w/ nested expressions, we currently do not allow temp iotas to leak
        Is this still workable?
    Proof engine would be able to apply generalized rewritings supplied by functions
3. Property objects
    includes arrays
    Since data, as refed by iotas, not vars, is immutable, should all "properties" just be functions?
4. Support setting proofs in parent scope when they only correspond to declared there
    Control flow blocks will need to have their own rules
5. Functions
    Dont fully evaluate immediately in validation? ie. rewrite to get result?
6. Proof transformation v2
7. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
8. Distinguish between proof only vars and regular vars

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
    