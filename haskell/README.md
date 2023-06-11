Well typed implementation of ideas I wrote in black FB notebook.

Next steps:
1. Improved proof representation, proof engine
    How are we handling proofs w/ nested expressions, we currently do not allow temp iotas to leak
        Is this still workable?
    Proof engine would be able to apply generalized rewritings supplied by functions
2. Functions
    Multiple args
    Replace operators (plus, minus)
    Dont fully evaluate immediately? ie. rewrite to get result?
3. Property objects
    includes arrays
    Since data, as refed by iotas, not vars, is immutable, should all "properties" just be functions?
4. User defined functions
5. Proof transformation v2
6. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
7. Distinguish between proof only vars and regular vars

Running:
    0. From this (haskell/) directory
    1. `ghci`
    2. `:load proof`
    3. Enter one of the cases below

Working Test cases:
    validate [Assign "x" (F Size [(Val (VIntList [5]))])]
    validate [Assign "x" (Val (VIntList [5, 4])), Assign "y" (F Size [(Var "x")])]
    validate [Assign "x" (F Size [(Val (VIntList [5]))]), Assign "y" (F Minus [(Val (VInt 1)), (Val (VInt 1))])]
    validate [Assign "x" (Val (VInt 5)),  ProofAssert (C "x" Eq (VInt 5))]
    validate [Assign "x" (Val (VInt 5)), Rewrite (EqToLtPlus1 "x"), ProofAssert (C "x" Lt (VInt 6))]
    validate [Assign "x" (Val (VInt 5)), AssignProofVar "a" (Val (VInt 5)), Rewrite (Refl "x"), ProofAssert (A "x" Eq "a")]

Working Error cases:
    validate [ProofAssert (C "x" Lt (VInt 5))]
    validate [Assign "x" (Val (VInt 5)), ProofAssert (C "x" Lt (VInt 6))]
    