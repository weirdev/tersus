Well typed implementation of ideas I wrote in black FB notebook.

Next steps:
0. User defined functions
    Block structure
        expression containing list of expressions
        evaluating returns a value or void
        validating adds proofs
    Functions as ordinary values
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
4. Proof transformation v2
5. Test against motivating example cases (safe access to lize of size known at runtime, parallel iteration of lists, provably safe doubly linked list)
6. Distinguish between proof only vars and regular vars

Running:
    0. From this (haskell/) directory
    1. `ghci`
    2. `:load proof`
    3. Enter one of the cases below

Working Test cases:
    validate [Assign "x" (F Size [(Val (VIntList [5]))])]
      -> (fromList [("x","a0")],[C "a0" Eq (VInt 1)],["b0"])
    validate [Assign "x" (Val (VIntList [5, 4])), Assign "y" (F Size [(Var "x")])]
      -> (fromList [("x","a0"),("y","b0")],[C "a0" Eq (VIntList [5,4]),FApp "b0" Size ["a0"],C "b0" Eq (VInt 2)],["c0"])
    validate [Assign "x" (F Size [(Val (VIntList [5]))]), Assign "y" (F Minus [(Val (VInt 1)), (Val (VInt 1))])]
    validate [Assign "x" (Val (VInt 5)),  ProofAssert (C "x" Eq (VInt 5))]
    validate [Assign "x" (Val (VInt 5)), Rewrite (EqToLtPlus1 "x"), ProofAssert (C "x" Lt (VInt 6))]
      -> (fromList [("x","a0")],[C "a0" Eq (VInt 5),A "a0" Lt "b0",FApp "b0" Plus ["a0","c0"],C "c0" Eq (VInt 1),C "b0" Eq (VInt 6),C "a0" Lt (VInt 6)],["d0"])
    validate [Assign "x" (Val (VInt 5)), AssignProofVar "a" (Val (VInt 5)), Rewrite (Refl "x"), ProofAssert (A "x" Eq "a")]

Working Error cases:
    validate [ProofAssert (C "x" Lt (VInt 5))]
    validate [Assign "x" (Val (VInt 5)), ProofAssert (C "x" Lt (VInt 4))]
    