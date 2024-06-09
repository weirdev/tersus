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
    0. stack run
Tests:
    0. stack test
OR:
    0. From this (tersus/) directory
    1. `ghci`
    2. `:load Proof`
    3. Enter one of the cases below

Working Test cases: (Note see tests, only keeping this list temporarily in case the full validation output is useful)
    validate [Assign "x" (F Size [(Val (VIntList [5]))])]
      -> (fromList [("x","a0")],[FApp (Rel Eq) [ATerm "a0",CTerm (VInt 1)]],["b0"])
    validate [Assign "x" (Val (VIntList [5, 4])), Assign "y" (F Size [(Var "x")])]
      -> (fromList [("x","a0"),("y","b0")],[FApp (Rel Eq) [ATerm "a0",CTerm (VIntList [5,4])],FApp (Rel Eq) [ATerm "b0",FApp Size [ATerm "a0"]],FApp (Rel Eq) [ATerm "b0",CTerm (VInt 2)]],["c0"])
    validate [Assign "x" (F Size [(Val (VIntList [5]))]), Assign "y" (F Minus [(Val (VInt 1)), (Val (VInt 1))])]
      -> (fromList [("x","a0"),("y","b0")],[FApp (Rel Eq) [ATerm "a0",CTerm (VInt 1)],FApp (Rel Eq) [ATerm "b0",CTerm (VInt 0)]],["c0"])
    validate [Assign "x" (Val (VInt 5)),  ProofAssert (FApp (Rel Eq) [ATerm "x", CTerm (VInt 5)])]
      -> (fromList [("x","a0")],[FApp (Rel Eq) [ATerm "a0",CTerm (VInt 5)]],["b0"])
    validate [Assign "x" (Val (VInt 5)), Rewrite (EqToLtPlus1 "x"), ProofAssert (FApp (Rel Lt) [ATerm "x", CTerm (VInt 6)])]
      -> (fromList [("x","a0")],[FApp (Rel Eq) [ATerm "a0",CTerm (VInt 5)],FApp (Rel Lt) [ATerm "a0",ATerm "b0"],FApp (Rel Eq) [ATerm "b0",FApp Plus [ATerm "a0",ATerm "c0"]],FApp (Rel Eq) [ATerm "c0",CTerm (VInt 1)],FApp (Rel Eq) [ATerm "b0",CTerm (VInt 6)],FApp (Rel Lt) [ATerm "a0",CTerm (VInt 6)]],["d0"])
    validate [Assign "x" (Val (VInt 5)), AssignProofVar "a" (Val (VInt 5)), Rewrite (Refl "x"), ProofAssert (FApp (Rel Eq) [ATerm "x", ATerm "a"])]
      -> (fromList [("a","b0"),("x","a0")],[FApp (Rel Eq) [ATerm "a0",CTerm (VInt 5)],FApp (Rel Eq) [ATerm "b0",CTerm (VInt 5)],FApp (Rel Eq) [ATerm "a0",ATerm "b0"],FApp (Rel Eq) [ATerm "b0",ATerm "a0"]],["c0"])
    