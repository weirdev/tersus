module StdLib where

import Data.Map (Map, fromList, toList)

import TersusTypes

-- TODO: Separate this into primitive functions and true std lib
-- TODO: Write std lib as text to be parsed

builtinFunct :: BuiltinFunct -> Value
builtinFunct Size = VFunct ["list"] [] [] (BuiltinFunct Size) []
builtinFunct First =
    VFunct
        ["list"]
        [ AssignProofVar "s" (F (Val (builtinFunct Size)) [Var "list"])
        , Rewrite (UserRewrite "eqToGtZero" [ATerm "s"])
        , ProofAssert
            ( FApp
                (CTerm (builtinFunct (Rel Gt)))
                [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 0)]
            )
        ]
        []
        (BuiltinFunct First)
        []
builtinFunct Last =
    VFunct
        ["list"]
        [ AssignProofVar "s" (F (Val (builtinFunct Size)) [Var "list"])
        , Rewrite (UserRewrite "eqToGtZero" [ATerm "s"])
        , ProofAssert
            ( FApp
                (CTerm (builtinFunct (Rel Gt)))
                [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 0)]
            )
        ]
        []
        (BuiltinFunct Last)
        []
-- get requires a valid index. The contract is checked with checkRel so that a concrete
-- list and index need no proof from the caller, while symbolic ones must already have
-- 0 <= index < size(list) in the proof context.
builtinFunct Get =
    VFunct
        ["list", "index"]
        [ Rewrite (CheckRel (FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm "index", CTerm (VInt 0)]))
        , Rewrite (CheckRel (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "index", FApp (CTerm (builtinFunct Size)) [ATerm "list"]]))
        , ProofAssert (FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm "index", CTerm (VInt 0)])
        , ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "index", FApp (CTerm (builtinFunct Size)) [ATerm "list"]])
        ]
        []
        (BuiltinFunct Get)
        []
-- push adds an element at the end, so the result is one longer than the input list and its
-- last element (at the old size) is x.
builtinFunct Push =
    VFunct
        ["list", "x"]
        []
        []
        (BuiltinFunct Push)
        [ FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Size)) [ATerm "return"]
            , FApp (CTerm (builtinFunct Plus)) [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 1)]
            ]
        , FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Get)) [ATerm "return", FApp (CTerm (builtinFunct Size)) [ATerm "list"]]
            , ATerm "x"
            ]
        ]
-- set replaces one element, so it needs a valid index like get, and the result has the same
-- size as the input list, and x at that index. The list itself is not changed: the result is
-- a new list. What happens to the other elements is not stated yet.
builtinFunct Set =
    VFunct
        ["list", "index", "x"]
        [ Rewrite (CheckRel (FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm "index", CTerm (VInt 0)]))
        , Rewrite (CheckRel (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "index", FApp (CTerm (builtinFunct Size)) [ATerm "list"]]))
        , ProofAssert (FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm "index", CTerm (VInt 0)])
        , ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm "index", FApp (CTerm (builtinFunct Size)) [ATerm "list"]])
        ]
        []
        (BuiltinFunct Set)
        [ FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Size)) [ATerm "return"]
            , FApp (CTerm (builtinFunct Size)) [ATerm "list"]
            ]
        , FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Get)) [ATerm "return", ATerm "index"]
            , ATerm "x"
            ]
        ]
builtinFunct Plus = VFunct ["a", "b"] [] [] (BuiltinFunct Plus) []
builtinFunct Minus = VFunct ["a", "b"] [] [] (BuiltinFunct Minus) []
builtinFunct (Rel rel) = VFunct ["a", "b"] [] [] (BuiltinFunct (Rel rel)) []

stdLibCtx :: Map Variable Value
stdLibCtx =
    fromList
        [ ("size", builtinFunct Size)
        , ("first", builtinFunct First)
        , ("last", builtinFunct Last)
        , ("get", builtinFunct Get)
        , ("push", builtinFunct Push)
        , ("set", builtinFunct Set)
        , ("+", builtinFunct Plus)
        , ("-", builtinFunct Minus)
        , ("=", builtinFunct (Rel Eq))
        , ("<", builtinFunct (Rel Lt))
        , (">", builtinFunct (Rel Gt))
        , ("<=", builtinFunct (Rel LtEq))
        , (">=", builtinFunct (Rel GtEq))
        ]

eqProof :: IotaProof
eqProof = CTerm (builtinFunct (Rel Eq))

eqVarProof :: VariableProof
eqVarProof = CTerm (builtinFunct (Rel Eq))

stdLibValCtx :: (Map Variable Iota, [IotaProof])
stdLibValCtx = stdLibCtxToValCtx stdLibCtx

stdLibRuleCtx :: RuleContext
stdLibRuleCtx =
    fromList
        [ ( "eqToLtPlus1"
          , AxiomRule
                ["x"]
                []
                [ AssignProofVar "xPlusOne" (F (Val (builtinFunct Plus)) [Var "x", Val (VInt 1)])
                , ProofAssert
                    ( FApp
                        (CTerm (builtinFunct (Rel Lt)))
                        [ATerm "x", ATerm "xPlusOne"]
                    )
                ]
          )
        , ( "eqToGtZero"
          , AxiomRule
                ["x"]
                [ Rewrite (CheckGtZero (ATerm "x"))
                , ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])
                ]
                [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])]
          )
        ]

-- NOTE: Could also take iotaseq as input here
stdLibCtxToValCtx :: Map Variable Value -> (Map Variable Iota, [IotaProof])
stdLibCtxToValCtx ctx =
    let (varIotas, proofs) = stdLibCtxToValCtxHelper (toList ctx)
     in (fromList varIotas, proofs)

stdLibCtxToValCtxHelper :: [(Variable, Value)] -> ([(Variable, Iota)], [IotaProof])
stdLibCtxToValCtxHelper [] = ([], [])
-- Seed validation with one fresh symbolic name per stdlib binding plus a proof that
-- the symbolic name is equal to the concrete builtin value.
stdLibCtxToValCtxHelper ((var, functDef) : rest) =
    let newVarIota = (var, Iota var)
     in let newProof = FApp eqProof [ATerm (Iota var), CTerm functDef]
         in let (restVarIota, restProof) = stdLibCtxToValCtxHelper rest
             in (newVarIota : restVarIota, newProof : restProof)
