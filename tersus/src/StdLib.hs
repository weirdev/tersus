module StdLib where

import Data.Map (Map, fromList, toList)

import TersusTypes

-- TODO: Separate this into primitive functions and true std lib
-- TODO: Write std lib as text to be parsed

builtinFunct :: BuiltinFunct -> Value
builtinFunct Size = VFunct ["list"] [] (BuiltinFunct Size) []
builtinFunct First =
    VFunct
        ["list"]
        [ AssignProofVar "s" (F (Val (builtinFunct Size)) [Var "list"])
        -- , Rewrite (Eval "s")
        , Rewrite (EqToGtZero "s")
        , ProofAssert
            ( FApp
                (CTerm (builtinFunct (Rel Gt)))
                [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 0)]
            )
        ]
        (BuiltinFunct First)
        []
builtinFunct Last = VFunct ["list"] [] (BuiltinFunct Last) []
builtinFunct Plus = VFunct ["a", "b"] [] (BuiltinFunct Plus) []
builtinFunct Minus = VFunct ["a", "b"] [] (BuiltinFunct Minus) []
builtinFunct (Rel rel) = VFunct ["a", "b"] [] (BuiltinFunct (Rel rel)) []

stdLibCtx :: Map Variable Value
stdLibCtx =
    fromList
        [ ("size", builtinFunct Size)
        , ("first", builtinFunct First)
        , ("last", builtinFunct Last)
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

-- NOTE: Could also take iotaseq as input here
stdLibCtxToValCtx :: Map Variable Value -> (Map Variable Iota, [IotaProof])
stdLibCtxToValCtx ctx =
    let (varIotas, proofs) = stdLibCtxToValCtxHelper (toList ctx)
     in (fromList varIotas, proofs)

stdLibCtxToValCtxHelper :: [(Variable, Value)] -> ([(Variable, Iota)], [IotaProof])
stdLibCtxToValCtxHelper [] = ([], [])
stdLibCtxToValCtxHelper ((var, functDef) : rest) =
    let newVarIota = (var, Iota var)
     in let newProof = FApp eqProof [ATerm (Iota var), CTerm functDef]
         in let (restVarIota, restProof) = stdLibCtxToValCtxHelper rest
             in (newVarIota : restVarIota, newProof : restProof)