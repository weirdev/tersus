module StdLib where

import Data.Map (Map, fromList, toList)

import TersusTypes

builtinFunct :: Funct -> Value
builtinFunct Size = VFunct ["list"] [] (BuiltinFunct Size) []
builtinFunct First = VFunct ["list"] [] (BuiltinFunct First) []
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
    let newVarIota = (var, var)
     in let newProof = FApp (Rel Eq) [ATerm var, CTerm functDef]
         in let (restVarIota, restProof) = stdLibCtxToValCtxHelper rest
             in (newVarIota : restVarIota, newProof : restProof)