module StdLib where

import Data.Map (Map, fromList, toList)

import TersusTypes
import Utils

-- TODO: Separate this into primitive functions and true std lib
-- TODO: Write std lib as text to be parsed

builtinFunct :: BuiltinFunct -> Value
builtinFunct Size = VFunct ["list"] [] [] (BuiltinFunct Size) []
-- first and last are get at the first and the last index, which is how element facts about the list reach them
builtinFunct First =
    VFunct
        ["list"]
        [ ProofAssert
            ( FApp
                (CTerm (builtinFunct (Rel Gt)))
                [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 0)]
            )
        ]
        []
        (BuiltinFunct First)
        [ FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ATerm "return", FApp (CTerm getSymbol) [ATerm "list", CTerm (VInt 0)]]
        ]
builtinFunct Last =
    VFunct
        ["list"]
        [ ProofAssert
            ( FApp
                (CTerm (builtinFunct (Rel Gt)))
                [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 0)]
            )
        ]
        []
        (BuiltinFunct Last)
        [ FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ATerm "return", FApp (CTerm getSymbol) [ATerm "list", FApp (CTerm (builtinFunct Minus)) [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 1)]]]
        ]
-- get requires a valid index, and its result is equal to the term get(list, index), which is what
-- forall facts about the list are instantiated at. The contract is checked with checkRel so that a concrete
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
        [ FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ATerm "return", FApp (CTerm getSymbol) [ATerm "list", ATerm "index"]]
        ]
-- push adds an element at the end, so the result is one longer than the input list and its
-- last element (at the old size) is x. The elements it already had are unchanged. The result is
-- also equal to the term push(list, x).
builtinFunct Push =
    VFunct
        ["list", "x"]
        []
        []
        (BuiltinFunct Push)
        [ FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ATerm "return", FApp (CTerm pushSymbol) [ATerm "list", ATerm "x"]]
        , FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Size)) [ATerm "return"]
            , FApp (CTerm (builtinFunct Plus)) [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 1)]
            ]
        , FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Get)) [ATerm "return", FApp (CTerm (builtinFunct Size)) [ATerm "list"]]
            , ATerm "x"
            ]
        , -- The elements the list already had are unchanged
          Forall
            "j"
            [ relProof GtEq (BVar "j") (CTerm (VInt 0))
            , relProof Lt (BVar "j") (FApp (CTerm (builtinFunct Size)) [ATerm "list"])
            ]
            (relProof Eq (FApp (CTerm (builtinFunct Get)) [ATerm "return", BVar "j"]) (FApp (CTerm (builtinFunct Get)) [ATerm "list", BVar "j"]))
        ]
-- set replaces one element, so it needs a valid index like get, and the result has the same
-- size as the input list, and x at that index. The list itself is not changed: the result is
-- a new list. Every other element is unchanged. The result is also equal to the term
-- set(list, index, x).
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
            [ATerm "return", FApp (CTerm setSymbol) [ATerm "list", ATerm "index", ATerm "x"]]
        , FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Size)) [ATerm "return"]
            , FApp (CTerm (builtinFunct Size)) [ATerm "list"]
            ]
        , FApp
            (CTerm (builtinFunct (Rel Eq)))
            [ FApp (CTerm (builtinFunct Get)) [ATerm "return", ATerm "index"]
            , ATerm "x"
            ]
        , -- Every other element is unchanged
          Forall
            "j"
            [ relProof GtEq (BVar "j") (CTerm (VInt 0))
            , relProof Lt (BVar "j") (FApp (CTerm (builtinFunct Size)) [ATerm "list"])
            , relProof NotEq (BVar "j") (ATerm "index")
            ]
            (relProof Eq (FApp (CTerm (builtinFunct Get)) [ATerm "return", BVar "j"]) (FApp (CTerm (builtinFunct Get)) [ATerm "list", BVar "j"]))
        ]
builtinFunct Plus = VFunct ["a", "b"] [] [] (BuiltinFunct Plus) []
builtinFunct Minus = VFunct ["a", "b"] [] [] (BuiltinFunct Minus) []
builtinFunct Times = VFunct ["a", "b"] [] [] (BuiltinFunct Times) []
-- Division by zero is rejected, like an out of range index: the divisor must already be known to be non-zero
builtinFunct Div =
    VFunct
        ["a", "b"]
        [ Rewrite (CheckRel (relProof NotEq (ATerm "b") (CTerm (VInt 0))))
        , ProofAssert (relProof NotEq (ATerm "b") (CTerm (VInt 0)))
        ]
        []
        (BuiltinFunct Div)
        []
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
        , ("*", builtinFunct Times)
        , ("/", builtinFunct Div)
        , ("=", builtinFunct (Rel Eq))
        , ("!=", builtinFunct (Rel NotEq))
        , ("<", builtinFunct (Rel Lt))
        , (">", builtinFunct (Rel Gt))
        , ("<=", builtinFunct (Rel LtEq))
        , (">=", builtinFunct (Rel GtEq))
        ]

-- Evaluates a builtin function on concrete arguments
evalBuiltinFunct :: BuiltinFunct -> [Value] -> Result Value String
evalBuiltinFunct Size [VList l] = Ok $ VInt (fromIntegral (length l))
evalBuiltinFunct Size _ = Error "Size only valid for a list"
evalBuiltinFunct First [VList []] = Error "First requires a non-empty list"
evalBuiltinFunct First [VList l] = Ok $ head l
evalBuiltinFunct First _ = Error "First only valid for a list"
evalBuiltinFunct Last [VList []] = Error "Last requires a non-empty list"
evalBuiltinFunct Last [VList l] = Ok $ last l
evalBuiltinFunct Last _ = Error "Last only valid for a list"
evalBuiltinFunct Get [VList l, VInt i]
    | i < 0 || i >= fromIntegral (length l) = Error "Get index out of range"
    | otherwise = Ok $ l !! fromIntegral i
evalBuiltinFunct Get _ = Error "Get only valid for a list and an int"
evalBuiltinFunct Push [VList l, x] = Ok $ VList (l ++ [x])
evalBuiltinFunct Push _ = Error "Push only valid for a list and an element"
evalBuiltinFunct Set [VList l, VInt i, x]
    | i < 0 || i >= fromIntegral (length l) = Error "Set index out of range"
    | otherwise = let (before, after) = splitAt (fromIntegral i) l in Ok $ VList (before ++ x : drop 1 after)
evalBuiltinFunct Set _ = Error "Set only valid for a list, an int and an element"
evalBuiltinFunct Minus [VInt v1, VInt v2] = Ok $ VInt (v1 - v2)
evalBuiltinFunct Minus _ = Error "Minus only valid for two ints"
evalBuiltinFunct Plus [VInt v1, VInt v2] = Ok $ VInt (v1 + v2)
evalBuiltinFunct Plus _ = Error "Plus only valid for two ints"
evalBuiltinFunct Times [VInt v1, VInt v2] = Ok $ VInt (v1 * v2)
evalBuiltinFunct Times _ = Error "Times only valid for two ints"
evalBuiltinFunct Div [VInt _, VInt 0] = Error "Division by zero"
evalBuiltinFunct Div [VInt v1, VInt v2] = Ok $ VInt (v1 `div` v2)
evalBuiltinFunct Div _ = Error "Div only valid for two ints"
evalBuiltinFunct (Rel Eq) [VInt v1, VInt v2] = Ok $ VBool (v1 == v2)
evalBuiltinFunct (Rel Eq) _ = Error "Eq only valid for two ints"
evalBuiltinFunct (Rel NotEq) [VInt v1, VInt v2] = Ok $ VBool (v1 /= v2)
evalBuiltinFunct (Rel NotEq) _ = Error "NotEq only valid for two ints"
evalBuiltinFunct (Rel Lt) [VInt v1, VInt v2] = Ok $ VBool (v1 < v2)
evalBuiltinFunct (Rel Lt) _ = Error "Lt only valid for two ints"
evalBuiltinFunct (Rel Gt) [VInt v1, VInt v2] = Ok $ VBool (v1 > v2)
evalBuiltinFunct (Rel Gt) _ = Error "Rt only valid for two ints"
evalBuiltinFunct (Rel LtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 <= v2)
evalBuiltinFunct (Rel LtEq) _ = Error "LtEq only valid for two ints"
evalBuiltinFunct (Rel GtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 >= v2)
evalBuiltinFunct (Rel GtEq) _ = Error "GtEq only valid for two ints"

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

-- Function symbols for the terms push(list, x) and set(list, index, x) in contracts and frame
-- rules. They cannot be the full builtin values, which contain these very contracts.
getSymbol :: Value
getSymbol = VFunct ["list", "index"] [] [] (BuiltinFunct Get) []

pushSymbol :: Value
pushSymbol = VFunct ["list", "x"] [] [] (BuiltinFunct Push) []

setSymbol :: Value
setSymbol = VFunct ["list", "index", "x"] [] [] (BuiltinFunct Set) []

relProof :: Rel -> VariableProof -> VariableProof -> VariableProof
relProof rel lhs rhs = FApp (CTerm (builtinFunct (Rel rel))) [lhs, rhs]

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
