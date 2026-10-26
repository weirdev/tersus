module StdLib
    ( builtinFunct
    , comparable
    , eqProof
    , eqVarProof
    , evalBuiltinFunct
    , relProof
    , stdLibCtx
    , stdLibRuleCtx
    , stdLibValCtx
    ) where

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
-- pop takes the last element out, so the list must have one; the result is one shorter and keeps the others in their places. The
-- result is also equal to the term pop(list).
builtinFunct Pop =
    VFunct
        ["list"]
        [ Rewrite (CheckRel (relProof Gt (FApp (CTerm (builtinFunct Size)) [ATerm "list"]) (CTerm (VInt 0))))
        , ProofAssert (relProof Gt (FApp (CTerm (builtinFunct Size)) [ATerm "list"]) (CTerm (VInt 0)))
        ]
        []
        (BuiltinFunct Pop)
        [ relProof Eq (ATerm "return") (FApp (CTerm popSymbol) [ATerm "list"])
        , relProof Eq (FApp (CTerm (builtinFunct Size)) [ATerm "return"]) (FApp (CTerm (builtinFunct Minus)) [FApp (CTerm (builtinFunct Size)) [ATerm "list"], CTerm (VInt 1)])
        , Forall
            "j"
            [ relProof GtEq (BVar "j") (CTerm (VInt 0))
            , relProof Lt (BVar "j") (FApp (CTerm (builtinFunct Size)) [ATerm "return"])
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
-- array(n, x) is an array of n copies of x, so it needs a size that is not negative. Its size is n and every element is x;
-- the result is also equal to the term array(n, x). An array has no push: its size never changes, which is all that makes this
-- a fact a caller can keep.
builtinFunct NewArray =
    VFunct
        ["n", "x"]
        [ Rewrite (CheckRel (relProof GtEq (ATerm "n") (CTerm (VInt 0))))
        , ProofAssert (relProof GtEq (ATerm "n") (CTerm (VInt 0)))
        ]
        []
        (BuiltinFunct NewArray)
        [ relProof Eq (ATerm "return") (FApp (CTerm newArraySymbol) [ATerm "n", ATerm "x"])
        , relProof Eq (FApp (CTerm (builtinFunct Size)) [ATerm "return"]) (ATerm "n")
        , Forall
            "j"
            [ relProof GtEq (BVar "j") (CTerm (VInt 0))
            , relProof Lt (BVar "j") (ATerm "n")
            ]
            (relProof Eq (FApp (CTerm (builtinFunct Get)) [ATerm "return", BVar "j"]) (ATerm "x"))
        ]
-- Array::boxed(n, x) promises what array(n, x) does, for an n that need not be a constant
builtinFunct NewBoxedArray =
    case builtinFunct NewArray of
        VFunct params ins outs _ proofs -> VFunct params ins outs (BuiltinFunct NewBoxedArray) proofs
        other -> other
-- Array::empty() is the array of no elements
builtinFunct NewEmptyArray =
    VFunct
        []
        []
        []
        (BuiltinFunct NewEmptyArray)
        [ relProof Eq (FApp (CTerm (builtinFunct Size)) [ATerm "return"]) (CTerm (VInt 0))
        ]
-- writeError(b) is writeByte(b) on the standard error
builtinFunct WriteError =
    VFunct
        ["b"]
        []
        []
        (BuiltinFunct WriteError)
        [relProof Eq (ATerm "return") (ATerm "b")]
-- writeByte(b) writes the Byte b to the standard output and is b
builtinFunct WriteByte =
    VFunct
        ["b"]
        []
        []
        (BuiltinFunct WriteByte)
        [relProof Eq (ATerm "return") (ATerm "b")]
-- toByte(x) is x as a Byte: x has to be from 0 to 255. toInt(b) is b as an Int.
builtinFunct ToByte =
    VFunct
        ["x"]
        [ Rewrite (CheckRel (relProof GtEq (ATerm "x") (CTerm (VInt 0))))
        , ProofAssert (relProof GtEq (ATerm "x") (CTerm (VInt 0)))
        , Rewrite (CheckRel (relProof Lt (ATerm "x") (CTerm (VInt 256))))
        , ProofAssert (relProof Lt (ATerm "x") (CTerm (VInt 256)))
        ]
        []
        (BuiltinFunct ToByte)
        [relProof Eq (ATerm "return") (ATerm "x")]
builtinFunct FromByte = VFunct ["b"] [] [] (BuiltinFunct FromByte) [relProof Eq (ATerm "return") (ATerm "b")]
-- The List<Byte> of a list of Ints that is written out: the same list
builtinFunct BytesFrom = VFunct ["list"] [] [] (BuiltinFunct BytesFrom) []
-- readByte() is the next byte of the standard input, or -1 at its end: it is not known beyond that, so a program has to test what it relies on
builtinFunct ReadByte =
    VFunct
        []
        []
        []
        (BuiltinFunct ReadByte)
        [ relProof GtEq (ATerm "return") (CTerm (VInt (-1)))
        , relProof Lt (ATerm "return") (CTerm (VInt 256))
        ]
-- Unsize b is b: the Box has the same value, it carries the size
builtinFunct Unsize = VFunct ["box"] [] [] (BuiltinFunct Unsize) []
-- The array that a literal makes is the list of its elements, read as an array: the same value
builtinFunct ArrayFrom = VFunct ["list"] [] [] (BuiltinFunct ArrayFrom) []
-- Box::new(x) is x: a Box has the value of what it holds
builtinFunct NewBox = VFunct ["value"] [] [] (BuiltinFunct NewBox) []
builtinFunct UnBox = VFunct ["box"] [] [] (BuiltinFunct UnBox) []
builtinFunct (Ctor name fields) = VFunct fields [] [] (BuiltinFunct (Ctor name fields)) []
builtinFunct (Field owner field) = VFunct ["struct"] [] [] (BuiltinFunct (Field owner field)) []
builtinFunct (Is variant) = VFunct ["value"] [] [] (BuiltinFunct (Is variant)) []
-- A cast demands the proof that the value is the variant, and does nothing when it runs
builtinFunct (Cast variant) =
    VFunct
        ["value"]
        [ProofAssert (FApp (CTerm (builtinFunct (Is variant))) [ATerm "value"])]
        []
        (BuiltinFunct (Cast variant))
        []
builtinFunct (Project variant field) = VFunct ["value"] [] [] (BuiltinFunct (Project variant field)) []
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
-- Modulo by zero is rejected the same way
builtinFunct Mod =
    VFunct
        ["a", "b"]
        [ Rewrite (CheckRel (relProof NotEq (ATerm "b") (CTerm (VInt 0))))
        , ProofAssert (relProof NotEq (ATerm "b") (CTerm (VInt 0)))
        ]
        []
        (BuiltinFunct Mod)
        []
builtinFunct (Rel rel) = VFunct ["a", "b"] [] [] (BuiltinFunct (Rel rel)) []
builtinFunct Within = VFunct ["a", "b"] [] [] (BuiltinFunct Within) []

stdLibCtx :: Map Variable Value
stdLibCtx =
    fromList
        [ ("size", builtinFunct Size)
        , ("first", builtinFunct First)
        , ("last", builtinFunct Last)
        , ("get", builtinFunct Get)
        , ("push", builtinFunct Push)
        , ("pop", builtinFunct Pop)
        , ("set", builtinFunct Set)
        , ("array", builtinFunct NewArray)
        , ("writeByte", builtinFunct WriteByte)
        , ("writeError", builtinFunct WriteError)
        , ("readByte", builtinFunct ReadByte)
        , ("toByte", builtinFunct ToByte)
        , ("toInt", builtinFunct FromByte)
        , ("+", builtinFunct Plus)
        , ("-", builtinFunct Minus)
        , ("*", builtinFunct Times)
        , ("/", builtinFunct Div)
        , ("%", builtinFunct Mod)
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
evalBuiltinFunct Pop [VList []] = Error "Pop requires a non-empty list"
evalBuiltinFunct Pop [VList l] = Ok $ VList (init l)
evalBuiltinFunct Pop _ = Error "Pop only valid for a list"
evalBuiltinFunct Set [VList l, VInt i, x]
    | i < 0 || i >= fromIntegral (length l) = Error "Set index out of range"
    | otherwise = let (before, after) = splitAt (fromIntegral i) l in Ok $ VList (before ++ x : drop 1 after)
evalBuiltinFunct Set _ = Error "Set only valid for a list, an int and an element"
-- (an array too large to write out is not evaluated: the validator knows its size from the contract, and does not need it)
evalBuiltinFunct NewArray [VInt n, x]
    | n >= 0 && n <= maxUnfolded = Ok $ VList (replicate (fromIntegral n) x)
    | otherwise = Error "The array is not evaluated"
evalBuiltinFunct NewArray _ = Error "array takes a size and an element"
evalBuiltinFunct NewBoxedArray args = evalBuiltinFunct NewArray args
evalBuiltinFunct NewEmptyArray [] = Ok (VList [])
evalBuiltinFunct WriteByte [VInt b] = Ok (VInt b)
evalBuiltinFunct WriteByte _ = Error "writeByte takes one byte"
evalBuiltinFunct WriteError [VInt b] = Ok (VInt b)
evalBuiltinFunct WriteError _ = Error "writeError takes one byte"
evalBuiltinFunct ToByte [VInt x]
    | x >= 0 && x < 256 = Ok (VInt x)
    | otherwise = Error "toByte needs an Int from 0 to 255"
evalBuiltinFunct ToByte _ = Error "toByte takes one Int"
evalBuiltinFunct FromByte [VInt b] = Ok (VInt b)
evalBuiltinFunct FromByte _ = Error "toInt takes one Byte"
evalBuiltinFunct BytesFrom [VList l]
    | all isByte l = Ok (VList l)
  where
    isByte (VInt x) = x >= 0 && x < 256
    isByte _ = False
evalBuiltinFunct BytesFrom _ = Error "A list of bytes is written with numbers from 0 to 255"
-- (not a value that can be worked out: what it gives is the input, which a proof does not have, so the proof engine may not fold a call to a constant)
evalBuiltinFunct ReadByte _ = Error "readByte reads the input, so it has no value to evaluate"
evalBuiltinFunct Unsize [value] = Ok value
evalBuiltinFunct Unsize _ = Error "unsize takes one Box"
evalBuiltinFunct ArrayFrom [VList l] = Ok $ VList l
evalBuiltinFunct ArrayFrom _ = Error "An array literal is made from a list"
evalBuiltinFunct NewBox [value] = Ok value
evalBuiltinFunct NewBox _ = Error "Box::new takes one value"
evalBuiltinFunct UnBox [value] = Ok value
evalBuiltinFunct UnBox _ = Error "Box::unbox takes one Box"
evalBuiltinFunct (Ctor name fields) args
    | length fields == length args = Ok $ VData name (zip fields args)
    | otherwise = Error ("Struct " ++ name ++ " takes " ++ show (length fields) ++ " fields, got " ++ show (length args))
evalBuiltinFunct (Field owner field) [VData name fields]
    | maybe False (/= name) owner = Error ("Expected a " ++ maybe "" id owner ++ " but got a " ++ name)
    | otherwise =
    case lookup field fields of
        Just value -> Ok value
        Nothing -> Error ("Struct " ++ name ++ " has no field " ++ field ++ " (reading it after a cast to the wrong variant is undefined behaviour)")
evalBuiltinFunct (Is variant) [VData name _] = Ok $ VBool (name == variant)
evalBuiltinFunct (Is _) _ = Error "Is only tests the variant of an enum value"
evalBuiltinFunct (Project variant field) [VData name fields]
    | name /= variant = Error ("Expected a " ++ variant ++ " but got a " ++ name)
    | otherwise = maybe (Error ("Variant " ++ variant ++ " has no field " ++ field)) Ok (lookup field fields)
evalBuiltinFunct Within [inner, outer] = Ok $ VBool (partOf inner outer)
  where
    partOf part (VData _ fields) = any (\(_, field) -> field == part || partOf part field) fields
    partOf _ _ = False
evalBuiltinFunct Within _ = Error "Within takes two values"
evalBuiltinFunct (Cast _) [value] = Ok value
evalBuiltinFunct (Cast _) _ = Error "A cast takes one value"
evalBuiltinFunct (Project _ _) _ = Error "A field can only be read from an enum value"
evalBuiltinFunct (Field _ _) _ = Error "A field can only be read from a struct"
evalBuiltinFunct Minus [VInt v1, VInt v2] = checkedInt (v1 - v2)
evalBuiltinFunct Minus _ = Error "Minus only valid for two ints"
evalBuiltinFunct Plus [VInt v1, VInt v2] = checkedInt (v1 + v2)
evalBuiltinFunct Plus _ = Error "Plus only valid for two ints"
evalBuiltinFunct Times [VInt v1, VInt v2] = checkedInt (v1 * v2)
evalBuiltinFunct Times _ = Error "Times only valid for two ints"
evalBuiltinFunct Div [VInt _, VInt 0] = Error "Division by zero"
evalBuiltinFunct Div [VInt v1, VInt v2] = checkedInt (v1 `div` v2)
evalBuiltinFunct Div _ = Error "Div only valid for two ints"
evalBuiltinFunct Mod [VInt _, VInt 0] = Error "Modulo by zero"
evalBuiltinFunct Mod [VInt v1, VInt v2] = Ok $ VInt (v1 `mod` v2)
evalBuiltinFunct Mod _ = Error "Mod only valid for two ints"
evalBuiltinFunct (Rel Eq) [v1, v2] | comparable v1 v2 = Ok $ VBool (v1 == v2)
evalBuiltinFunct (Rel Eq) _ = Error "Eq only valid for two values of the same kind that are not functions"
evalBuiltinFunct (Rel NotEq) [v1, v2] | comparable v1 v2 = Ok $ VBool (v1 /= v2)
evalBuiltinFunct (Rel NotEq) _ = Error "NotEq only valid for two values of the same kind that are not functions"
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

popSymbol :: Value
popSymbol = VFunct ["list"] [] [] (BuiltinFunct Pop) []

pushSymbol :: Value
pushSymbol = VFunct ["list", "x"] [] [] (BuiltinFunct Push) []

setSymbol :: Value
setSymbol = VFunct ["list", "index", "x"] [] [] (BuiltinFunct Set) []

newArraySymbol :: Value
newArraySymbol = VFunct ["n", "x"] [] [] (BuiltinFunct NewArray) []

-- The largest array that the validator writes out as a value when it knows the size
maxUnfolded :: Integer
maxUnfolded = 1024

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

-- An Int result that does not fit in 64 bits is an error, as in compiled code (addition, subtraction and
-- multiplication overflow, and so does minInt / -1)
checkedInt :: Integer -> Result Value String
checkedInt n
    | inIntRange n = Ok (VInt n)
    | otherwise = Error "Integer overflow"

-- Equality is structural, for any two values that are not functions
comparable :: Value -> Value -> Bool
comparable VFunct{} _ = False
comparable _ VFunct{} = False
comparable VFnRef{} _ = False
comparable _ VFnRef{} = False
comparable (VInt _) (VInt _) = True
comparable (VBool _) (VBool _) = True
comparable (VList _) (VList _) = True
comparable (VData _ _) (VData _ _) = True
comparable _ _ = False
