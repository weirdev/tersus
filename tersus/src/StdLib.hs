module StdLib
    ( builtinFunct
    , comparable
    , eqProof
    , eqVarProof
    , evalBuiltinFunct
    , relProof
    , stdLibRuleCtx
    ) where

import Data.Map (fromList)

import BuiltinRegistry
import Types
import Syntax
import Utils

-- A builtin as a value: the parameter names of its registry entry, with the contract of a
-- PrimitiveContract entry and without one otherwise. The contract of a ParsedContract entry is the
-- `builtin fn` declaration of lib/stdlib.tersus that StdLibDefs parses; the value made here, which
-- is how a proof names such a builtin, carries none.
builtinFunct :: BuiltinFunct -> Value
builtinFunct b = case contractSpec b of
    PrimitiveContract ins outs -> VFunct (entryParams (entryFor b) b) ins [] (BuiltinFunct b) outs
    _ -> VFunct (entryParams (entryFor b) b) [] [] (BuiltinFunct b) []

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
evalBuiltinFunct ArrayFromList [VList l] = Ok (VList l)
evalBuiltinFunct ArrayFromList _ = Error "Array::fromList takes a list"
evalBuiltinFunct WriteByte [VInt b] = Ok (VInt b)
evalBuiltinFunct WriteByte _ = Error "writeByte takes one byte"
evalBuiltinFunct WriteError [VInt b] = Ok (VInt b)
evalBuiltinFunct WriteError _ = Error "writeError takes one byte"
evalBuiltinFunct ToByte [VInt x]
    | x >= 0 && x < 256 = Ok (VInt x)
    | otherwise = Error "toByte needs an Int from 0 to 255"
evalBuiltinFunct ToByte _ = Error "toByte takes one Int"
evalBuiltinFunct FromByte [VInt b] = Ok (VInt b)
evalBuiltinFunct (ToWord signed bits) [VInt x]
    | x >= fst (wordRange signed bits) && x < snd (wordRange signed bits) = Ok (VInt x)
    | otherwise = Error (wordName signed bits ++ "::from needs an Int in the range of " ++ wordName signed bits)
evalBuiltinFunct FromByte _ = Error "toInt takes one Byte"
evalBuiltinFunct BytesFrom [VList l]
    | all isByte l = Ok (VList l)
  where
    isByte (VInt x) = x >= 0 && x < 256
    isByte _ = False
evalBuiltinFunct BytesFrom _ = Error "A list of bytes is written with numbers from 0 to 255"
-- (not a value that can be worked out: what it gives is the input, which a proof does not have, so the proof engine may not fold a call to a constant)
evalBuiltinFunct ReadByte _ = Error "readByte reads the input, so it has no value to evaluate"
evalBuiltinFunct ArgCount _ = Error "argCount is the arguments of the program, so it has no value to evaluate"
evalBuiltinFunct ArgByte _ = Error "argByte is the arguments of the program, so it has no value to evaluate"
evalBuiltinFunct b _ | b `elem` [PathByte, FileLoad, FileByte, StoreByte, FileStore] = Error "a file operation is the files of the program, so it has no value to evaluate"
evalBuiltinFunct Unsize [value] = Ok value
evalBuiltinFunct Unsize _ = Error "unsize takes one Box"
evalBuiltinFunct ArrayFrom [VList l] = Ok $ VList l
evalBuiltinFunct ArrayFrom _ = Error "An array literal is made from a list"
evalBuiltinFunct NewBox [value] = Ok value
evalBuiltinFunct NewBox _ = Error "Box::new takes one value"
evalBuiltinFunct UnBox [value] = Ok value
evalBuiltinFunct UnBox _ = Error "Box::unbox takes one Box"
evalBuiltinFunct CloneOf [value] = Ok value
evalBuiltinFunct CloneOf _ = Error "clone takes one value"
evalBuiltinFunct (Ctor name _ fields) args
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
evalBuiltinFunct And [VBool a, VBool b] = Ok (VBool (a && b))
evalBuiltinFunct And _ = Error "&& only valid for two Bools"
evalBuiltinFunct Or [VBool a, VBool b] = Ok (VBool (a || b))
evalBuiltinFunct Or _ = Error "|| only valid for two Bools"
evalBuiltinFunct Not [VBool a] = Ok (VBool (not a))
evalBuiltinFunct Not _ = Error "! only valid for a Bool"
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
-- (an address is not a value a proof works out: it is new at each allocation, and memory is what a permission says)
evalBuiltinFunct b _ = Error (show b ++ " is an operation on memory, so it has no value to evaluate")


eqProof :: IotaProof
eqProof = CTerm (builtinFunct (Rel Eq))

eqVarProof :: VariableProof
eqVarProof = CTerm (builtinFunct (Rel Eq))

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
-- The largest array that the validator writes out as a value when it knows the size
maxUnfolded :: Integer
maxUnfolded = 1024

relProof :: Rel -> VariableProof -> VariableProof -> VariableProof
relProof rel lhs rhs = FApp (CTerm (builtinFunct (Rel rel))) [lhs, rhs]

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
