module MirEval
    ( MirValue (..)
    , runProgram
    , renderMirValue
    ) where

import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir
import TersusTypes (Name, Rel (..), Variable)
import Utils

-- Runs the MIR: a function is its locals and the block it is in. The statements of the block run, then the
-- terminator says where to go next. The operations that need a contract the validator proved (a divisor that is not 0,
-- an index in range) still check it and report an error, so that a mistake of the validator is a failure here instead
-- of a wrong answer, as it is in the evaluator of the AST.
data MirValue
    = MInt Integer
    | MBool Bool
    | MList [MirValue]
    | MData Name [(Variable, MirValue)]
    | MFn Name
    deriving (Eq, Show)

-- The value of _0 when the program returns, and Nothing when it ends without
runProgram :: Program -> Result (Maybe MirValue) String
runProgram program = runFunction program (progMain program) []

runFunction :: Program -> Function -> [MirValue] -> Result (Maybe MirValue) String
runFunction program fn args
    | length args /= length (fnParams fn) =
        Error ("Function expected " ++ show (length (fnParams fn)) ++ " arguments, got " ++ show (length args))
    | otherwise = runBlock program fn (BlockId 0) (Map.fromList (zip (fnParams fn) args))

type Frame = Map Local MirValue

runBlock :: Program -> Function -> BlockId -> Frame -> Result (Maybe MirValue) String
runBlock program fn block frame =
    case Map.lookup block (fnBlocks fn) of
        Nothing -> Error ("Jump to a block that does not exist: " ++ show block)
        Just (BasicBlock stmts term) ->
            runStatements frame stmts `bindResult` \frame' ->
                case term of
                    Goto next -> runBlock program fn next frame'
                    SwitchBool test yes no ->
                        operandValue frame' test `bindResult` \v -> case v of
                            MBool True -> runBlock program fn yes frame'
                            MBool False -> runBlock program fn no frame'
                            _ -> Error "Condition must be a boolean"
                    Call callee args dest next ->
                        operandValue frame' callee `bindResult` \f ->
                            mapResults (operandValue frame') args `bindResult` \argValues ->
                                callFunction program f argValues `bindResult` \result ->
                                    runBlock program fn next (Map.insert dest result frame')
                    Return -> Ok (Map.lookup (Local 0) frame')
                    Unreachable -> Error "Function did not return a value"

callFunction :: Program -> MirValue -> [MirValue] -> Result MirValue String
callFunction program (MFn name) args =
    case Map.lookup name (progFunctions program) of
        Nothing -> Error ("Call of a function that does not exist: " ++ name)
        Just fn -> runFunction program fn args `bindResult` maybe (Error "Function did not return a value") Ok
callFunction _ _ _ = Error "Object being called must be a function"

mapResults :: (a -> Result b String) -> [a] -> Result [b] String
mapResults = flatResultMap

runStatements :: Frame -> [Statement] -> Result Frame String
runStatements frame [] = Ok frame
runStatements frame (Ghost{} : rest) = runStatements frame rest
runStatements frame (Assign dest rv : rest) =
    evalRvalue frame rv `bindResult` \v -> runStatements (Map.insert dest v frame) rest

operandValue :: Frame -> Operand -> Result MirValue String
operandValue frame (Copy l) = maybe (Error ("Undefined variable: " ++ show l)) Ok (Map.lookup l frame)
operandValue _ (Const c) = Ok (constantValue c)

constantValue :: Constant -> MirValue
constantValue (CInt i) = MInt i
constantValue (CBool b) = MBool b
constantValue (CList cs) = MList (map constantValue cs)
constantValue (CData name fields) = MData name [(f, constantValue c) | (f, c) <- fields]
constantValue (CFn name) = MFn name

evalRvalue :: Frame -> Rvalue -> Result MirValue String
evalRvalue frame rv =
    case rv of
        Use o -> operandValue frame o
        BinaryOp op a b -> operandValue frame a `bindResult` \x -> operandValue frame b `bindResult` \y -> binary op x y
        ListOp op os -> mapResults (operandValue frame) os `bindResult` listOp op
        MakeList os -> MList <$$> mapResults (operandValue frame) os
        MakeData name fields -> MData name <$$> mapResults (\(f, o) -> (,) f <$$> operandValue frame o) fields
        ReadField o name field ->
            operandValue frame o `bindResult` \v -> case v of
                MData actual fields
                    | actual /= name -> Error ("Expected a " ++ name ++ " but got a " ++ actual)
                    | otherwise -> maybe (Error ("Variant " ++ name ++ " has no field " ++ field)) Ok (lookup field fields)
                _ -> Error "A field can only be read from a struct"
        IsVariant o name ->
            operandValue frame o `bindResult` \v -> case v of
                MData actual _ -> Ok (MBool (actual == name))
                _ -> Error "Is only tests the variant of an enum value"
  where
    f <$$> r = mapResult f r

binary :: BinOp -> MirValue -> MirValue -> Result MirValue String
binary Add (MInt a) (MInt b) = checked (a + b)
binary Sub (MInt a) (MInt b) = checked (a - b)
binary Mul (MInt a) (MInt b) = checked (a * b)
binary Div (MInt _) (MInt 0) = Error "Division by zero"
binary Div (MInt a) (MInt b) = checked (a `div` b)
binary Mod (MInt _) (MInt 0) = Error "Modulo by zero"
binary Mod (MInt a) (MInt b) = Ok (MInt (a `mod` b))
binary (Compare Eq) a b | comparable a b = Ok (MBool (a == b))
binary (Compare NotEq) a b | comparable a b = Ok (MBool (a /= b))
binary (Compare Lt) (MInt a) (MInt b) = Ok (MBool (a < b))
binary (Compare Gt) (MInt a) (MInt b) = Ok (MBool (a > b))
binary (Compare LtEq) (MInt a) (MInt b) = Ok (MBool (a <= b))
binary (Compare GtEq) (MInt a) (MInt b) = Ok (MBool (a >= b))
binary op _ _ = Error (show op ++ " is not defined for these values")

-- Int is 64 bits: addition, subtraction, multiplication and division that leave the range stop the program
checked :: Integer -> Result MirValue String
checked n
    | inIntRange n = Ok (MInt n)
    | otherwise = Error "Integer overflow"

-- Equality is structural, for any two values that are not functions
comparable :: MirValue -> MirValue -> Bool
comparable (MInt _) (MInt _) = True
comparable (MBool _) (MBool _) = True
comparable (MList _) (MList _) = True
comparable (MData _ _) (MData _ _) = True
comparable _ _ = False

listOp :: ListOp -> [MirValue] -> Result MirValue String
listOp Length [MList l] = Ok (MInt (fromIntegral (length l)))
listOp First [MList []] = Error "First requires a non-empty list"
listOp First [MList l] = Ok (head l)
listOp Last [MList []] = Error "Last requires a non-empty list"
listOp Last [MList l] = Ok (last l)
listOp Get [MList l, MInt i]
    | i < 0 || i >= fromIntegral (length l) = Error "Get index out of range"
    | otherwise = Ok (l !! fromIntegral i)
listOp Push [MList l, x] = Ok (MList (l ++ [x]))
listOp Set [MList l, MInt i, x]
    | i < 0 || i >= fromIntegral (length l) = Error "Set index out of range"
    | otherwise = let (before, after) = splitAt (fromIntegral i) l in Ok (MList (before ++ x : drop 1 after))
listOp op _ = Error (show op ++ " is not defined for these values")

renderMirValue :: MirValue -> String
renderMirValue (MInt i) = show i
renderMirValue (MBool True) = "true"
renderMirValue (MBool False) = "false"
renderMirValue (MList l) = "[" ++ intercalate ", " (map renderMirValue l) ++ "]"
renderMirValue (MData name []) = name
renderMirValue (MData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderMirValue v | (f, v) <- fields] ++ " }"
renderMirValue MFn{} = "<function>"
