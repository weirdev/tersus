module MirEval
    ( MirValue (..)
    , runProgram
    , runProgramOutput
    , runProgramWith
    , runProgramStreams
    , renderMirValue
    , toMirValue
    , fromMirValue
    ) where

import Data.Char (chr)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir
import TersusTypes (Name, Rel (..), Value (..), Variable)
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
runProgram = mapResult snd . runProgramOutput

-- The bytes that the program wrote with writeByte (as characters from 0 to 255), and the value it returns, when there is no input
runProgramOutput :: Program -> Result (String, Maybe MirValue) String
runProgramOutput = runProgramWith ""

-- The same for a program given input, the bytes (as characters from 0 to 255) that readByte reads in turn. The input is read as the program
-- asks for it, so it can be a stream that is not at its end.
runProgramWith :: String -> Program -> Result (String, Maybe MirValue) String
runProgramWith input program = mapResult (\(out, _, value) -> (out, value)) (runProgramStreams input program)

-- The same, with the bytes written to the standard error too (as characters from 0 to 255)
runProgramStreams :: String -> Program -> Result (String, String, Maybe MirValue) String
runProgramStreams input program = mapResult (\(value, (out, err), _) -> (out, err, value)) (runE (runFunction program (progMain program) []) input)

-- What a program has written to the standard output and to the standard error
type Written = (String, String)

none :: Written
none = ("", "")

-- The evaluator is a function of the input that is left, and the failure of a result, with the bytes written so far and the input that is left
newtype E a = E {runE :: String -> Result (a, Written, String) String}

instance Functor E where
    fmap f (E r) = E (\input -> mapResult (\(a, output, rest) -> (f a, output, rest)) (r input))

instance Applicative E where
    pure a = E (\input -> Ok (a, none, input))
    E f <*> E g = E (\input -> f input `bindResult` \(h, o1, rest) -> mapResult (\(a, o2, rest') -> (h a, together o1 o2, rest')) (g rest))

instance Monad E where
    E g >>= f = E (\input -> g input `bindResult` \(a, o1, rest) -> runE (f a) rest `bindResult` \(b, o2, rest') -> Ok (b, together o1 o2, rest'))

together :: Written -> Written -> Written
together (out1, err1) (out2, err2) = (out1 ++ out2, err1 ++ err2)

failE :: String -> E a
failE e = E (\_ -> Error e)

liftE :: Result a String -> E a
liftE r = E (\input -> mapResult (\a -> (a, none, input)) r)

write :: Char -> E ()
write c = E (\input -> Ok ((), ([c], ""), input))

writeError :: Char -> E ()
writeError c = E (\input -> Ok ((), ("", [c]), input))

-- The next byte of the input, or -1 at its end
readInput :: E Integer
readInput = E (\input -> case input of
    [] -> Ok (-1, none, [])
    c : rest -> Ok (toInteger (fromEnum c `mod` 256), none, rest))

runFunction :: Program -> Function -> [MirValue] -> E (Maybe MirValue)
runFunction program fn args
    | length args /= length (fnParams fn) =
        failE ("Function expected " ++ show (length (fnParams fn)) ++ " arguments, got " ++ show (length args))
    | otherwise = runBlock program fn (BlockId 0) (Map.fromList (zip (fnParams fn) args))

type Frame = Map Local MirValue

runBlock :: Program -> Function -> BlockId -> Frame -> E (Maybe MirValue)
runBlock program fn block frame =
    case Map.lookup block (fnBlocks fn) of
        Nothing -> failE ("Jump to a block that does not exist: " ++ show block)
        Just (BasicBlock stmts term) -> do
            frame' <- runStatements frame stmts
            case term of
                Goto next -> runBlock program fn next frame'
                SwitchBool test yes no -> do
                    v <- liftE (operandValue frame' test)
                    case v of
                        MBool True -> runBlock program fn yes frame'
                        MBool False -> runBlock program fn no frame'
                        _ -> failE "Condition must be a boolean"
                Call callee args dest next -> do
                    f <- liftE (operandValue frame' callee)
                    argValues <- liftE (mapResults (operandValue frame') args)
                    result <- callFunction program f argValues
                    runBlock program fn next (Map.insert dest result frame')
                Return -> return (Map.lookup (Local 0) frame')
                Unreachable -> failE "Function did not return a value"

callFunction :: Program -> MirValue -> [MirValue] -> E MirValue
callFunction program (MFn name) args =
    case Map.lookup name (progFunctions program) of
        Nothing -> failE ("Call of a function that does not exist: " ++ name)
        Just fn -> runFunction program fn args >>= maybe (failE "Function did not return a value") return
callFunction _ _ _ = failE "Object being called must be a function"

mapResults :: (a -> Result b String) -> [a] -> Result [b] String
mapResults = flatResultMap

runStatements :: Frame -> [Statement] -> E Frame
runStatements frame [] = return frame
runStatements frame (Ghost{} : rest) = runStatements frame rest
runStatements frame (Drop{} : rest) = runStatements frame rest
runStatements frame (Peek dest rv : rest) = runStatements frame (Assign dest rv : rest)
runStatements frame (Assign dest (ListOp ReadByte []) : rest) = do
    b <- readInput
    runStatements (Map.insert dest (MInt b) frame) rest
runStatements frame (Assign dest (ListOp WriteByte [o]) : rest) = do
    v <- liftE (operandValue frame o)
    case v of
        MInt b -> write (chr (fromIntegral (b `mod` 256))) >> runStatements (Map.insert dest v frame) rest
        _ -> failE "writeByte takes an Int"
runStatements frame (Assign dest (ListOp WriteError [o]) : rest) = do
    v <- liftE (operandValue frame o)
    case v of
        MInt b -> writeError (chr (fromIntegral (b `mod` 256))) >> runStatements (Map.insert dest v frame) rest
        _ -> failE "writeError takes an Int"
runStatements frame (Assign dest rv : rest) = do
    v <- liftE (evalRvalue frame rv)
    runStatements (Map.insert dest v frame) rest

operandValue :: Frame -> Operand -> Result MirValue String
operandValue frame (Copy l) = maybe (Error ("Undefined variable: " ++ show l)) Ok (Map.lookup l frame)
-- (a value is a value here: who owns it only matters to native code, so owned MIR gives the same results)
operandValue frame (Move l) = operandValue frame (Copy l)
operandValue _ (Const c) = Ok (constantValue c)

constantValue :: Constant -> MirValue
constantValue (CInt i) = MInt i
constantValue (CBool b) = MBool b
constantValue (CList cs) = MList (map constantValue cs)
constantValue (CArray cs) = MList (map constantValue cs)
constantValue (CData name fields) = MData (plain name) [(f, constantValue c) | (f, c) <- fields]
constantValue (CFn name) = MFn name

evalRvalue :: Frame -> Rvalue -> Result MirValue String
evalRvalue frame rv =
    case rv of
        Use o -> operandValue frame o
        BinaryOp op a b -> operandValue frame a `bindResult` \x -> operandValue frame b `bindResult` \y -> binary op x y
        ListOp op os -> mapResults (operandValue frame) os `bindResult` listOp op
        MakeList os -> MList <$$> mapResults (operandValue frame) os
        MakeBox o -> operandValue frame o
        Unbox o -> operandValue frame o
        Unsize o -> operandValue frame o
        MakeData name fields -> MData (plain name) <$$> mapResults (\(f, o) -> (,) f <$$> operandValue frame o) fields
        ReadField o name field ->
            operandValue frame o `bindResult` \v -> case v of
                MData actual fields
                    | actual /= plain name -> Error ("Expected a " ++ name ++ " but got a " ++ actual)
                    | otherwise -> maybe (Error ("Variant " ++ name ++ " has no field " ++ field)) Ok (lookup field fields)
                _ -> Error "A field can only be read from a struct"
        -- (a wrong cast is undefined behaviour, as in the evaluator of the AST: reading a field that is not there is the error)
        AsVariant o _ -> operandValue frame o
        Clone o -> operandValue frame o
        TakeField l name field -> evalRvalue frame (ReadField (Copy l) name field)
        IsVariant o name ->
            operandValue frame o `bindResult` \v -> case v of
                MData actual _ -> Ok (MBool (actual == plain name))
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
listOp Pop [MList []] = Error "Pop requires a non-empty list"
listOp Pop [MList l] = Ok (MList (init l))
listOp NewBoxed args = listOp NewArray args
listOp WriteByte _ = Error "writeByte is run by the statement that calls it"
listOp WriteError _ = Error "writeError is run by the statement that calls it"
listOp ToByte [MInt x]
    | x >= 0 && x < 256 = Ok (MInt x)
    | otherwise = Error "toByte needs an Int from 0 to 255"
listOp FromByte [MInt b] = Ok (MInt b)
listOp ReadByte _ = Error "readByte is run by the statement that calls it"
listOp NewEmptyBoxed [] = Ok (MList [])
listOp NewArray [MInt n, x]
    | n < 0 = Error "array needs a size that is not negative"
    | otherwise = Ok (MList (replicate (fromIntegral n) x))
listOp Set [MList l, MInt i, x]
    | i < 0 || i >= fromIntegral (length l) = Error "Set index out of range"
    | otherwise = let (before, after) = splitAt (fromIntegral i) l in Ok (MList (before ++ x : drop 1 after))
listOp op _ = Error (show op ++ " is not defined for these values")

-- A struct with sizes is one struct to a program that runs: the sizes are in the name of each copy that native code makes, and
-- not in a value (`Packet<n>` and `Packet<3>` are both a Packet)
plain :: Name -> Name
plain = takeWhile (/= '<')

renderMirValue :: MirValue -> String
renderMirValue (MInt i) = show i
renderMirValue (MBool True) = "true"
renderMirValue (MBool False) = "false"
renderMirValue (MList l) = "[" ++ intercalate ", " (map renderMirValue l) ++ "]"
renderMirValue (MData name []) = name
renderMirValue (MData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderMirValue v | (f, v) <- fields] ++ " }"
renderMirValue MFn{} = "<function>"

-- The value of the AST that a value of the MIR is, and the other way: a function of the program is VFnRef, and no function
-- written in the AST is a value of the MIR
fromMirValue :: MirValue -> Value
fromMirValue (MInt i) = VInt i
fromMirValue (MBool b) = VBool b
fromMirValue (MList vs) = VList (map fromMirValue vs)
fromMirValue (MData name fields) = VData name [(f, fromMirValue v) | (f, v) <- fields]
fromMirValue (MFn name) = VFnRef name

toMirValue :: Value -> Maybe MirValue
toMirValue (VInt i) = Just (MInt i)
toMirValue (VBool b) = Just (MBool b)
toMirValue (VList vs) = MList <$> mapM toMirValue vs
toMirValue (VData name fields) = MData name <$> mapM (\(f, v) -> (,) f <$> toMirValue v) fields
toMirValue (VFnRef name) = Just (MFn name)
toMirValue VFunct{} = Nothing
