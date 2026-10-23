module LlvmEmit
    ( emitProgram
    ) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map

import Mir
import Pretty (renderType)
import TersusTypes (Name, Rel (..), Type (..))
import Utils

-- Lowers the MIR to LLVM IR as text (a .ll file), which clang compiles together with the runtime of LlvmRuntime.
--
-- Every local is a stack slot (alloca) that the statements load and store, so the blocks need no phis and `mem2reg` builds
-- them. A function of the program is an internal function `@"fn.<name>"`; the statements of `main` are `@tersus_main`, which
-- the C-level `@main` runs and then prints what it returns.
--
-- Contracts the validator proved (a divisor that is not 0, an index in range, a list that is not empty) are not checked: the
-- operations assume them, as `unreachable` would. What the language itself defines does stop the program: an Int that
-- leaves its 64 bits, with the same message as the executor of the MIR.
--
-- Int is i64 and Bool is i1. A program that uses anything else is refused for now.

emitProgram :: Program -> Result String String
emitProgram program =
    flatResultMap (\(name, fn) -> emitFunction program (functionSymbol name) fn) (Map.toList (progFunctions program))
        `bindResult` \functions ->
            emitFunction program "@tersus_main" (progMain program) `bindResult` \mainFunction ->
                entryPoint (progMain program) `bindResult` \entry ->
                    Ok (unlines (concat (declarations : intersperseBlank (functions ++ [mainFunction, entry]))))
  where
    intersperseBlank = map (++ [""])

declarations :: [String]
declarations =
    [ "declare {i64, i1} @llvm.sadd.with.overflow.i64(i64, i64)"
    , "declare {i64, i1} @llvm.ssub.with.overflow.i64(i64, i64)"
    , "declare {i64, i1} @llvm.smul.with.overflow.i64(i64, i64)"
    , "declare void @tersus_overflow() noreturn"
    , "declare void @tersus_print_int(i64)"
    , "declare void @tersus_print_bool(i32)"
    , ""
    ]

-- The C-level main: runs the program and prints its return value, if it has one
entryPoint :: Function -> Result [String] String
entryPoint fn =
    case fnReturns fn of
        Nothing -> Ok (wrap ["call void @tersus_main()"])
        Just TInt -> Ok (wrap ["%r = call i64 @tersus_main()", "call void @tersus_print_int(i64 %r)"])
        Just TBool -> Ok (wrap ["%r = call i1 @tersus_main()", "%z = zext i1 %r to i32", "call void @tersus_print_bool(i32 %z)"])
        Just t -> Error (unsupportedType t)
  where
    wrap body = ["define i32 @main() {"] ++ map ("    " ++) (body ++ ["ret i32 0"]) ++ ["}"]

-- Generating the code of one function: a counter for the names of temporaries and labels, and the lines so far (last first)
newtype G a = G {runG :: Int -> [String] -> Result (a, Int, [String]) String}

instance Functor G where
    fmap f (G g) = G (\n ls -> mapResult (\(a, n', ls') -> (f a, n', ls')) (g n ls))

instance Applicative G where
    pure a = G (\n ls -> Ok (a, n, ls))
    G f <*> G g = G (\n ls -> f n ls `bindResult` \(h, n', ls') -> mapResult (\(a, n'', ls'') -> (h a, n'', ls'')) (g n' ls'))

instance Monad G where
    G g >>= f = G (\n ls -> g n ls `bindResult` \(a, n', ls') -> runG (f a) n' ls')

failG :: String -> G a
failG e = G (\_ _ -> Error e)

-- An instruction
emit :: String -> G ()
emit line = G (\n ls -> Ok ((), n, ("    " ++ line) : ls))

-- The start of a block
label :: String -> G ()
label name = G (\n ls -> Ok ((), n, (name ++ ":") : ls))

-- A name for a label that no other has
freshLabel :: String -> G String
freshLabel base = G (\n ls -> Ok (base ++ show n, n + 1, ls))

-- An instruction that gives a value, and the name of that value
ins :: String -> String -> G String
ins base text = G (\n ls -> let name = "%" ++ base ++ show n in Ok (name, n + 1, ("    " ++ name ++ " = " ++ text) : ls))

emitFunction :: Program -> String -> Function -> Result [String] String
emitFunction program symbol fn =
    inFunction (flatResultMap (localLlvmType fn) (fnParams fn)) `bindResult` \paramTypes ->
        inFunction (maybe (Ok "void") llvmType (fnReturns fn)) `bindResult` \returnType ->
            inFunction (flatResultMap (\(l, d) -> mapResult ((,) l) (llvmType (localType d))) (Map.toList (fnLocals fn))) `bindResult` \localTypes ->
                let params = intercalate ", " [t ++ " %p" ++ localNumber p | (p, t) <- zip (fnParams fn) paramTypes]
                    header = "define internal " ++ returnType ++ " " ++ symbol ++ "(" ++ params ++ ") {"
                    prologue =
                        ["entry:"]
                            ++ ["    " ++ slot l ++ " = alloca " ++ t | (l, t) <- localTypes]
                            ++ ["    store " ++ t ++ " %p" ++ localNumber p ++ ", ptr " ++ slot p | (p, t) <- zip (fnParams fn) paramTypes]
                            ++ ["    br label %bb" ++ blockNumber (BlockId 0)]
                 in case runG (mapM_ (emitBlock program fn) (Map.toList (fnBlocks fn))) 0 [] of
                        Error e -> Error ("In " ++ fnName fn ++ ": " ++ e)
                        Ok (_, _, body) ->
                            Ok ([header] ++ prologue ++ reverse body ++ overflowBlock ++ ["}"])
  where
    inFunction r = case r of
        Error e -> Error ("In " ++ fnName fn ++ ": " ++ e)
        Ok a -> Ok a
    overflowBlock = ["overflow:", "    call void @tersus_overflow()", "    unreachable"]

emitBlock :: Program -> Function -> (BlockId, BasicBlock) -> G ()
emitBlock program fn (b, BasicBlock stmts term) = do
    label ("bb" ++ blockNumber b)
    mapM_ (emitStatement fn) stmts
    emitTerminator program fn term

emitStatement :: Function -> Statement -> G ()
emitStatement _ (Ghost _ _) = pure ()
emitStatement fn (Assign dest rv) = do
    result <- rvalue fn rv
    store fn dest result

rvalue :: Function -> Rvalue -> G String
rvalue fn rv =
    case rv of
        Use o -> operandValue fn o
        BinaryOp op a b -> do
            ty <- operandType fn a
            x <- operandValue fn a
            y <- operandValue fn b
            binary op ty x y
        _ -> failG ("Native code does not support " ++ renderRvalue rv ++ " yet")

binary :: BinOp -> Type -> String -> String -> G String
binary Add _ x y = checked "sadd" x y
binary Sub _ x y = checked "ssub" x y
binary Mul _ x y = checked "smul" x y
binary Div _ x y = do
    -- the one quotient that does not fit, which sdiv does not define
    isMin <- ins "c" ("icmp eq i64 " ++ x ++ ", " ++ show intMin)
    isMinusOne <- ins "c" ("icmp eq i64 " ++ y ++ ", -1")
    overflows <- ins "c" ("and i1 " ++ isMin ++ ", " ++ isMinusOne)
    stopOn overflows
    -- sdiv rounds toward 0 and `/` rounds down
    q <- ins "q" ("sdiv i64 " ++ x ++ ", " ++ y)
    r <- ins "r" ("srem i64 " ++ x ++ ", " ++ y)
    adjust <- roundsTheOtherWay r y
    lower <- ins "q" ("sub i64 " ++ q ++ ", 1")
    ins "q" ("select i1 " ++ adjust ++ ", i64 " ++ lower ++ ", i64 " ++ q)
binary Mod _ x y = do
    -- x % -1 is 0, and srem does not define it for the smallest Int
    isMinusOne <- ins "c" ("icmp eq i64 " ++ y ++ ", -1")
    divisor <- ins "d" ("select i1 " ++ isMinusOne ++ ", i64 1, i64 " ++ y)
    r <- ins "r" ("srem i64 " ++ x ++ ", " ++ divisor)
    -- srem takes the sign of the dividend and `%` the sign of the divisor
    adjust <- roundsTheOtherWay r y
    shifted <- ins "r" ("add i64 " ++ r ++ ", " ++ y)
    ins "r" ("select i1 " ++ adjust ++ ", i64 " ++ shifted ++ ", i64 " ++ r)
binary (Compare rel) ty x y = do
    t <- typeG ty
    ins "c" ("icmp " ++ predicate rel ++ " " ++ t ++ " " ++ x ++ ", " ++ y)

predicate :: Rel -> String
predicate Eq = "eq"
predicate NotEq = "ne"
predicate Lt = "slt"
predicate Gt = "sgt"
predicate LtEq = "sle"
predicate GtEq = "sge"

-- Arithmetic that stops the program when the result does not fit in an Int
checked :: String -> String -> String -> G String
checked name x y = do
    result <- ins "o" ("call {i64, i1} @llvm." ++ name ++ ".with.overflow.i64(i64 " ++ x ++ ", i64 " ++ y ++ ")")
    value <- ins "r" ("extractvalue {i64, i1} " ++ result ++ ", 0")
    overflowed <- ins "f" ("extractvalue {i64, i1} " ++ result ++ ", 1")
    stopOn overflowed
    return value

-- Goes to the overflow block when the flag is set, and carries on in a new block otherwise
stopOn :: String -> G ()
stopOn flag = do
    next <- freshLabel "ok"
    emit ("br i1 " ++ flag ++ ", label %overflow, label %" ++ next)
    label next

-- Whether a remainder and the divisor have opposite signs and the remainder is not 0, which is when truncating and
-- rounding down differ
roundsTheOtherWay :: String -> String -> G String
roundsTheOtherWay r divisor = do
    nonZero <- ins "c" ("icmp ne i64 " ++ r ++ ", 0")
    signs <- ins "x" ("xor i64 " ++ r ++ ", " ++ divisor)
    differ <- ins "c" ("icmp slt i64 " ++ signs ++ ", 0")
    ins "c" ("and i1 " ++ nonZero ++ ", " ++ differ)

emitTerminator :: Program -> Function -> Terminator -> G ()
emitTerminator _ _ (Goto b) = emit ("br label %bb" ++ blockNumber b)
emitTerminator _ fn (SwitchBool o yes no) = do
    v <- operandValue fn o
    emit ("br i1 " ++ v ++ ", label %bb" ++ blockNumber yes ++ ", label %bb" ++ blockNumber no)
emitTerminator program fn (Call (Const (CFn name)) args dest next) =
    case Map.lookup name (progFunctions program) of
        Nothing -> failG ("Call of a function that does not exist: " ++ name)
        Just callee -> do
            values <- mapM (operandValue fn) args
            paramTypes <- mapM (\p -> localTypeG callee p >>= typeG) (fnParams callee)
            returnType <- maybe (failG ("Function without a result: " ++ name)) typeG (fnReturns callee)
            result <- ins "c" ("call " ++ returnType ++ " " ++ functionSymbol name ++ "(" ++ intercalate ", " (zipWith (\t v -> t ++ " " ++ v) paramTypes values) ++ ")")
            store fn dest result
            emit ("br label %bb" ++ blockNumber next)
emitTerminator _ _ (Call callee _ _ _) = failG ("Native code does not support a call of " ++ renderOperand' callee ++ " yet")
emitTerminator _ fn Return =
    case fnReturns fn of
        Nothing -> emit "ret void"
        Just ty -> do
            t <- typeG ty
            v <- ins "v" ("load " ++ t ++ ", ptr " ++ slot (Local 0))
            emit ("ret " ++ t ++ " " ++ v)
emitTerminator _ _ Unreachable = emit "unreachable"

renderOperand' :: Operand -> String
renderOperand' o = renderRvalue (Use o)

-- The text that stands for an operand: a constant, or the value loaded from the slot of the local
operandValue :: Function -> Operand -> G String
operandValue _ (Const (CInt i)) = pure (show i)
operandValue _ (Const (CBool b)) = pure (if b then "true" else "false")
operandValue _ (Const c) = failG ("Native code does not support the constant " ++ renderRvalue (Use (Const c)) ++ " yet")
operandValue fn (Copy l) = do
    t <- localTypeG fn l >>= typeG
    ins "v" ("load " ++ t ++ ", ptr " ++ slot l)

operandType :: Function -> Operand -> G Type
operandType _ (Const (CInt _)) = pure TInt
operandType _ (Const (CBool _)) = pure TBool
operandType _ (Const c) = failG ("Native code does not support the constant " ++ renderRvalue (Use (Const c)) ++ " yet")
operandType fn (Copy l) = localTypeG fn l

store :: Function -> Local -> String -> G ()
store fn dest value = do
    t <- localTypeG fn dest >>= typeG
    emit ("store " ++ t ++ " " ++ value ++ ", ptr " ++ slot dest)

localTypeG :: Function -> Local -> G Type
localTypeG fn l = maybe (failG ("Undeclared local " ++ show l)) (pure . localType) (Map.lookup l (fnLocals fn))

localLlvmType :: Function -> Local -> Result String String
localLlvmType fn l = maybe (Error ("Undeclared local " ++ show l)) (llvmType . localType) (Map.lookup l (fnLocals fn))

typeG :: Type -> G String
typeG ty = either failG pure (toEither (llvmType ty))
  where
    toEither (Ok a) = Right a
    toEither (Error e) = Left e

llvmType :: Type -> Result String String
llvmType TInt = Ok "i64"
llvmType TBool = Ok "i1"
llvmType ty = Error (unsupportedType ty)

unsupportedType :: Type -> String
unsupportedType ty = "Native code does not support " ++ renderType ty ++ " yet"

-- The stack slot of a local
slot :: Local -> String
slot l = "%l" ++ localNumber l

localNumber :: Local -> String
localNumber (Local n) = show n

blockNumber :: BlockId -> String
blockNumber (BlockId n) = show n

-- The symbol of a function of the program. Quoted, since a lifted function is named outer::inner.
functionSymbol :: Name -> String
functionSymbol name = "@\"fn." ++ concatMap escape name ++ "\""
  where
    escape '"' = "\\22"
    escape '\\' = "\\5C"
    escape c = [c]
