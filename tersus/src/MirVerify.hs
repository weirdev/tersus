module MirVerify (verifyProgram) where

import Data.Maybe (fromMaybe)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir
import Pretty (renderType)
import TersusTypes (Name, Rel (..), Type (..), Variable)
import Utils (Result (..))

-- Whether the program is a well formed MIR: the shape (every block a jump names is there, every local and function
-- used is declared), and the types (every operation is applied to operands of the types it takes, and gives the type
-- of the local that receives it). Lowering gives every local its type by replaying the checker, which is a second
-- copy of its rules, and native code built on a wrong type is a wrong program, so this is what every lowering goes
-- through, and what every pass over the MIR should go through again.
verifyProgram :: Program -> Result () String
verifyProgram program =
    case concatMap (problems program) (progMain program : Map.elems (progFunctions program)) of
        [] -> Ok ()
        problem : _ -> Error problem

-- What the program declares: the constructors with the type they build, and the type of each function
data Env = Env
    { envCtors :: Map Name (Name, [(Variable, Type)])
    , envFns :: Map Name Type
    }

environment :: Program -> Env
environment program =
    Env
        { envCtors = Map.fromList (concatMap ctors (Map.toList (progTypes program)))
        , envFns = Map.fromList [(fnName f, fnType f) | f <- Map.elems (progFunctions program)]
        }
  where
    ctors (name, StructDecl fields) = [(name, (name, fields))]
    ctors (name, EnumDecl variants) = [(v, (name, fields)) | (v, fields) <- variants]
    fnType f = TFn [maybe (TVar 0) localType (Map.lookup p (fnLocals f)) | p <- fnParams f] (fromMaybe (TVar 0) (fnReturns f))

problems :: Program -> Function -> [String]
problems program fn =
    map (("In " ++ fnName fn ++ ": ") ++) $
        [ "no entry block bb0" | not (block (BlockId 0)) ]
            ++ [show l ++ " has no known type" | (l, d) <- Map.toList (fnLocals fn), hasUnknown (localType d)]
            ++ ["parameter " ++ show l ++ " is not declared" | l <- fnParams fn, not (declared l)]
            ++ ["_0 is not declared" | Just _ <- [fnReturns fn], not (declared (Local 0))]
            ++ ["_0 is " ++ renderType t ++ " but the function returns " ++ renderType r | Just r <- [fnReturns fn], Just d <- [Map.lookup (Local 0) (fnLocals fn)], let t = localType d, t /= r]
            ++ concat
                [ shape b stmts term ++ concatMap (map ((show b ++ ": ") ++) . statementProblems) stmts ++ map ((show b ++ ": ") ++) (terminatorProblems term)
                | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn)
                ]
            ++ ["a loop is at " ++ show b ++ ", which is not there" | b <- Map.keys (specLoops (fnSpec fn)), not (block b)]
  where
    env = environment program
    declared l = Map.member l (fnLocals fn)
    block b = Map.member b (fnBlocks fn)
    functionNames = Map.keys (progFunctions program)

    shape b stmts term =
        [show b ++ " uses the undeclared " ++ show l | l <- concatMap statementLocals stmts ++ terminatorLocals term, not (declared l)]
            ++ [show b ++ " jumps to " ++ show t ++ ", which is not there" | t <- successors term, not (block t)]
            ++ [show b ++ " names the function " ++ n ++ ", which is not there" | n <- concatMap statementFunctions stmts ++ terminatorFunctions term, n `notElem` functionNames]

    localTy l = localType <$> Map.lookup l (fnLocals fn)

    statementProblems stmt@(Assign dest rv) =
        case localTy dest of
            Nothing -> []
            Just d -> [renderStatement stmt ++ " is ill typed: " ++ why | why <- rvalueProblems env localTy d rv]
    statementProblems Ghost{} = []

    terminatorProblems term = case term of
        SwitchBool test _ _ -> [renderTerminator term ++ " is ill typed: the test is not a Bool" | not (fits env localTy TBool test)]
        Call callee args dest _ ->
            let why = case operandType env localTy callee of
                    Just (TFn params result)
                        | length params /= length args -> ["it takes " ++ show (length params) ++ " arguments, got " ++ show (length args)]
                        | otherwise ->
                            ["argument " ++ show i ++ " is not " ++ renderType p | (i, p, a) <- zip3 [1 :: Int ..] params args, not (fits env localTy p a)]
                                ++ ["the result is " ++ renderType result ++ ", not " ++ maybe "?" renderType (localTy dest) | Just d <- [localTy dest], not (sub env d result)]
                    _ -> ["the callee is not a function"]
             in [renderTerminator term ++ " is ill typed: " ++ w | w <- why]
        _ -> []

    hasUnknown (TVar _) = True
    hasUnknown (TList t) = hasUnknown t
    hasUnknown (TFn args ret) = any hasUnknown (ret : args)
    hasUnknown _ = False

-- Why the rvalue cannot give a value of the type of the local it is assigned to
rvalueProblems :: Env -> (Local -> Maybe Type) -> Type -> Rvalue -> [String]
rvalueProblems env localTy d rv =
    case rv of
        Use o -> [expected d o | not (fits' d o)]
        BinaryOp op a b -> case op of
            Compare Eq -> comparison a b
            Compare NotEq -> comparison a b
            Compare _ -> ints [a, b] ++ result TBool
            _ -> ints [a, b] ++ result TInt
        ListOp Length [l] -> [expected' "a list" l | not (isList l)] ++ result TInt
        ListOp First [l] -> [expected (TList d) l | not (fits' (TList d) l)]
        ListOp Last [l] -> [expected (TList d) l | not (fits' (TList d) l)]
        ListOp Get [l, i] -> [expected (TList d) l | not (fits' (TList d) l)] ++ ints [i]
        ListOp Push [l, x] -> withElement (\e -> [expected d l | not (fits' d l)] ++ [expected e x | not (fits' e x)])
        ListOp Set [l, i, x] -> withElement (\e -> [expected d l | not (fits' d l)] ++ ints [i] ++ [expected e x | not (fits' e x)])
        ListOp op os -> [show op ++ " is applied to " ++ show (length os) ++ " operands"]
        MakeList os -> withElement (\e -> [expected e o | o <- os, not (fits' e o)])
        MakeData name fields -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, declared)
                | map fst declared /= map fst fields -> [name ++ " is built with the wrong fields"]
                | otherwise -> ["the result is " ++ renderType d ++ ", not " ++ typeName | d /= TNamed typeName] ++ [expected t o | ((_, t), (_, o)) <- zip declared fields, not (fits' t o)]
        ReadField o name field -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, declared) ->
                [expected' ("a " ++ name) o | not (isValueOf typeName o)]
                    ++ case lookup field declared of
                        Nothing -> [name ++ " has no field " ++ field]
                        Just t -> ["the field is " ++ renderType t ++ ", not " ++ renderType d | not (sub env d t)]
        IsVariant o name -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, _) -> [expected' ("a " ++ typeName) o | not (isValueOf typeName o)] ++ result TBool
        AsVariant o name -> case Map.lookup name (envCtors env) of
            Nothing -> ["there is no constructor " ++ name]
            Just (typeName, _) ->
                [expected' ("a " ++ typeName) o | not (isValueOf typeName o)]
                    ++ ["the result is " ++ renderType d ++ ", not " ++ name | not (sub env d (TVariant name))]
  where
    fits' = fits env localTy
    expected t o = renderOperand' o ++ " is not " ++ renderType t
    expected' what o = renderOperand' o ++ " is not " ++ what
    renderOperand' o = case o of
        Copy l -> show l ++ maybe "" (\t -> " (" ++ renderType t ++ ")") (localTy l)
        Const _ -> "the constant"
    ints os = [expected TInt o | o <- os, not (fits' TInt o)]
    result t = ["the result is " ++ renderType t ++ ", not " ++ renderType d | d /= t]
    withElement k = case d of
        TList e -> k e
        _ -> ["the result is " ++ renderType d ++ ", not a list"]
    comparison a b =
        result TBool
            ++ case (operandType env localTy a, operandType env localTy b) of
                (Just x, Just y)
                    | isFn x || isFn y -> ["functions cannot be compared"]
                    | not (sub env x y || sub env y x) -> ["the operands are " ++ renderType x ++ " and " ++ renderType y]
                _ -> []
    isFn TFn{} = True
    isFn _ = False
    isList o = case operandType env localTy o of
        Just (TList _) -> True
        Nothing -> case o of
            Const (CList _) -> True
            _ -> False
        _ -> False
    -- a value of the type with this name, or of one of its variants
    isValueOf typeName o = case operandType env localTy o of
        Just t -> sub env (TNamed typeName) t
        Nothing -> False

-- The type an operand is known to have; none for a list constant, whose element type is not in it
operandType :: Env -> (Local -> Maybe Type) -> Operand -> Maybe Type
operandType env localTy o = case o of
    Copy l -> localTy l
    Const c -> case c of
        CInt _ -> Just TInt
        CBool _ -> Just TBool
        CList _ -> Nothing
        CData name _ -> TNamed . fst <$> Map.lookup name (envCtors env)
        CFn name -> Map.lookup name (envFns env)

-- Whether the operand can be used where the type is wanted
fits :: Env -> (Local -> Maybe Type) -> Type -> Operand -> Bool
fits env localTy wanted o = case o of
    Copy l -> maybe False (sub env wanted) (localTy l)
    Const c -> constantFits env wanted c

constantFits :: Env -> Type -> Constant -> Bool
constantFits env wanted c = case c of
    CInt _ -> wanted == TInt
    CBool _ -> wanted == TBool
    CList cs -> case wanted of
        TList e -> all (constantFits env e) cs
        _ -> False
    CData name fields -> case Map.lookup name (envCtors env) of
        Nothing -> False
        Just (typeName, declared) ->
            sub env wanted (TNamed typeName)
                && map fst declared == map fst fields
                && and [constantFits env t v | ((_, t), (_, v)) <- zip declared fields]
    CFn name -> maybe False (== wanted) (Map.lookup name (envFns env))

-- Whether a value of the second type can be used where the first is wanted: the same type, or a variant of an enum
-- where the enum is wanted (but not the other way), also inside a list
sub :: Env -> Type -> Type -> Bool
sub env wanted actual = case (wanted, actual) of
    (TNamed t, TVariant v) -> maybe False ((== t) . fst) (Map.lookup v (envCtors env))
    (TList a, TList b) -> sub env a b
    _ -> wanted == actual

statementLocals :: Statement -> [Local]
statementLocals (Assign dest rv) = dest : concatMap operandLocals (rvalueOperands rv)
statementLocals Ghost{} = []

rvalueOperands :: Rvalue -> [Operand]
rvalueOperands (Use o) = [o]
rvalueOperands (BinaryOp _ a b) = [a, b]
rvalueOperands (ListOp _ os) = os
rvalueOperands (MakeList os) = os
rvalueOperands (MakeData _ fields) = map snd fields
rvalueOperands (ReadField o _ _) = [o]
rvalueOperands (IsVariant o _) = [o]
rvalueOperands (AsVariant o _) = [o]

operandLocals :: Operand -> [Local]
operandLocals (Copy l) = [l]
operandLocals (Const _) = []

terminatorLocals :: Terminator -> [Local]
terminatorLocals (SwitchBool o _ _) = operandLocals o
terminatorLocals (Call f args dest _) = dest : concatMap operandLocals (f : args)
terminatorLocals _ = []

statementFunctions :: Statement -> [Name]
statementFunctions (Assign _ rv) = concatMap operandFunctions (rvalueOperands rv)
statementFunctions Ghost{} = []

terminatorFunctions :: Terminator -> [Name]
terminatorFunctions (SwitchBool o _ _) = operandFunctions o
terminatorFunctions (Call f args _ _) = concatMap operandFunctions (f : args)
terminatorFunctions _ = []

operandFunctions :: Operand -> [Name]
operandFunctions (Const c) = constantFunctions c
operandFunctions _ = []

constantFunctions :: Constant -> [Name]
constantFunctions (CFn n) = [n]
constantFunctions (CList cs) = concatMap constantFunctions cs
constantFunctions (CData _ fs) = concatMap (constantFunctions . snd) fs
constantFunctions _ = []
