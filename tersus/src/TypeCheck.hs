module TypeCheck (typeCheck, renderType) where

import Data.List (intercalate)
import qualified Data.Map as Map
import Data.Map (Map)

import StdLib
import TersusTypes
import Utils

-- Types are checked between parsing and validation. Parameters and return types are written in the
-- program, locals take the type of their first assignment, and the builtins have the signatures below.
-- Checking is unification inside one function body, with no polymorphism for user functions.

typeCheck :: [Statement] -> Result () String
typeCheck stmts =
    case runTc (checkProgram stmts) of
        Left err -> Error err
        Right _ -> Ok ()

renderType :: Type -> String
renderType TInt = "Int"
renderType TBool = "Bool"
renderType (TList t) = "List<" ++ renderType t ++ ">"
renderType (TFn args ret) = "fn(" ++ intercalate ", " (map renderType args) ++ ") -> " ++ renderType ret
renderType (TNamed name) = name
renderType (TVar _) = "?"

-- The checking monad: a substitution for the type variables, a counter for new ones, and failure

-- Every struct is a type with one constructor named like it, and every enum a type with a constructor for
-- each variant (named Enum::Variant)
data TcState = TcState
    { tcSubst :: Map Int Type
    , tcNext :: Int
    , tcTypes :: Map Name [Name]
    , tcCtors :: Map Name (Name, [(Variable, Type)])
    }

newtype TC a = TC (TcState -> Either String (a, TcState))

runTc :: TC a -> Either String a
runTc (TC f) = fmap fst (f (TcState Map.empty 0 Map.empty Map.empty))

instance Functor TC where
    fmap f (TC g) = TC (\s -> fmap (\(a, s') -> (f a, s')) (g s))

instance Applicative TC where
    pure a = TC (\s -> Right (a, s))
    TC f <*> TC g = TC (\s -> case f s of
        Left e -> Left e
        Right (h, s') -> fmap (\(a, s'') -> (h a, s'')) (g s'))

instance Monad TC where
    TC g >>= f = TC (\s -> case g s of
        Left e -> Left e
        Right (a, s') -> let TC h = f a in h s')

failTc :: String -> TC a
failTc err = TC (\_ -> Left err)

getState :: TC TcState
getState = TC (\s -> Right (s, s))

putState :: TcState -> TC ()
putState s = TC (\_ -> Right ((), s))

freshVar :: TC Type
freshVar = do
    s <- getState
    putState s{tcNext = tcNext s + 1}
    return (TVar (tcNext s))

-- Applies what is known about the type variables
zonk :: Type -> TC Type
zonk t@(TVar n) = do
    s <- getState
    case Map.lookup n (tcSubst s) of
        Just t' -> zonk t'
        Nothing -> return t
zonk (TList t) = TList <$> zonk t
zonk (TFn args ret) = TFn <$> mapM zonk args <*> zonk ret
zonk t = return t

bindVar :: Int -> Type -> TC ()
bindVar n t = do
    s <- getState
    putState s{tcSubst = Map.insert n t (tcSubst s)}

occurs :: Int -> Type -> Bool
occurs n (TVar m) = n == m
occurs n (TList t) = occurs n t
occurs n (TFn args ret) = any (occurs n) (ret : args)
occurs _ _ = False

-- Makes the two types equal if possible
unify :: Type -> Type -> TC Bool
unify a b = do
    a' <- zonk a
    b' <- zonk b
    case (a', b') of
        (TVar n, TVar m) | n == m -> return True
        (TVar n, t) | not (occurs n t) -> bindVar n t >> return True
        (t, TVar n) | not (occurs n t) -> bindVar n t >> return True
        (TInt, TInt) -> return True
        (TBool, TBool) -> return True
        (TNamed x, TNamed y) -> return (x == y)
        (TList x, TList y) -> unify x y
        (TFn xs x, TFn ys y)
            | length xs == length ys -> allM (uncurry unify) (zip (x : xs) (y : ys))
        _ -> return False
  where
    allM _ [] = return True
    allM f (x : xs) = do
        ok <- f x
        if ok then allM f xs else return False

-- Fails with the context if the types cannot be made equal
expect :: String -> Type -> Type -> TC ()
expect context expected actual = do
    ok <- unify expected actual
    if ok
        then return ()
        else do
            e <- zonk expected
            a <- zonk actual
            failTc ("Type error: " ++ context ++ ": expected " ++ renderType e ++ ", got " ++ renderType a)

-- Environment

-- Variables by lexical scope, innermost first, and the functions every body can see
type Env = [Map Variable Type]

data Ctx = Ctx
    { ctxFns :: Map Variable Type
    , ctxReturn :: Maybe Type
    }

lookupVar :: Ctx -> Env -> Variable -> TC Type
lookupVar ctx env var =
    case [t | scope <- env, Just t <- [Map.lookup var scope]] of
        t : _ -> return t
        [] -> case Map.lookup var (ctxFns ctx) of
            Just t -> return t
            Nothing -> case Map.lookup var stdLibCtx of
                -- a builtin is instantiated afresh at each use, so push can be used at several element types
                Just builtin -> valueType builtin
                Nothing -> failTc ("Undefined variable: " ++ var)

-- A proof can name a proof variable that a called function's contract defined and exported
-- (examples/contracts.tersus), which is not in scope here as far as this check can tell, so an unknown name
-- there is an unknown type and the validator decides whether it exists.
lookupProofVar :: Ctx -> Env -> Variable -> TC Type
lookupProofVar ctx env var =
    case [t | scope <- env, Just t <- [Map.lookup var scope]] ++ maybe [] pure (Map.lookup var (ctxFns ctx)) of
        t : _ -> return t
        [] -> case Map.lookup var stdLibCtx of
            Just builtin -> valueType builtin
            Nothing -> freshVar

-- Assigning an existing variable keeps its type, and a new one is local to the innermost scope
assignVar :: Ctx -> Env -> Variable -> Type -> TC Env
assignVar _ env var t =
    case [existing | scope <- env, Just existing <- [Map.lookup var scope]] of
        existing : _ -> expect ("assignment to " ++ var) existing t >> return env
        [] -> case env of
            scope : outer -> return (Map.insert var t scope : outer)
            [] -> return [Map.singleton var t]

-- Structs

ctorInfo :: Name -> TC (Name, [(Variable, Type)])
ctorInfo name = do
    s <- getState
    case Map.lookup name (tcCtors s) of
        Just info -> return info
        Nothing -> failTc ("Type error: unknown struct or variant " ++ name)

-- The constructors of a type
typeCtors :: Name -> TC [Name]
typeCtors name = do
    s <- getState
    case Map.lookup name (tcTypes s) of
        Just ctors -> return ctors
        Nothing -> failTc ("Type error: unknown type " ++ name)

-- A struct built from values for its fields, which are given in declaration order
checkConstruct :: Name -> [Variable] -> [Type] -> TC Type
checkConstruct name fields argTys = do
    (typeName, declared) <- ctorInfo name
    if map fst declared /= fields || length fields /= length argTys
        then failTc ("Type error: " ++ name ++ " is built with the wrong fields")
        else do
            mapM_ (\((field, fieldTy), argTy) -> expect ("field " ++ field ++ " of " ++ name) fieldTy argTy) (zip declared argTys)
            return (TNamed typeName)

-- Reading a field; the base of an update must be the struct being built
readField :: Maybe Name -> Variable -> Type -> TC Type
readField owner field structTy = do
    case owner of
        Just name -> expect ("base of an update of " ++ name) (TNamed name) structTy
        Nothing -> return ()
    fieldType field structTy

-- The type of reading a field from a value of the given type
fieldType :: Variable -> Type -> TC Type
fieldType field structTy = do
    t <- zonk structTy
    case t of
        TNamed name -> do
            ctors <- typeCtors name
            case ctors of
                [ctor] -> do
                    (_, declared) <- ctorInfo ctor
                    case lookup field declared of
                        Just fieldTy -> return fieldTy
                        Nothing -> failTc ("Type error: " ++ name ++ " has no field " ++ field)
                _ -> failTc ("Type error: " ++ name ++ " has several variants, so its field " ++ field ++ " may be absent: take the value apart with match")
        TVar _ -> failTc ("Type error: the type of the value whose field " ++ field ++ " is read is not known yet; annotate it")
        other -> failTc ("Type error: field " ++ field ++ " is read from a " ++ renderType other ++ ", which is not a struct")

declareType :: Name -> TC ()
declareType name = declareTypeWith name [name]

declareTypeWith :: Name -> [Name] -> TC ()
declareTypeWith name ctors = do
    s <- getState
    if Map.member name (tcTypes s)
        then failTc ("Type already defined: " ++ name)
        else putState s{tcTypes = Map.insert name ctors (tcTypes s)}

registerCtors :: Name -> [(Name, [(Variable, Type)])] -> TC ()
registerCtors typeName ctors = do
    s <- getState
    putState s{tcCtors = foldr (\(ctor, fields) -> Map.insert ctor (typeName, fields)) (tcCtors s) ctors}

-- Every struct a type names must be declared
checkType :: Type -> TC ()
checkType (TNamed name) = () <$ typeCtors name
checkType (TList t) = checkType t
checkType (TFn args ret) = mapM_ checkType (ret : args)
checkType _ = return ()

-- Builtins

builtinType :: BuiltinFunct -> TC Type
builtinType funct =
    case funct of
        Size -> list (\a -> TFn [TList a] TInt)
        First -> list (\a -> TFn [TList a] a)
        Last -> list (\a -> TFn [TList a] a)
        Get -> list (\a -> TFn [TList a, TInt] a)
        Push -> list (\a -> TFn [TList a, a] (TList a))
        Set -> list (\a -> TFn [TList a, TInt, a] (TList a))
        Plus -> arith
        Minus -> arith
        Times -> arith
        Div -> arith
        Rel Eq -> list (\a -> TFn [a, a] TBool)
        Rel NotEq -> list (\a -> TFn [a, a] TBool)
        Rel _ -> return (TFn [TInt, TInt] TBool)
        Ctor name fields -> do
            (typeName, declared) <- ctorInfo name
            if map fst declared == fields
                then return (TFn (map snd declared) (TNamed typeName))
                else failTc ("Type error: " ++ name ++ " is built with the wrong fields")
        Is variant -> do
            (typeName, _) <- ctorInfo variant
            return (TFn [TNamed typeName] TBool)
        Project variant field -> do
            (typeName, declared) <- ctorInfo variant
            case lookup field declared of
                Just fieldTy -> return (TFn [TNamed typeName] fieldTy)
                Nothing -> failTc ("Type error: " ++ variant ++ " has no field " ++ field)
        Field _ field -> failTc ("Type error: field " ++ field ++ " must be read from a struct, as in value." ++ field)
  where
    list build = build <$> freshVar
    arith = return (TFn [TInt, TInt] TInt)

valueType :: Value -> TC Type
valueType (VInt _) = return TInt
valueType (VBool _) = return TBool
valueType (VData name _) = TNamed . fst <$> ctorInfo name
valueType (VList elements) = do
    element <- freshVar
    types <- mapM valueType elements
    mapM_ (expect "list element" element) types
    return (TList element)
valueType (VFunct _ _ _ (BuiltinFunct funct) _) = builtinType funct
valueType (VFunct _ _ _ (NativeFunct (Signature ptys rty) _) _) = return (TFn ptys rty)

-- Programs

checkProgram :: [Statement] -> TC ()
checkProgram stmts = do
    _ <- checkStatements True (Ctx Map.empty Nothing) [Map.empty] stmts
    return ()

-- Statements run in order; a top-level function is visible to the functions after it, and the
-- returned environment holds the variables the statements defined in the innermost scope.
checkStatements :: Bool -> Ctx -> Env -> [Statement] -> TC Env
checkStatements _ _ env [] = return env
checkStatements top ctx env (stmt : rest) = do
    (ctx', env') <- checkStatement top ctx env stmt
    checkStatements top ctx' env' rest

checkStatement :: Bool -> Ctx -> Env -> Statement -> TC (Ctx, Env)
checkStatement top ctx env stmt =
    case stmt of
        Assign var (Val (VFunct params ins outs (NativeFunct (Signature ptys rty) body) _)) -> do
            let fnTy = TFn ptys rty
                ctx' = if top then ctx{ctxFns = Map.insert var fnTy (ctxFns ctx)} else ctx
            env' <- assignVar ctx env var fnTy
            checkFunction ctx' var params ptys rty ins outs body
            return (ctx', env')
        Assign var expr -> do
            t <- inferExpr ctx env expr
            env' <- assignVar ctx env var t
            return (ctx, env')
        Let var expr -> do
            t <- inferExpr ctx env expr
            case env of
                scope : outer -> return (ctx, Map.insert var t scope : outer)
                [] -> return (ctx, [Map.singleton var t])
        Return expr -> do
            t <- inferExpr ctx env expr
            case ctxReturn ctx of
                Just rty -> expect "returned value" rty t
                Nothing -> return ()
            return (ctx, env)
        ValidationStatement vs -> do
            env' <- checkValidation ctx env vs
            return (ctx, env')
        StructDef name fields -> do
            declareType name
            mapM_ (checkType . snd) fields
            registerCtors name [(name, fields)]
            return (ctx, env)
        EnumDef name variants -> do
            -- the type is known before its fields are checked, so a variant may hold the enum itself
            declareTypeWith name (map fst variants)
            mapM_ (mapM_ (checkType . snd) . snd) variants
            registerCtors name variants
            return (ctx, env)
        AxiomDef{} -> return (ctx, env)
        ProofDef{} -> return (ctx, env)
        Block stmts -> do
            _ <- checkStatements False ctx (Map.empty : env) stmts
            return (ctx, env)
        If cond thenStmts elseStmts -> do
            condTy <- inferExpr ctx env cond
            expect "condition of if" TBool condTy
            _ <- checkStatements False ctx (Map.empty : env) thenStmts
            _ <- checkStatements False ctx (Map.empty : env) elseStmts
            return (ctx, env)
        While cond invariant body -> do
            condTy <- inferExpr ctx env cond
            expect "condition of while" TBool condTy
            _ <- checkValidations ctx env invariant
            _ <- checkStatements False ctx (Map.empty : env) body
            return (ctx, env)
        LoopEnd invariant -> checkValidations ctx env invariant >> return (ctx, env)
        EndBlock -> return (ctx, env)

-- The body sees its parameters, the functions defined before it (and itself), and nothing else
checkFunction :: Ctx -> Variable -> [Variable] -> [Type] -> Type -> [ValidationStatement] -> [ValidationStatement] -> [Statement] -> TC ()
checkFunction ctx name params ptys rty ins outs body = do
    mapM_ checkType (rty : ptys)
    if length params /= length ptys
        then failTc ("Type error: function " ++ name ++ " has " ++ show (length params) ++ " parameters but " ++ show (length ptys) ++ " types")
        else return ()
    let bodyCtx = ctx{ctxReturn = Just rty}
        paramEnv = [Map.fromList (zip params ptys)]
    inEnv <- checkValidations bodyCtx paramEnv ins
    _ <- checkValidations bodyCtx (Map.insert "return" rty (head inEnv) : tail inEnv) outs
    _ <- checkStatements False bodyCtx (Map.empty : paramEnv) body
    return ()

checkValidations :: Ctx -> Env -> [ValidationStatement] -> TC Env
checkValidations _ env [] = return env
checkValidations ctx env (vs : rest) = do
    env' <- checkValidation ctx env vs
    checkValidations ctx env' rest

checkValidation :: Ctx -> Env -> ValidationStatement -> TC Env
checkValidation ctx env vs =
    case vs of
        ProofAssert proof -> do
            t <- inferProof ctx env proof
            expect "affirmed proof" TBool t
            return env
        AssignProofVar var expr -> do
            t <- inferExpr ctx env expr
            assignVar ctx env var t
        Rewrite rule -> do
            case rule of
                Refl proof -> () <$ inferProof ctx env proof
                Eval var -> () <$ lookupVar ctx env var
                EvalAll -> return ()
                CheckGtZero proof -> () <$ inferProof ctx env proof
                CheckRel proof -> () <$ inferProof ctx env proof
                UserRewrite _ proofs -> mapM_ (inferProof ctx env) proofs
            return env

-- Expressions and proofs

inferExpr :: Ctx -> Env -> Expression -> TC Type
inferExpr ctx env expr =
    case expr of
        Val value -> valueType value
        Var var -> lookupVar ctx env var
        F (Val (VFunct _ _ _ (BuiltinFunct (Field owner field)) _)) [struct] ->
            inferExpr ctx env struct >>= readField owner field
        F (Val (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args ->
            mapM (inferExpr ctx env) args >>= checkConstruct name fields
        F funct args -> do
            ft <- inferExpr ctx env funct
            ats <- mapM (inferExpr ctx env) args
            result <- checkCall (describe funct) ft ats
            comparing funct ats
            return result
  where
    describe (Var name) = name
    describe _ = "call"

inferProof :: Ctx -> Env -> VariableProof -> TC Type
inferProof ctx env proof =
    case proof of
        ATerm var -> lookupProofVar ctx env var
        BVar var -> lookupVar ctx env var
        CTerm value -> valueType value
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Field owner field)) _)) [struct] ->
            inferProof ctx env struct >>= readField owner field
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args ->
            mapM (inferProof ctx env) args >>= checkConstruct name fields
        FApp funct args -> do
            ft <- inferProof ctx env funct
            ats <- mapM (inferProof ctx env) args
            result <- checkCall "call" ft ats
            comparing (proofHead funct) ats
            return result
        Forall index guards body -> do
            let env' = Map.singleton index TInt : env
            mapM_ (\g -> inferProof ctx env' g >>= expect "guard of forall" TBool) guards
            inferProof ctx env' body >>= expect "body of forall" TBool
            return TBool

-- Equality is structural, which functions do not have
comparing :: Expression -> [Type] -> TC ()
comparing (Val (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) (t : _)
    | rel `elem` [Eq, NotEq] = do
        t' <- zonk t
        case t' of
            TFn{} -> failTc "Type error: functions cannot be compared"
            _ -> return ()
comparing _ _ = return ()

proofHead :: VariableProof -> Expression
proofHead (CTerm value) = Val value
proofHead _ = Var ""

-- The result of applying a function type to argument types
checkCall :: String -> Type -> [Type] -> TC Type
checkCall name ft ats = do
    ft' <- zonk ft
    case ft' of
        TFn pts rty
            | length pts /= length ats ->
                failTc ("Type error: " ++ name ++ " takes " ++ show (length pts) ++ " arguments, got " ++ show (length ats))
            | otherwise -> do
                mapM_ (\(i, pt, at) -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) pt at) (zip3 [1 ..] pts ats)
                return rty
        TVar _ -> do
            rty <- freshVar
            expect ("call of " ++ name) ft' (TFn ats rty)
            return rty
        other -> failTc ("Type error: " ++ name ++ " is not a function, it is " ++ renderType other)
