module TypeCheckCore where

import Control.Monad (forM, forM_, unless, void, when)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate, isInfixOf, (\\))
import Data.Maybe (isJust)
import qualified Data.Set as Set

import BuiltinRegistry (SigScheme (..), ghostBuiltinByName, methodBuiltinByName, methodNameFor, pointerBuiltinByName, signatureScheme)
import Pretty (renderType)
import StdLib
import Types
import Syntax
import Utils

-- An expression with the type the checker gave it, and the typed expressions inside it that the lowering
-- visits (see Elaborated): for an application whose head is a name or a value, the head is not one of them.
data TExpr = TExpr Type Expression [TExpr]

tType :: TExpr -> Type
tType (TExpr t _ _) = t

tExpr :: TExpr -> Expression
tExpr (TExpr _ e _) = e

-- The types of an expression and of the typed expressions inside it, in the order the lowering visits them
tTypes :: TExpr -> [Type]
tTypes (TExpr t _ inner) = t : concatMap tTypes inner

tLeaf :: Type -> Expression -> TExpr
tLeaf t e = TExpr t e []


-- The checking monad: a substitution for the type variables, a counter for new ones, and failure

-- Every struct is a type with one constructor named like it, and every enum a type with a constructor for
-- each variant (named Enum::Variant)
data TcState = TcState
    { tcSubst :: Map Int Type
    , tcNext :: Int
    , tcTypes :: Map Name [Name]
    , tcCtors :: Map Name (Name, [(Variable, Type)])
    , tcProgramReturn :: Maybe Type -- what the first return of the program itself (not of a function) returned
    , tcTraits :: Map Name [TraitFn]
    , tcImpls :: Set.Set (Name, Name) -- (trait, type) for each trait a type implements
    , tcAssoc :: Map (Name, Name) [Maybe Name] -- for a type and a function name, the impls that define it (Nothing is an impl of the type itself), in order
    , tcSizeSubst :: Map Int Size -- what the sizes that a call gave to size parameters have come to
    , tcSizeScope :: [Variable] -- the size parameters of the function being checked
    , tcGenerics :: Map Name ([Variable], [(Variable, Type)]) -- the structs with sizes: their sizes and fields, with the sizes in them
    , tcReadOnly :: [Variable] -- the parameters of the function being checked that it borrows
    , tcTypeScope :: [Variable] -- the type parameters of the function being checked
    , tcCurrent :: Maybe Variable -- the function being checked, which may call itself
    , tcTraitParams :: Map Name [Variable] -- the types of each trait that has any (`trait Sequence<E>`)
    , tcTraitSelf :: Maybe [TraitFn] -- the functions of the trait being checked, which a contract of it may call on a value of type Self
    , tcImplArgs :: Map (Name, Name) (Type, [Arg]) -- for a trait and a type that implements it, the impl's type (`Vec<T>`) and the types it gives the trait
    , tcTemplates :: Map Name Template -- the functions with bounds on their types, each checked for the types it is called with
    , tcInstances :: Map Name Type -- the functions that a template has been made into so far, with their types
    , tcEmitted :: [(Statement, [Type])] -- the instances made since the last statement of the program, which come before it, with the types of their expressions
    , tcActive :: [Name] -- the templates that an instance is being checked of, which a call of one of them cannot make another instance of
    , tcLinear :: Set.Set Name -- the structs and enums that are linear
    , tcDrops :: Set.Set Name -- the structs and enums that have a drop
    , tcGhost :: Bool -- whether the expression being checked is the validator's (of a `define`), where what is known of a permission can be read
    }

-- A function whose type parameters have bounds (`fn total<S: Sequence<Int>>(s: &S) -> Int`): its definition, the bounds and the functions it can
-- see. There is a function of it for each list of types that a call gives (see templateCall).
data Template = Template
    { tmplBounds :: [Bound]
    , tmplCtx :: Ctx
    , tmplParams :: [Variable]
    , tmplSignature :: Signature
    , tmplRequires :: [ValidationStatement]
    , tmplEnsures :: [ValidationStatement]
    , tmplTermination :: Maybe Termination
    , tmplBody :: [Statement]
    }

newtype TC a = TC (TcState -> Either String (a, TcState))

initialTcState :: TcState
initialTcState = TcState Map.empty 0 Map.empty Map.empty Nothing Map.empty Set.empty Map.empty Map.empty [] Map.empty [] [] Nothing Map.empty Nothing Map.empty Map.empty Map.empty [] [] Set.empty Set.empty False

runTcState :: TC a -> TcState -> Either String (a, TcState)
runTcState (TC f) = f

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

tryTc :: TC a -> TC (Maybe a)
tryTc (TC f) = TC (\s -> Right (case f s of Left _ -> (Nothing, s); Right (a, s') -> (Just a, s')))

getState :: TC TcState
getState = TC (\s -> Right (s, s))

putState :: TcState -> TC ()
putState s = TC (\_ -> Right ((), s))

freshVar :: TC Type
freshVar = do
    s <- getState
    putState s{tcNext = tcNext s + 1}
    return (TVar (tcNext s))

freshSize :: TC Size
freshSize = do
    s <- getState
    putState s{tcNext = tcNext s + 1}
    return (SizeVar (tcNext s))

zonkSize :: Size -> TC Size
zonkSize size@(SizeVar n) = do
    s <- getState
    case Map.lookup n (tcSizeSubst s) of
        Just size' -> zonkSize size'
        Nothing -> return size
zonkSize size = return size

-- Makes the two sizes equal if possible
unifySize :: Size -> Size -> TC Bool
unifySize a b = do
    a' <- zonkSize a
    b' <- zonkSize b
    case (a', b') of
        (SizeVar n, SizeVar m) | n == m -> return True
        (SizeVar n, size) -> bindSize n size >> return True
        (size, SizeVar n) -> bindSize n size >> return True
        _ -> return (a' == b')
  where
    bindSize n size = getState >>= \s -> putState s{tcSizeSubst = Map.insert n size (tcSizeSubst s)}

-- Applies what is known about the type variables
zonk :: Type -> TC Type
zonk t@(TVar n) = do
    s <- getState
    case Map.lookup n (tcSubst s) of
        Just t' -> zonk t'
        Nothing -> return t
zonk (TList t) = TList <$> zonk t
zonk (TArrayOf t size) = TArrayOf <$> zonk t <*> zonkSize size
zonk (TForall sizes types t) = TForall sizes types <$> zonk t
-- (the sizes of an instance of a struct with sizes are in its name)
zonk (TNamed base args) = TNamed base <$> mapM zonkArg args
  where
    zonkArg (ArgSize size) = ArgSize <$> zonkSize size
    zonkArg (ArgType t) = ArgType <$> zonk t
zonk (TBox t) = TBox <$> zonk t
zonk (TAddr t) = TAddr <$> zonk t
zonk (TUninit t) = TUninit <$> zonk t
zonk (TBlock t) = TBlock <$> zonk t
zonk (TRef t) = TRef <$> zonk t
zonk (TFn args ret) = TFn <$> mapM zonk args <*> zonk ret
zonk t = return t

bindVar :: Int -> Type -> TC ()
bindVar n t = do
    s <- getState
    putState s{tcSubst = Map.insert n t (tcSubst s)}

occurs :: Int -> Type -> Bool
occurs n (TVar m) = n == m
occurs n (TList t) = occurs n t
occurs n (TArrayOf t _) = occurs n t
occurs n (TForall _ _ t) = occurs n t
occurs n (TBox t) = occurs n t
occurs n (TAddr t) = occurs n t
occurs n (TUninit t) = occurs n t
occurs n (TBlock t) = occurs n t
occurs n (TNamed _ args) = or [occurs n t | ArgType t <- args]
occurs n (TRef t) = occurs n t
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
        (TByte, TByte) -> return True
        (TBool, TBool) -> return True
        (TWord s n, TWord t m) -> return (s == t && n == m)
        (TNamed bx xs, TNamed by ys)
            | bx == by, length xs == length ys -> allM (uncurry unifyArg) (zip xs ys)
            | otherwise -> return False
        (TVariant x, TVariant y) -> return (x == y)
        -- a value read as one variant is still a value of its enum
        -- (only one way: a Circle is a Shape, but a Shape is not a Circle)
        (TNamed base args, TVariant v) -> variantOf (instanceName base args) v
        (TVariant _, TNamed _ _) -> return False
        (TList x, TList y) -> unify x y
        (TArrayOf x n, TArrayOf y m) -> unifySize n m >>= \same -> if same then unify x y else return False
        (TBox x, TBox y) -> unify x y
        (TAddr x, TAddr y) -> unify x y
        (TUninit x, TUninit y) -> unify x y
        (TBlock x, TBlock y) -> unify x y
        (TRef x, TRef y) -> unify x y
        (TParam x, TParam y) -> return (x == y)
        (TFn xs x, TFn ys y)
            | length xs == length ys -> allM (uncurry unify) (zip (x : xs) (y : ys))
        _ -> return False
  where
    allM _ [] = return True
    allM f (x : xs) = do
        ok <- f x
        if ok then allM f xs else return False

-- Makes two arguments of an instance of a struct equal if possible
unifyArg :: Arg -> Arg -> TC Bool
unifyArg (ArgSize a) (ArgSize b) = unifySize a b
unifyArg (ArgType a) (ArgType b) = unify a b
unifyArg _ _ = return False

variantOf :: Name -> Name -> TC Bool
variantOf typeName variant = do
    s <- getState
    return (variant `elem` Map.findWithDefault [] typeName (tcTypes s))

-- Where a value is given to something that has a type (an argument, a field, a returned value, a variable that has one), a Box of an
-- array of a size can be given where a Box of an array of any size is wanted: the unsizing conversion, which keeps the value and
-- makes the size part of the Box. It is written into the expression, since the Box is not the same in memory afterwards.
coerce :: Type -> TExpr -> TC TExpr
coerce wanted texpr = do
    let actual = tType texpr
        expr = tExpr texpr
    w <- zonk wanted
    a <- zonk actual
    case (w, a) of
        (TBox (TArrayOf x SizeAny), TBox (TArrayOf y size)) | size /= SizeAny -> do
            same <- unify x y
            return (if same then TExpr w (F (Val (builtinFunct Unsize)) [expr]) [texpr] else texpr)
        -- an integer written out where a fixed-width integer is wanted is that integer, if it is in its range
        (TWord signed bits, TInt) | Val (VInt n) <- expr ->
            let (low, high) = wordRange signed bits
             in if n >= low && n < high
                    then return (TExpr w (F (Val (builtinFunct (ToWord signed bits))) [expr]) [texpr])
                    else failTc ("Type error: " ++ show n ++ " is not a " ++ wordName signed bits ++ ": a " ++ wordName signed bits ++ " is from " ++ show low ++ " to " ++ show (high - 1))
        -- an integer written out where a Byte is wanted is that Byte, if it is from 0 to 255 (`writeByte(104)`)
        (TByte, TInt) | Val (VInt n) <- expr ->
            if n >= 0 && n < 256
                then return (TExpr TByte (F (Val (builtinFunct ToByte)) [expr]) [texpr])
                else failTc ("Type error: " ++ show n ++ " is not a Byte: a Byte is from 0 to 255")
        -- and a list of them written out is a list of Bytes (`String { bytes: ... }` is not written so, but a field of a list of Bytes can be)
        (TList TByte, TList TInt) | Val (VList items) <- expr, Just ns <- mapM literalInt items ->
            if all (\n -> n >= 0 && n < 256) ns
                then return (TExpr (TList TByte) (F (Val (builtinFunct BytesFrom)) [expr]) [texpr])
                else failTc "Type error: a list of Bytes is written with numbers from 0 to 255"
        _ -> return texpr
  where
    literalInt (VInt n) = Just n
    literalInt _ = Nothing

-- The arguments of a call of a function of the program, given the unsizing conversions its parameters ask for
coerceArguments :: Type -> [TExpr] -> TC [TExpr]
coerceArguments ft inferred = do
    ft' <- zonk ft
    case ft' of
        TFn pts _ | length pts == length inferred -> mapM (uncurry coerce) (zip (map unref pts) inferred)
        _ -> return inferred

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

-- A struct with sizes and types is a struct for each list of them (Packet<4>, Vec<Int, 3>), which is declared the first time it is looked at
ensureInstance :: Type -> TC ()
ensureInstance (TNamed base args) = do
    s <- getState
    let name = instanceName base args
    unless (Map.member name (tcCtors s) || null args) $
        case maybe (tupleGeneric base) Just (Map.lookup base (tcGenerics s)) of
            Just (params, fields) -> do
                when (length args /= length params) $
                    failTc ("Type error: " ++ base ++ " has " ++ show (length params) ++ " parameters (" ++ intercalate ", " params ++ "), got " ++ show (length args))
                when (ArgSize SizeAny `elem` args) $
                    failTc ("Type error: " ++ name ++ " has a size that is not given: a struct with a size of ? cannot be held yet")
                -- (a tuple is made of the types of values that are there already, which were checked where they were made)
                unless (isJust (tupleGeneric base)) $ mapM_ argKnown (zip params args)
                case instanceFields params args fields of
                    Nothing -> failTc ("Type error: " ++ name ++ " gives a size where " ++ base ++ " wants a type, or a type where it wants a size (" ++ intercalate ", " [p ++ (if isTypeName p then " is a type" else " is a size") | p <- params] ++ ")")
                    Just fields' -> do
                        s' <- getState
                        putState s'{tcTypes = Map.insert name [name] (tcTypes s'), tcCtors = Map.insert name (name, fields') (tcCtors s')}
            Nothing -> return ()
  where
    -- (a size can come to be an Int, as the size of a function that is given the struct, so it has to fit in one; a type is a type of value)
    argKnown (_, ArgSize size) = case size of
        SizeParam _ -> sizeInScope size
        SizeConst c | not (inIntRange c) -> failTc ("Type error: the size " ++ show c ++ " in " ++ instanceName base args ++ " is more than an Int can hold (an Int is 64 bits)")
        _ -> return ()
    argKnown (p, ArgType ty) = do
        ty' <- zonk ty
        when (hasFunction ty') $ failTc ("Type error: the type " ++ p ++ " of " ++ instanceName base args ++ " would be " ++ renderType ty' ++ ", and a type parameter is not a function")
        checkType ty'
ensureInstance _ = return ()

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
        Nothing -> case Map.lookup name (tcGenerics s) of
            Just (params, _) -> failTc ("Type error: " ++ name ++ " has parameters <" ++ intercalate ", " params ++ ">, which a type gives, as in " ++ name ++ "<" ++ intercalate ", " params ++ ">")
            Nothing -> failTc ("Type error: unknown type " ++ name)

-- The arguments a generic struct is given, worked out by matching its declared field types against the types at hand
solveInstanceArgs :: [Variable] -> [(Variable, Type)] -> [Type] -> [Arg]
solveInstanceArgs params template actuals =
    let (sizeBindings, typeBindings) = foldl collect ([], []) (zip (map snd template) actuals)
     in [if isTypeName param then ArgType (maybe (TParam param) id (lookup param typeBindings)) else ArgSize (maybe (SizeParam param) id (lookup param sizeBindings)) | param <- params]
  where
    collect bindings (pattern, actual) = matchType bindings pattern actual
    matchType bindings (TParam param) actual = (fst bindings, (param, actual) : snd bindings)
    matchType bindings (TList a) (TList b) = matchType bindings a b
    matchType bindings (TBox a) (TBox b) = matchType bindings a b
    matchType bindings (TAddr a) (TAddr b) = matchType bindings a b
    matchType bindings (TUninit a) (TUninit b) = matchType bindings a b
    matchType bindings (TBlock a) (TBlock b) = matchType bindings a b
    matchType bindings (TRef a) b = matchType bindings a b
    matchType bindings a (TRef b) = matchType bindings a b
    matchType bindings (TArrayOf a size) (TArrayOf b actualSize) =
        let bindings' = matchType bindings a b
         in case size of SizeParam param -> ( (param, actualSize) : fst bindings', snd bindings'); _ -> bindings'
    matchType bindings (TNamed pb pa) (TNamed ab aa)
        | pb == ab = foldl (\bs (x, y) -> matchArg bs x y) bindings (zip pa aa)
    matchType bindings (TFn pa pr) (TFn aa ar) = foldl (\bs (x, y) -> matchType bs x y) bindings (zip (pr : pa) (ar : aa))
    matchType bindings _ _ = bindings
    matchArg bindings (ArgType x) (ArgType y) = matchType bindings x y
    matchArg bindings (ArgSize (SizeParam param)) (ArgSize s) = ((param, s) : fst bindings, snd bindings)
    matchArg bindings _ _ = bindings

-- The instance type a constructor with these argument types builds, by unifying its declared fields with them
instanceTypeFor :: Name -> [Type] -> TC (Maybe Type)
instanceTypeFor base argTys = do
    s <- getState
    case Map.lookup base (tcGenerics s) of
        Nothing -> return Nothing
        Just (params, template) -> do
            vars <- mapM (\param -> if isTypeName param then Right <$> freshVar else Left <$> freshSize) params
            let sizes = [(param, size) | (param, Left size) <- zip params vars]
                types = [(param, ty) | (param, Right ty) <- zip params vars]
            mapM_ (uncurry unify) (zip [substitute sizes types fieldTy | (_, fieldTy) <- template] argTys)
            args <- mapM (\v -> case v of Left size -> ArgSize <$> zonkSize size; Right ty -> ArgType <$> zonk ty) vars
            return (Just (TNamed base args))

-- The type of a constructor's value, from its owner name and its declared (already instantiated) fields
ctorResultType :: Name -> [(Variable, Type)] -> TC Type
ctorResultType typeName declared = do
    let base = baseNameOf typeName
    s <- getState
    case tupleGeneric base of
        Just _ -> return (tupleType (map snd declared))
        Nothing -> case Map.lookup base (tcGenerics s) of
            Just (params, template) -> return (TNamed base (solveInstanceArgs params template (map snd declared)))
            Nothing -> return (TNamed typeName [])

-- A struct built from values for its fields, which are given in declaration order. The type is the instance the
-- literal names, with its arguments structural from the parser, so a size or type that no field value decides
-- (`P<2> { body: #[5] }`, `B<Int> { data: Array::empty() }`) is still the one that was written.
checkConstruct :: Type -> [Variable] -> [Type] -> TC Type
checkConstruct ty0 fields argTys0 = do
    argTys <- mapM zonk argTys0
    ty <- case ty0 of
        TNamed base _
            | Just _ <- tupleGeneric base -> return (tupleType argTys)
            | "::" `isInfixOf` base -> do (owner, _) <- ctorInfo base; return (TNamed owner [])
        TNamed base [] -> maybe ty0 id <$> instanceTypeFor base argTys
        _ -> return ty0
    ensureInstance ty
    let name = case ty of TNamed b a -> instanceName b a; _ -> ""
        ctorName = case ty0 of TNamed base _ | "::" `isInfixOf` base -> base; _ -> name
    (_, declared) <- ctorInfo ctorName
    if map fst declared /= fields || length fields /= length argTys
        then failTc ("Type error: " ++ ctorName ++ " is built with the wrong fields")
        else do
            mapM_ (\((field, fieldTy), argTy) -> expect ("field " ++ field ++ " of " ++ ctorName) fieldTy argTy) (zip declared argTys)
            return ty

-- Reading a field; the base of an update must be the struct being built
readField :: Maybe Name -> Variable -> Type -> TC Type
readField owner field structTy = do
    -- (a Box is looked into for the base of an update as for a field)
    held <- zonk structTy >>= \t -> return (case t of TBox inner -> inner; _ -> t)
    case owner of
        Just name -> do h <- zonk held; unless (namedMatches h name) $ expect ("base of an update of " ++ name) (TNamed name []) held
        Nothing -> return ()
    fieldType field structTy

-- The type a value is looked through to where a struct or an enum is looked at (a field, `is`, `as`, a `match`, the base of an
-- update, `shrinks`): a Box to what it holds, which the language gives itself since what a Box holds is not a field of it, and a type
-- with a `Deref` impl to the type the impl gives (LANGUAGE.md, Deref)
derefTarget :: Type -> TC (Maybe Type)
derefTarget ty = do
    t <- zonk ty
    case t of
        TBox inner -> return (Just inner)
        _ -> do
            args <- traitArguments "Deref" t
            return (case args of Just [target] -> Just target; _ -> Nothing)

-- The type that owns the Deref impl of a type, whose `deref` a look-through calls
derefOwner :: Type -> TC Name
derefOwner ty = do
    t <- zonk ty
    case t of
        TNamed base _ -> return base
        TVariant variant -> fst <$> ctorInfo variant
        other -> failTc ("Type error: " ++ renderType other ++ " has no Deref impl")


-- Whether a builtin looks at the struct or enum a value is of (tests its variant, casts it to one, reads a field of one)
isLookThrough :: BuiltinFunct -> Bool
isLookThrough (Is _) = True
isLookThrough (Cast _) = True
isLookThrough (Project _ _) = True
isLookThrough _ = False

-- The type of reading a field from a value of the given type
fieldType :: Variable -> Type -> TC Type
fieldType field structTy = do
    t <- zonk structTy
    case t of
        -- (a Box has the fields of what it holds)
        TBox inner -> fieldType field inner
        TNamed "Self" _ -> failTc ("Type error: a trait does not know the fields of Self, so field " ++ field ++ " cannot be read from it")
        TNamed base args -> do
            let name = instanceName base args
            ensureInstance (TNamed base args)
            ctors <- typeCtors name
            case ctors of
                [ctor] -> do
                    (_, declared) <- ctorInfo ctor
                    case lookup field declared of
                        Just fieldTy -> return fieldTy
                        Nothing -> failTc ("Type error: " ++ name ++ " has no field " ++ field)
                _ -> failTc ("Type error: " ++ name ++ " has several variants, so its field " ++ field ++ " may be absent: cast the value to a variant first, as in (value as " ++ name ++ "::Variant)." ++ field ++ ", or take it apart with match")
        TVariant variant -> do
            (_, declared) <- ctorInfo variant
            case lookup field declared of
                Just fieldTy -> return fieldTy
                Nothing -> failTc ("Type error: " ++ variant ++ " has no field " ++ field)
        TVar _ -> failTc ("Type error: the type of the value whose field " ++ field ++ " is read is not known yet; annotate it")
        other -> failTc ("Type error: field " ++ field ++ " is read from a " ++ renderType other ++ ", which is not a struct")

declareType :: Name -> TC ()
declareType name = declareTypeWith name [name]

declareTypeWith :: Name -> [Name] -> TC ()
declareTypeWith name ctors = do
    s <- getState
    if Map.member name (tcTypes s) || Map.member name (tcTraits s)
        then failTc ("Type already defined: " ++ name)
        else putState s{tcTypes = Map.insert name ctors (tcTypes s)}

-- Whether a type uses the struct being declared with a type argument that is made of the parameters without being one of them
selfExpands :: Name -> Type -> Bool
selfExpands name ty = case ty of
    TList t -> selfExpands name t
    TBox t -> selfExpands name t
    TAddr t -> selfExpands name t
    TUninit t -> selfExpands name t
    TBlock t -> selfExpands name t
    TRef t -> selfExpands name t
    TArrayOf t _ -> selfExpands name t
    TFn args ret -> any (selfExpands name) (ret : args)
    TNamed base args -> (base == name && any grows args) || or [selfExpands name t | ArgType t <- args]
    _ -> False
  where
    grows (ArgType t) = case t of
        TParam _ -> False
        _ -> mentionsParameter t
    grows (ArgSize _) = False

-- A struct with sizes and types: the declaration, from which each Packet<4> and Vec<Int, 3> is made
declareGeneric :: Name -> [Variable] -> [(Variable, Type)] -> TC ()
declareGeneric name params fields = do
    s <- getState
    if Map.member name (tcTypes s) || Map.member name (tcTraits s) || Map.member name (tcGenerics s)
        then failTc ("Type already defined: " ++ name)
        else do
            when (length params /= length (nubSizes params)) $ failTc ("Type error: " ++ name ++ " names a parameter twice")
            putState s{tcGenerics = Map.insert name (params, fields) (tcGenerics s)}
            when (any (selfExpands name . snd) fields) $
                failTc ("Type error: " ++ name ++ " uses itself with a type made of its own parameters, which would make a struct for each depth (Node<List<T>> inside Node<T>): a struct that holds itself gives its own parameters as they are")
            -- (the fields are checked with the sizes and types in scope, and the struct may hold itself in a Box)
            withGenerics (filter (not . isTypeName) params) (filter isTypeName params) (mapM_ (checkType . snd) fields)
            checkFinite name [fields]
  where
    nubSizes = foldr (\x acc -> if x `elem` acc then acc else x : acc) []


registerCtors :: Name -> [(Name, [(Variable, Type)])] -> TC ()
registerCtors typeName ctors = do
    s <- getState
    putState s{tcCtors = foldr (\(ctor, fields) -> Map.insert ctor (typeName, fields)) (tcCtors s) ctors}

-- A struct or an enum that holds itself by value would have no size, so it holds the recursion in a Box (a List is a pointer
-- to its elements, and does as well)
checkFinite :: Name -> [[(Variable, Type)]] -> TC ()
checkFinite root variants = do
    s <- getState
    let ownerOf v = fst <$> Map.lookup v (tcCtors s)
        holds ty = case ty of
            TNamed base _ -> base == root
            TVariant v -> ownerOf v == Just root
            TArrayOf t _ -> holds t
            _ -> False
    when (or [holds ty | fields <- variants, (_, ty) <- fields]) $
        failTc ("Type error: " ++ root ++ " holds itself, so it would have no size: hold the recursion in a Box, as in Box<" ++ root ++ ">")

-- The type a parameter has in its function: what it is, without the & that says a call lends it
unref :: Type -> Type
unref (TRef t) = t
unref t = t

-- Every struct a type names must be declared
checkType :: Type -> TC ()
checkType ty@(TNamed base args) = ensureInstance ty >> (() <$ typeCtors (instanceName base args))
checkType (TVariant name) = () <$ ctorInfo name
checkType (TList t) = noGhostIn "a list" t >> checkType t
-- (a Box holds any type that has a size; the one place an array of no size can be is behind it)
checkType (TBox t@(TArrayOf e SizeAny)) = checkType e >> arrayOk t
checkType (TBox t) = noGhostIn "a Box" t >> checkType t
checkType (TAddr t) = addressable t
checkType (TUninit t) = noGhostIn "an Uninit" t >> checkType t
checkType (TBlock t) = addressable t
checkType (TArrayOf _ SizeAny) = failTc unsizedByValue
checkType ty@(TArrayOf t size) = noGhostIn "an array" t >> checkType t >> sizeInScope size >> arrayOk ty
checkType (TForall _ _ t) = checkType t
checkType (TParam name) = do
    s <- getState
    unless (name `elem` tcTypeScope s) $ failTc ("Type error: " ++ name ++ " is not a type here: a function declares a type parameter, as in fn f<" ++ name ++ ">(a: " ++ name ++ ")")
checkType (TFn args ret) = mapM_ (noGhostIn "a function value") (ret : map unref args) >> mapM_ checkType (ret : map unref args)
checkType (TRef _) = failTc "Type error: & is for the parameter of a function, as in fn f(a: &List<Int>), and a type is not a reference anywhere else"
checkType _ = return ()

-- A permission is a ghost value: it is erased before the program runs, so it can only be where it is erased with what holds it (a local, a
-- parameter, a field, a part of a tuple), and not in a list, a Box, an array or a function value, which are in the program that runs
noGhostIn :: String -> Type -> TC ()
noGhostIn what t = do
    t' <- zonk t
    ghostly <- holdsGhost t'
    when ghostly $ failTc ("Type error: a permission and a value of a linear type are used exactly once, so " ++ what ++ " cannot hold " ++ renderType t' ++ ", which is or holds one")

-- Whether a value of a type is or holds a permission or a value of a linear type, in a field or a part, at any depth. Such a value is linear:
-- it is used exactly once.
holdsGhost :: Type -> TC Bool
holdsGhost ty0 = fst <$> go Set.empty ty0
  where
    -- (each struct or enum is looked into once: one that holds itself does so through a Box, and holds a permission if a field does)
    go seen ty1 = do
        ty <- zonk ty1
        case ty of
            TBlock _ -> return (True, seen)
            TUninit t -> ownsHeap t >>= \owning -> if owning then return (True, seen) else go seen t
            TRef t -> go seen t
            TList t -> go seen t
            TBox t -> go seen t
            TArrayOf t _ -> go seen t
            TNamed "Self" _ -> return (False, seen)
            TNamed base args
                | Set.member (instanceName base args) seen -> return (False, seen)
                | otherwise -> do
                  linear <- tcLinear <$> getState
                  drops <- tcDrops <$> getState
                  -- (a type with a drop is used by its drop, wherever it goes out of scope: it is not linear, whatever it holds)
                  let n = instanceName base args
                  if Set.member base drops then return (False, seen) else
                   if Set.member base linear then return (True, seen) else do
                    s0 <- getState
                    when (not (null args) && Map.notMember n (tcCtors s0)) (ensureInstance (TNamed base args))
                    s <- getState
                    let fields = concat [fs | c <- Map.findWithDefault [] n (tcTypes s), Just (_, fs) <- [Map.lookup c (tcCtors s)]]
                    anyOf (Set.insert n seen) (map snd fields)
            TVariant v
                | Set.member v seen -> return (False, seen)
                | otherwise -> do
                    s <- getState
                    anyOf (Set.insert v seen) (maybe [] (map snd . snd) (Map.lookup v (tcCtors s)))
            _ -> return (False, seen)
    anyOf seen [] = return (False, seen)
    anyOf seen (t : ts) = do
        (found, seen') <- go seen t
        if found then return (True, seen') else anyOf seen' ts

-- Whether a value of a type owns something on the heap (a list or a Box, in it at any depth): an Uninit of one is linear, since nothing
-- frees what it holds but taking it out
ownsHeap :: Type -> TC Bool
ownsHeap = go Set.empty
  where
    go seen ty0 = do
        ty <- zonk ty0
        case ty of
            TList _ -> return True
            TBox _ -> return True
            TArrayOf t _ -> go seen t
            TUninit t -> go seen t
            TNamed base args | Set.member (instanceName base args) seen -> return False
            TNamed "Self" _ -> return False
            TNamed base args -> do
                let n = instanceName base args
                s0 <- getState
                when (not (null args) && Map.notMember n (tcCtors s0)) (ensureInstance (TNamed base args))
                s <- getState
                let fields = concat [fs | c <- Map.findWithDefault [] n (tcTypes s), Just (_, fs) <- [Map.lookup c (tcCtors s)]]
                or <$> mapM (go (Set.insert n seen) . snd) fields
            TVariant v -> do
                s <- getState
                or <$> mapM (go seen . snd) (maybe [] snd (Map.lookup v (tcCtors s)))
            _ -> return False

-- What an address and a permission are of: a type with a size, which is what a slot holds, and not a permission (a permission is not in memory)
addressable :: Type -> TC ()
addressable t = do
    t' <- zonk t
    case t' of
        TBlock _ -> failTc "Type error: a permission is not held in memory, so there is no Addr<Block<T>> or Block<Block<T>>"
        _ -> checkType t'

-- A size parameter is a name that the function declares, as in fn dot<n>
sizeInScope :: Size -> TC ()
sizeInScope (SizeParam name) = do
    s <- getState
    unless (name `elem` tcSizeScope s) $
        failTc ("Type error: " ++ name ++ " is not a size here: a size is a number, ?, or a name that the function declares, as in fn f<" ++ name ++ ">(a: Array<Int, " ++ name ++ ">)")
sizeInScope _ = return ()

-- Builtins

builtinType :: BuiltinFunct -> TC Type
builtinType funct =
    case signatureScheme funct of
        SigValueError message -> failTc message
        SigFn params ret -> do
            assignments <- mapM (\name -> (,) name <$> freshVar) (schemeVars (ret : params))
            return (TFn (map (instantiate assignments) params) (instantiate assignments ret))
        SigDynamic -> case funct of
            Ctor name ctorArgs fields -> do
                let ty0 = TNamed (baseNameOf name) ctorArgs
                when (not ("::" `isInfixOf` name)) $ ensureInstance ty0
                (typeName, declared) <- ctorInfo name
                if map fst declared == fields
                    then do
                        resultTy <- case ctorArgs of
                            [] -> ctorResultType typeName declared
                            _ -> return ty0
                        return (TFn (map snd declared) resultTy)
                    else failTc ("Type error: " ++ name ++ " is built with the wrong fields")
            Is variant -> do
                (typeName, _) <- ctorInfo variant
                return (TFn [TNamed typeName []] TBool)
            Cast variant -> do
                (typeName, _) <- ctorInfo variant
                return (TFn [TNamed typeName []] (TVariant variant))
            Project variant field -> projectType variant field
            Field _ field -> failTc ("Type error: field " ++ field ++ " must be read from a struct, as in value." ++ field)
            _ -> failTc ("Type error: " ++ show funct ++ " cannot be used as a value")
  where
    instantiate assignments ty = substitute [] assignments ty
    schemeVars tys = nub' (concatMap vars tys)
      where
        vars ty = case ty of
            TParam name -> [name]
            TList t -> vars t
            TArrayOf t _ -> vars t
            TBox t -> vars t
            TAddr t -> vars t
            TBlock t -> vars t
            TUninit t -> vars t
            TRef t -> vars t
            TFn args ret -> concatMap vars (ret : args)
            TNamed _ args -> concatMap argVars args
            TForall _ _ t -> vars t
            _ -> []
        argVars (ArgType t) = vars t
        argVars _ = []
    nub' = foldr (\x rest -> if x `elem` rest then rest else x : rest) []
    projectType variant field = do
        (typeName, declared) <- ctorInfo variant
        case lookup field declared of
            Just fieldTy -> return (TFn [TNamed typeName []] fieldTy)
            Nothing -> failTc ("Type error: " ++ variant ++ " has no field " ++ field)

-- size, first, last, get and set work on an array as on a list: the same contracts, so a call is typed by the kind of its first
-- argument. (A builtin used as a value, such as `h = size`, is the one for lists.)
checkBuiltinCall :: Maybe BuiltinFunct -> String -> Type -> [Type] -> TC Type
checkBuiltinCall (Just b) name ft ats@(container : _)
    | b `elem` [Size, First, Last, Get, Set, Replace] = do
        t <- zonk container
        case t of
            TArrayOf _ n -> arrayVersion (\a -> TArrayOf a n) b >>= \aft -> checkCall name aft ats
            -- (a Box of an array is looked through, and set gives the Box back)
            TBox (TArrayOf _ n) -> arrayVersion (\a -> TBox (TArrayOf a n)) b >>= \aft -> checkCall name aft ats
            _ -> checkCall name ft ats
  where
    arrayVersion sequenceOf funct = do
        a <- freshVar
        return $ case funct of
            Size -> TFn [sequenceOf a] TInt
            Get -> TFn [sequenceOf a, TInt] a
            Set -> TFn [sequenceOf a, TInt, a] (sequenceOf a)
            Replace -> TFn [sequenceOf a, TInt, a] (tupleType [sequenceOf a, a])
            _ -> TFn [sequenceOf a] a
-- (a Box is its contents wherever a struct or an enum is looked at: tested for its variant, cast to one, or read for a field)
checkBuiltinCall (Just b) name ft (first : rest)
    | isLookingAt b = do
        t <- zonk first
        case t of
            TBox inner -> checkCall name ft (inner : rest)
            _ -> checkCall name ft (first : rest)
  where
    isLookingAt (Is _) = True
    isLookingAt (Cast _) = True
    isLookingAt (Project _ _) = True
    isLookingAt _ = False
-- (toInt widens a Byte or a fixed-width integer)
checkBuiltinCall (Just FromByte) name ft [a] = do
    t <- zonk a
    case t of
        TWord _ _ -> return TInt
        _ -> checkCall name ft [a]
checkBuiltinCall _ name ft ats = checkCall name ft ats

-- Arrays: held inline, so their size is a constant of the type

-- The largest array there can be, in 8-byte slots (64 KB), since it is held in the frame of a function
maxArraySlots :: Integer
maxArraySlots = 8192

-- The 8-byte slots an array takes
arraySlots :: Type -> Integer
arraySlots (TArrayOf t (SizeConst n)) = n * arraySlots t
arraySlots _ = 1

-- What an array can hold: any value that has a size and is not a function: an Int, a Bool, a list, a struct, an enum, a Box or an array.
-- A type not known yet is accepted: the lowering looks at the finished types.
arrayElement :: Type -> Bool
arrayElement ty = case ty of
    TFn{} -> False
    TForall{} -> False
    TRef{} -> False
    TArrayOf t _ -> arrayElement t
    _ -> True

-- The values that have nothing to free, and are written out in a program: Int, Bool, or arrays of those. A literal `#[...]` is made of
-- them, since it is a constant and a list or a struct would be made again each time it is wanted.
plainElement :: Type -> Bool
plainElement TInt = True
plainElement TByte = True
plainElement TBool = True
plainElement (TArrayOf t _) = plainElement t
plainElement (TVar _) = True
plainElement _ = False

-- (the pointer that an unsized type goes behind comes with Box, which the language does not have yet)
unsizedByValue :: String
unsizedByValue = "Type error: an array with no size (Array<T> is Array<T, ?>) can only be used behind a Box, as in Box<Array<Int>>, or be given a size, as in Array<Int, 3>"

arrayOk :: Type -> TC ()
arrayOk ty@(TArray e n) = do
    e' <- zonk e
    when (n < 0) $ failTc ("Type error: the size of an array cannot be negative, got " ++ show n)
    unless (arrayElement e') $ failTc (notAnElement e')
    words' <- typeWords ty
    when (words' > maxArraySlots) $
        failTc ("Type error: " ++ renderType ty ++ " takes " ++ show words' ++ " words, more than the " ++ show maxArraySlots ++ " that an array held in a frame can have")
arrayOk (TArrayOf e _) = do
    e' <- zonk e
    unless (arrayElement e') $ failTc (notAnElement e')
arrayOk _ = return ()

-- (an array that is written out is made of Int, Bool and arrays of them; the others are made with array(n, x) and changed with set)
literalOk :: Type -> TC ()
literalOk e = do
    e' <- zonk e
    unless (plainElement e') $
        failTc ("Type error: an array literal holds Int, Bool or arrays of them, not " ++ renderType e' ++ " (make an array of other values with array(n, x) and set)")

notAnElement :: Type -> String
notAnElement ty = "Type error: an array holds values that have a size (Int, Bool, a list, a struct, an enum, a Box or an array), not " ++ renderType ty

-- The 8-byte words a value of the type takes where it is held: a struct is its fields', an enum a word and the widest variant's, an array
-- its elements', and anything else (a number, a list, a Box) one
typeWords :: Type -> TC Integer
typeWords ty = do
    t <- zonk ty
    s <- getState
    case t of
        TBox (TArrayOf _ SizeAny) -> return 2
        TArrayOf e (SizeConst n) -> (n *) <$> typeWords e
        ty@(TNamed base args) -> ensureInstance ty >> ofType (instanceName base args)
        TVariant variant -> do
            case Map.lookup variant (tcCtors s) of
                Just (owner, _) -> typeWords (TNamed owner [])
                Nothing -> return 1
        _ -> return 1
  where
    ofType name = do
        s <- getState
        case Map.lookup name (tcTypes s) of
            Just [ctor] | ctor == name, Just (_, fields) <- Map.lookup ctor (tcCtors s) -> sum <$> mapM (typeWords . snd) fields
            Just ctors -> do
                widths <- mapM (\c -> maybe (return 0) (\(_, fields) -> sum <$> mapM (typeWords . snd) fields) (Map.lookup c (tcCtors s))) ctors
                return (1 + maximum (0 : widths))
            Nothing -> return 1

-- The value of an expression made of numbers and arithmetic, which is what a size can be. Nothing if it is anything else. The
-- arithmetic is the program's: each step has to fit in an Int and a divisor cannot be 0, as when it runs, so an expression that
-- would stop the program is refused and not folded into a number that hides it.
constantInt :: Expression -> Maybe (Either String Integer)
constantInt (Val (VInt i)) = Just (Right i)
constantInt (F (Val (VFunct _ _ _ (BuiltinFunct b) _)) [x, y])
    | b `elem` [Plus, Minus, Times, Div, Mod] = do
        a <- constantInt x
        c <- constantInt y
        Just (a >>= \a' -> c >>= constantArithmetic b a')
constantInt _ = Nothing

constantProofInt :: VariableProof -> Maybe (Either String Integer)
constantProofInt (CTerm (VInt i)) = Just (Right i)
constantProofInt (FApp (CTerm (VFunct _ _ _ (BuiltinFunct b) _)) [x, y])
    | b `elem` [Plus, Minus, Times, Div, Mod] = do
        a <- constantProofInt x
        c <- constantProofInt y
        Just (a >>= \a' -> c >>= constantArithmetic b a')
constantProofInt _ = Nothing

-- One step of the arithmetic of a size
constantArithmetic :: BuiltinFunct -> Integer -> Integer -> Either String Integer
constantArithmetic b a c =
    case b of
        Div | c == 0 -> Left "Type error: division by zero in the size of an array"
        Mod | c == 0 -> Left "Type error: modulo by zero in the size of an array"
        Plus -> fits (a + c)
        Minus -> fits (a - c)
        Times -> fits (a * c)
        Div -> fits (a `div` c)
        _ -> fits (a `mod` c)
  where
    fits n
        | inIntRange n = Right n
        | otherwise = Left "Type error: integer overflow in the size of an array (an Int is 64 bits)"

-- The size an expression folds to, or why it is not one
constantSize :: Maybe (Either String Integer) -> TC Integer
constantSize folded =
    case folded of
        Nothing -> failTc noConstantSize
        Just (Left e) -> failTc e
        Just (Right n) -> return n

-- The size of an array made by array(n, x): a constant, or a size parameter of the function (which is then the argument as it is)
arraySize :: Maybe (Either String Integer) -> Expression -> TC (Size, Expression)
arraySize folded n = do
    s <- getState
    case n of
        Var v | v `elem` tcSizeScope s -> return (SizeParam v, n)
        _ -> (\c -> (SizeConst c, Val (VInt c))) <$> constantSize folded

proofSize :: Maybe (Either String Integer) -> VariableProof -> TC Size
proofSize folded n = do
    s <- getState
    case n of
        ATerm v | v `elem` tcSizeScope s -> return (SizeParam v)
        _ -> SizeConst <$> constantSize folded

noConstantSize :: String
noConstantSize = "Type error: the size of an array must be a constant (a number, arithmetic on numbers, or a size parameter of the function), since the array is held inline (for a size that the program works out, use Array::boxed(n, x), which puts the array on the heap in a Box)"

-- The builtin that the head of a call names, unless a variable of the program hides it
builtinHead :: Ctx -> Env -> Expression -> Maybe BuiltinFunct
builtinHead _ _ (Val (VFunct _ _ _ (BuiltinFunct b) _)) = Just b
builtinHead ctx env (Var var)
    | any (Map.member var) env || Map.member var (ctxFns ctx) = Nothing
    | Just (VFunct _ _ _ (BuiltinFunct b) _) <- Map.lookup var stdLibCtx = Just b
builtinHead _ _ _ = Nothing

valueType :: Value -> TC Type
valueType (VInt _) = return TInt
valueType (VBool _) = return TBool
valueType (VData name _) = do (typeName, declared) <- ctorInfo name; ctorResultType typeName declared
valueType (VList elements) = do
    element <- freshVar
    types <- mapM valueType elements
    mapM_ (expect "list element" element) types
    return (TList element)
valueType (VFunct _ _ _ (BuiltinFunct funct) _) = builtinType funct
valueType (VFunct _ _ _ (NativeFunct (Signature ptys rty sizes types) _ _) _) = return (functionType sizes types ptys rty)
valueType (VFnRef name) = failTc ("Type error: " ++ name ++ " is a function of the MIR, which a program cannot write")

-- Checks with the sizes that a function declares in scope
withSizes :: [Variable] -> TC a -> TC a
withSizes sizes = withGenerics sizes []

-- Checks with the sizes and the types that a function declares in scope
withGenerics :: [Variable] -> [Variable] -> TC a -> TC a
withGenerics sizes types action = do
    outer <- getState
    putState outer{tcSizeScope = sizes, tcTypeScope = types}
    a <- action
    after <- getState
    putState after{tcSizeScope = tcSizeScope outer, tcTypeScope = tcTypeScope outer}
    return a

-- The type of a function: one with size parameters is for any values of them
functionType :: [Variable] -> [Variable] -> [Type] -> Type -> Type
functionType [] [] ptys rty = TFn ptys rty
functionType sizes types ptys rty = TForall sizes types (TFn ptys rty)


-- A function with size and type parameters for sizes and types that are not known yet: each is a new unknown, which the arguments decide
instantiateGenerics :: [Variable] -> [Variable] -> Type -> TC (Type, [Size], [Type])
instantiateGenerics sizeNames typeNames ty = do
    sizes <- mapM (const freshSize) sizeNames
    types <- mapM (const freshVar) typeNames
    return (substitute (zip sizeNames sizes) (zip typeNames types) ty, sizes, types)

-- A type that is made of the type parameters of the function without being one of them
isExpanding :: [Variable] -> Type -> Bool
isExpanding scope ty = case ty of
    TParam _ -> False
    _ -> usesParam ty
  where
    usesParam t = case t of
        TParam p -> p `elem` scope
        TList u -> usesParam u
        TBox u -> usesParam u
        TAddr u -> usesParam u
        TUninit u -> usesParam u
        TBlock u -> usesParam u
        TRef u -> usesParam u
        TArrayOf u _ -> usesParam u
        TFn args ret -> any usesParam (ret : args)
        -- (a struct that is given a type is made of it: Wrap<T>)
        TNamed _ args -> or [usesParam u | ArgType u <- args]
        _ -> False

hasFunction :: Type -> Bool
hasFunction ty = case ty of
    TFn{} -> True
    TList t -> hasFunction t
    TBox t -> hasFunction t
    TAddr t -> hasFunction t
    TUninit t -> hasFunction t
    TBlock t -> hasFunction t
    TArrayOf t _ -> hasFunction t
    TRef t -> hasFunction t
    _ -> False

-- A call of a function with size parameters, from the types of the arguments that are written: the type of the result, and the
-- sizes the call gives, which the arguments decide and which come to be the last arguments of the call (a constant, or a size
-- parameter of the function that calls)
genericCall :: String -> [Variable] -> [Variable] -> Type -> [TExpr] -> TC (Type, [TExpr])
genericCall name names types inner inferred = do
    (instantiated, sizes, given') <- instantiateGenerics names types inner
    case instantiated of
        TFn pts rty
            | length pts - length names /= length inferred ->
                failTc ("Type error: " ++ name ++ " takes " ++ show (length pts - length names) ++ " arguments, got " ++ show (length inferred))
            | otherwise -> do
                args <- mapM (\(i, pt, arg) -> coerce (unref pt) arg >>= \arg' -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) (unref pt) (tType arg') >> return arg') (zip3 [1 ..] pts inferred)
                given <- mapM (\(n, size) -> zonkSize size >>= sizeArgument name n) (zip names sizes)
                -- (a type parameter is a type of value: not a function, which native code has no copy of the function for)
                forM_ (zip types given') $ \(n, t) -> do
                    t' <- zonk t
                    when (hasFunction t') $ failTc ("Type error: the type " ++ n ++ " of " ++ name ++ " would be " ++ renderType t' ++ ", and a type parameter is not a function")
                    ghostly <- holdsGhost t'
                    when ghostly $ failTc ("Type error: the type " ++ n ++ " of " ++ name ++ " would be " ++ renderType t' ++ ", which holds a permission, and a type parameter is not one (a function that takes any type may drop or keep a value of it, and a permission is used exactly once)")
                    -- (a function that calls itself with a type made of its own, as f(push([], a), n - 1), would need a copy for each depth)
                    current <- tcCurrent <$> getState
                    scope <- tcTypeScope <$> getState
                    when (current == Just name && isExpanding scope t') $
                        failTc ("Type error: " ++ name ++ " calls itself with the type " ++ renderType t' ++ " for " ++ n ++ ", which is made of its own type parameters: a call of itself gives each type parameter as it is, or a type that does not use them, since a copy of the function is made for each type and would be needed for each depth")
                result <- zonk rty
                return (result, args ++ map (tLeaf TInt) given)
        _ -> failTc ("Type error: " ++ name ++ " is not a function")

-- The argument that a call gives a size parameter of a function: a constant, or a size parameter of the function that calls
sizeArgument :: String -> Variable -> Size -> TC Expression
sizeArgument name n size = case size of
    SizeConst c -> return (Val (VInt c))
    SizeParam p -> return (Var p)
    _ -> failTc ("Type error: the size " ++ n ++ " of " ++ name ++ " cannot be worked out from its arguments: an argument has to be an array of that size")


-- Clone and Copy are traits with no functions, in lib/prelude.tersus, that a struct or enum says it has: `impl Clone for P { };` and
-- `impl Copy for P { };`. Int, Byte, Bool and functions have both, an array has what its elements have, and a list or a Box is Clone when its
-- elements are (never Copy). A type parameter of a function is taken to be Clone and not Copy: that is checked for the types it is given
-- when functions can say what their type parameters are.
implementsMarker :: Name -> Type -> TC Bool
implementsMarker trait = go (0 :: Int) False
  where
    -- (lenient: a type parameter has it, for the fields of a generic struct, which have it when the parameter does)
    go depth lenient ty0
        | depth > 16 = return True
        | otherwise = do
            ty <- zonk ty0
            case ty of
                TInt -> return True
                TByte -> return True
                TBool -> return True
                TWord _ _ -> return True
                TFn{} -> return True
                TVar _ -> return True
                TRef t -> go (depth + 1) lenient t
                TParam _ -> return (lenient || trait == "Clone")
                TArrayOf e _ -> go (depth + 1) lenient e
                TList e -> if trait == "Clone" then go (depth + 1) lenient e else return False
                TBox e -> if trait == "Clone" then go (depth + 1) lenient e else return False
                -- (an address is a word, copied wherever it is wanted; a permission is never copied)
                TAddr _ -> return True
                TBlock _ -> return False
                -- (an Uninit of a value that owns nothing is its bits, and is copied as they are; one of a value that owns something is linear)
                TUninit e -> ownsHeap e >>= \owning -> if owning then return False else go (depth + 1) lenient e
                TNamed "Self" _ -> return (trait == "Clone")
                -- (a tuple has what all of its parts have)
                TNamed base args | Just _ <- tupleGeneric base -> allM' [go (depth + 1) lenient t | ArgType t <- args]
                TNamed base args -> declared depth lenient (instanceName base args)
                TVariant variant -> ctorInfo variant >>= \(owner, _) -> declared depth lenient owner
                _ -> return False
    allM' [] = return True
    allM' (m : ms) = m >>= \ok -> if ok then allM' ms else return False
    declared depth lenient name = do
        s <- getState
        let base = baseNameOf name
        if not (Set.member (trait, base) (tcImpls s))
            then return False
            else
                -- (a struct with types is Copy for the types that are, and a Clone one is checked where its impl is)
                if trait == "Copy" && base /= name
                    then do
                        ctors <- typeCtors name
                        fields <- concat <$> mapM (fmap snd . ctorInfo) ctors
                        and <$> mapM (go (depth + 1) lenient . snd) fields
                    else return True

-- A copy is made of a type that has Clone
requireMarker :: Name -> Type -> TC ()
requireMarker trait ty = do
    ok <- implementsMarker trait ty
    unless ok $ do
        t <- zonk ty >>= lacking
        case t of
            TBlock _ -> failTc ("Type error: " ++ renderType t ++ " is a permission, which is never copied: there is only ever one for a piece of memory")
            TUninit _ -> failTc ("Type error: " ++ renderType t ++ " holds a value that owns something, or nothing, and native code cannot tell which: it is not copied (take the value out with Uninit::take, and copy that)")
            _ -> return ()
        failTc ("Type error: " ++ renderType t ++ " does not implement " ++ trait ++ (if trait == "Clone" then ", so a copy of it is not made: write impl Clone for " ++ describeOwner t ++ " { }; (its fields have to be Clone) if it should be" else ""))
  where
    -- (the type inside a list, a Box or an array that is the one without it)
    lacking t = case t of
        TList e -> inner t e
        TBox e -> inner t e
        TArrayOf e _ -> inner t e
        _ -> return t
    inner t e = do
        ok <- implementsMarker trait e
        if ok then return t else zonk e >>= lacking
    describeOwner t = case t of
        TNamed base _ -> base
        TVariant variant -> variant
        _ -> renderType t

-- The check of `impl Clone for T { };` and `impl Copy for T { };`: every field has what the type says it has, and a Copy type is Clone
checkMarkerImpl :: Name -> Name -> TC ()
checkMarkerImpl trait typeName = do
    s <- getState
    when (Set.member typeName (tcLinear s)) $
        failTc ("Type error: impl " ++ trait ++ " for " ++ typeName ++ ": " ++ typeName ++ " is linear, so a value of it is used exactly once and is never copied")
    when (Set.member typeName (tcDrops s)) $
        failTc ("Type error: impl " ++ trait ++ " for " ++ typeName ++ ": " ++ typeName ++ " has a drop, and a copy of a value with a drop would be dropped twice")
    when (trait == "Copy" && not (Set.member ("Clone", typeName) (tcImpls s))) $
        failTc ("Type error: impl Copy for " ++ typeName ++ ": " ++ typeName ++ " is Copy only if it is Clone, so write impl Clone for " ++ typeName ++ " { }; first")
    fields <- case Map.lookup typeName (tcGenerics s) of
        Just (_, declared) -> return [(typeName, declared)]
        Nothing -> do
            ctors <- typeCtors typeName
            mapM (\c -> (,) c . snd <$> ctorInfo c) ctors
    forM_ fields $ \(ctor, declared) -> forM_ declared $ \(field, fieldTy) -> do
        ok <- implementsMarkerLenient fieldTy
        unless ok $ do
            t <- zonk fieldTy
            failTc ("Type error: impl " ++ trait ++ " for " ++ typeName ++ ": the field " ++ field ++ " of " ++ ctor ++ " is " ++ renderType t ++ ", which is not " ++ trait)
  where
    implementsMarkerLenient fieldTy = do
        -- (a type parameter is accepted: the type has the trait for the types that do)
        let parameterFree = fieldTy
        parameterOk parameterFree
    parameterOk ty = do
        t <- zonk ty
        case t of
            TParam _ -> return True
            TList e | trait == "Clone" -> parameterOk e
            TBox e | trait == "Clone" -> parameterOk e
            TArrayOf e _ -> parameterOk e
            _ -> implementsMarker trait t

-- The types a type gives a trait that it implements: Nothing if it does not. A list implements Sequence and Growable, an array and a Box of an array
-- implement Sequence, each of the type of its elements; a struct or enum does what its impls say.
traitArguments :: Name -> Type -> TC (Maybe [Type])
traitArguments trait ty = do
    s <- getState
    if trait `elem` ["Clone", "Copy"] && Map.lookup trait (tcTraits s) == Just [] && null (Map.findWithDefault [] trait (tcTraitParams s))
        then implementsMarker trait ty >>= \ok -> return (if ok then Just [] else Nothing)
        else traitArgumentsOf trait ty

traitArgumentsOf :: Name -> Type -> TC (Maybe [Type])
traitArgumentsOf trait ty = do
    s <- getState
    let arity = length (Map.findWithDefault [] trait (tcTraitParams s))
        builtin elementType traits = Just [elementType | trait `elem` traits, arity == 1]
        own name args = case Map.lookup (trait, name) (tcImplArgs s) of
            Nothing -> Nothing
            Just (selfType, given) -> case selfType of
                TNamed _ selfArgs
                    | length selfArgs /= length args -> Nothing
                    | otherwise -> do
                        (sizesBound, typesBound) <- foldl collect (Just ([], [])) (zip selfArgs args)
                        return [substitute sizesBound typesBound t | ArgType t <- given]
                _ -> Just [t | ArgType t <- given]
          where
            collect Nothing _ = Nothing
            collect (Just (ss, ts)) (ArgSize (SizeParam p), ArgSize sz) = Just ((p, sz) : ss, ts)
            collect (Just bound) (ArgSize SizeAny, ArgSize _) = Just bound
            collect (Just bound) (ArgSize a, ArgSize b) = if a == b then Just bound else Nothing
            collect (Just (ss, ts)) (ArgType pattern, ArgType t) = fmap (\bound -> (ss, bound ++ ts)) (matchTypes pattern t)
            collect _ _ = Nothing
            -- (the types of the impl's type, as `Array<T>` in `Box<Array<T>>`, give the parameters they are made of; a part
            -- written out in the impl, a type or a size, is not matched by another, so the impl is not one for this type)
            matchTypes (TParam p) t = Just [(p, t)]
            matchTypes (TList a) (TList b) = matchTypes a b
            matchTypes (TBox a) (TBox b) = matchTypes a b
            matchTypes (TArrayOf a sa) (TArrayOf b sb)
                | sa == sb || sa == SizeAny || isParam sa = matchTypes a b
                | otherwise = Nothing
              where
                isParam (SizeParam _) = True
                isParam _ = False
            matchTypes a b = if a == b then Just [] else Nothing
    case ty of
        -- (a list, an array and a Box of an array implement what an impl for them declares, which lib/prelude.tersus does for
        -- Sequence and Growable; with no impl declared, as in a program that declares those traits itself, they have them as before)
        TList e -> case own "List" [ArgType e] of
            Just args -> return (Just args)
            Nothing -> return (builtin e ["Sequence", "Growable"] >>= nonEmpty)
        TArrayOf e size -> case own "Array" [ArgType e, ArgSize size] of
            Just args -> return (Just args)
            Nothing -> return (builtin e ["Sequence"] >>= nonEmpty)
        TBox (TArrayOf e _) -> case own "Box" [ArgType (TArrayOf e SizeAny)] of
            Just args -> return (Just args)
            Nothing -> return (builtin e ["Sequence"] >>= nonEmpty)
        TNamed base args -> return (own base args)
        TVariant variant -> (\(enum, _) -> own enum []) <$> ctorInfo variant
        _ -> return Nothing
  where
    nonEmpty xs = if null xs then Nothing else Just xs


-- The result of applying a function type to argument types
checkCall :: String -> Type -> [Type] -> TC Type
checkCall name ft ats = do
    ft' <- zonk ft
    case ft' of
        -- (the arguments here include the sizes, as a function of the MIR is given them: see genericCall)
        TForall sizes types inner -> do
            (inner', _, _) <- instantiateGenerics sizes types inner
            checkCall name inner' ats
        TFn pts rty
            | length pts /= length ats ->
                failTc ("Type error: " ++ name ++ " takes " ++ show (length pts) ++ " arguments, got " ++ show (length ats))
            | otherwise -> do
                mapM_ (\(i, pt, at) -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) (unref pt) at) (zip3 [1 ..] pts ats)
                return rty
        TVar _ -> do
            rty <- freshVar
            expect ("call of " ++ name) ft' (TFn ats rty)
            return rty
        other -> failTc ("Type error: " ++ name ++ " is not a function, it is " ++ renderType other)
