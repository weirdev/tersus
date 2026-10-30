module TypeCheck
    ( typeCheck
    , elaborate
    , renderType
      -- What MirLower needs to give every local of the MIR its type: the checker's monad and the steps of inferExpr
    , TC
    , TcState
    , initialTcState
    , runTcState
    , valueType
    , builtinType
    , checkCall
    , functionType
    , arraySlots
    , maxArraySlots
    , withSizes
    , withGenerics
    , plainElement
    , arrayElement
    , checkBuiltinCall
    , checkConstruct
    , readField
    , typeCtors
    , ctorInfo
    , declareType
    , declareTypeWith
    , declareGeneric
    , registerCtors
    , checkType
    , unify
    , expect
    , zonk
    , freshVar
    ) where

import Control.Monad (forM, forM_, unless, void, when)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate, (\\))
import Data.Maybe (isJust)
import qualified Data.Set as Set

import Pretty (renderType)
import StdLib
import TersusTypes
import Utils

-- Types are checked between parsing and validation. Parameters and return types are written in the
-- program, locals take the type of their first assignment, and the builtins have the signatures below.
-- Checking is unification inside one function body, with no polymorphism for user functions.

typeCheck :: [Statement] -> Result () String
typeCheck stmts = mapResult (const ()) (elaborate stmts)

-- Checks the program and gives it back with each `shrinks e` resolved by the type of e: an Int counts down to 0 (Counting),
-- an enum or struct loses a field at a time (Parts). The validator only sees the resolved clauses.
elaborate :: [Statement] -> Result [Statement] String
elaborate stmts =
    case runTc (checkProgram stmts) of
        Left err -> Error err
        Right stmts' -> Ok stmts'


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
    , tcImplArgs :: Map (Name, Name) (Name, [Arg]) -- for a trait and a type that implements it, the name of the impl's type (`Vec<'T>`) and the types it gives the trait
    , tcTemplates :: Map Name Template -- the functions with bounds on their types, each checked for the types it is called with
    , tcInstances :: Map Name Type -- the functions that a template has been made into so far, with their types
    , tcEmitted :: [Statement] -- the instances made since the last statement of the program, which come before it
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

runTc :: TC a -> Either String a
runTc tc = fmap fst (runTcState tc initialTcState)

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
zonk (TNamed name) | Just (base, args) <- instanceOf name = (\args' -> TNamed (instanceName base args')) <$> mapM zonkArg args
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
occurs n (TNamed name) | Just (_, args) <- instanceOf name = or [occurs n t | ArgType t <- args]
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
        (TNamed x, TNamed y)
            | x == y -> return True
            -- two instances of one struct with sizes are the same type if their sizes are
            | Just (b, xs) <- instanceOf x, Just (c, ys) <- instanceOf y, b == c, length xs == length ys -> allM (uncurry unifyArg) (zip xs ys)
            | otherwise -> return False
        (TVariant x, TVariant y) -> return (x == y)
        -- a value read as one variant is still a value of its enum
        -- (only one way: a Circle is a Shape, but a Shape is not a Circle)
        (TNamed t, TVariant v) -> variantOf t v
        (TVariant _, TNamed _) -> return False
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
coerce :: Type -> (Type, Expression) -> TC (Type, Expression)
coerce wanted (actual, expr) = do
    w <- zonk wanted
    a <- zonk actual
    case (w, a) of
        (TBox (TArrayOf x SizeAny), TBox (TArrayOf y size)) | size /= SizeAny -> do
            same <- unify x y
            return (if same then (w, F (Val (builtinFunct Unsize)) [expr]) else (actual, expr))
        -- an integer written out where a fixed-width integer is wanted is that integer, if it is in its range
        (TWord signed bits, TInt) | Val (VInt n) <- expr ->
            let (low, high) = wordRange signed bits
             in if n >= low && n < high
                    then return (w, F (Val (builtinFunct (ToWord signed bits))) [expr])
                    else failTc ("Type error: " ++ show n ++ " is not a " ++ wordName signed bits ++ ": a " ++ wordName signed bits ++ " is from " ++ show low ++ " to " ++ show (high - 1))
        -- an integer written out where a Byte is wanted is that Byte, if it is from 0 to 255 (`writeByte(104)`)
        (TByte, TInt) | Val (VInt n) <- expr ->
            if n >= 0 && n < 256
                then return (TByte, F (Val (builtinFunct ToByte)) [expr])
                else failTc ("Type error: " ++ show n ++ " is not a Byte: a Byte is from 0 to 255")
        -- and a list of them written out is a list of Bytes (`String { bytes: ... }` is not written so, but a field of a list of Bytes can be)
        (TList TByte, TList TInt) | Val (VList items) <- expr, Just ns <- mapM literalInt items ->
            if all (\n -> n >= 0 && n < 256) ns
                then return (TList TByte, F (Val (builtinFunct BytesFrom)) [expr])
                else failTc "Type error: a list of Bytes is written with numbers from 0 to 255"
        _ -> return (actual, expr)
  where
    literalInt (VInt n) = Just n
    literalInt _ = Nothing

-- The arguments of a call of a function of the program, given the unsizing conversions its parameters ask for
coerceArguments :: Type -> [(Type, Expression)] -> TC [(Type, Expression)]
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
ensureInstance :: Name -> TC ()
ensureInstance name = do
    s <- getState
    unless (Map.member name (tcCtors s)) $
        case instanceOf name of
            Just (base, args) | Just (params, fields) <- maybe (tupleGeneric base) Just (Map.lookup base (tcGenerics s)) -> do
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
            _ -> return ()
  where
    -- (a size can come to be an Int, as the size of a function that is given the struct, so it has to fit in one; a type is a type of value)
    argKnown (_, ArgSize size) = case size of
        SizeParam _ -> sizeInScope size
        SizeConst c | not (inIntRange c) -> failTc ("Type error: the size " ++ show c ++ " in " ++ name ++ " is more than an Int can hold (an Int is 64 bits)")
        _ -> return ()
    argKnown (p, ArgType ty) = do
        ty' <- zonk ty
        when (hasFunction ty') $ failTc ("Type error: the type " ++ p ++ " of " ++ name ++ " would be " ++ renderType ty' ++ ", and a type parameter is not a function")
        checkType ty'

ctorInfo :: Name -> TC (Name, [(Variable, Type)])
ctorInfo name = do
    ensureInstance name
    s <- getState
    case Map.lookup name (tcCtors s) of
        Just info -> return info
        Nothing -> failTc ("Type error: unknown struct or variant " ++ name)

-- The constructors of a type
typeCtors :: Name -> TC [Name]
typeCtors name = do
    ensureInstance name
    s <- getState
    case Map.lookup name (tcTypes s) of
        Just ctors -> return ctors
        Nothing -> case Map.lookup name (tcGenerics s) of
            Just (params, _) -> failTc ("Type error: " ++ name ++ " has parameters <" ++ intercalate ", " params ++ ">, which a type gives, as in " ++ name ++ "<" ++ intercalate ", " params ++ ">")
            Nothing -> failTc ("Type error: unknown type " ++ name)

-- A struct built from values for its fields, which are given in declaration order
checkConstruct :: Name -> [Variable] -> [Type] -> TC Type
-- (a tuple is the instance of its struct for the types of its parts)
checkConstruct name fields argTys | Just _ <- tupleGeneric name = do
    let ty = tupleType argTys
    case ty of
        TNamed instanceName' -> checkConstruct instanceName' fields argTys
        _ -> return ty
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
    -- (a Box is looked into for the base of an update as for a field)
    held <- zonk structTy >>= \t -> return (case t of TBox inner -> inner; _ -> t)
    case owner of
        Just name -> expect ("base of an update of " ++ name) (TNamed name) held
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
        TNamed name -> return (maybe name fst (instanceOf name))
        TVariant variant -> fst <$> ctorInfo variant
        other -> failTc ("Type error: " ++ renderType other ++ " has no Deref impl")

-- An expression looked through to the value it holds, by a call of its type's `deref` where it has a Deref impl, and as it is for a
-- Box (whose look-through the language gives) and for anything else. The result is the value that is looked at, so what is read from
-- it, tested or taken apart is a view of a value the call gives, and the value it came from is only lent to the call.
derefExpr :: Ctx -> Env -> (Type, Expression) -> TC (Type, Expression)
derefExpr ctx env (ty, expr) = do
    t <- zonk ty
    case t of
        TBox _ -> return (t, expr)
        _ -> do
            target <- derefTarget t
            case target of
                Just _ -> do
                    owner <- derefOwner t
                    (resultTy, call') <- inferExprR ctx env (F (Var (implFunctionName owner (Just "Deref") "deref")) [expr])
                    derefExpr ctx env (resultTy, call')
                Nothing -> return (t, expr)

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
        TNamed "Self" -> failTc ("Type error: a trait does not know the fields of Self, so field " ++ field ++ " cannot be read from it")
        TNamed name -> do
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
    TNamed n | Just (base, args) <- instanceOf n -> (base == name && any grows args) || or [selfExpands name t | ArgType t <- args]
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

-- The invariant of a struct is written with the names of its fields, and a function of the program defined before the struct may be called
checkInvariant :: Ctx -> [(Variable, Type)] -> [ValidationStatement] -> TC [ValidationStatement]
checkInvariant _ _ [] = return []
checkInvariant ctx fields invariant = do
    (_, checked) <- checkValidations ctx [Map.fromList fields] invariant
    return checked

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
            TNamed n -> n == root || fmap fst (instanceOf n) == Just root
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
checkType (TNamed name) = () <$ typeCtors name
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
            TNamed "Self" -> return (False, seen)
            TNamed n
                | Set.member n seen -> return (False, seen)
                | otherwise -> do
                  linear <- tcLinear <$> getState
                  drops <- tcDrops <$> getState
                  -- (a type with a drop is used by its drop, wherever it goes out of scope: it is not linear, whatever it holds)
                  if Set.member (maybe n fst (instanceOf n)) drops then return (False, seen) else
                   if Set.member (maybe n fst (instanceOf n)) linear then return (True, seen) else do
                    s0 <- getState
                    when (isJust (instanceOf n) && Map.notMember n (tcCtors s0)) (ensureInstance n)
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
            TNamed n | Set.member n seen -> return False
            TNamed "Self" -> return False
            TNamed n -> do
                s0 <- getState
                when (isJust (instanceOf n) && Map.notMember n (tcCtors s0)) (ensureInstance n)
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
    case funct of
        Size -> list (\a -> TFn [TList a] TInt)
        First -> list (\a -> TFn [TList a] a)
        Last -> list (\a -> TFn [TList a] a)
        Get -> list (\a -> TFn [TList a, TInt] a)
        Push -> list (\a -> TFn [TList a, a] (TList a))
        Pop -> list (\a -> TFn [TList a] (TList a))
        Set -> list (\a -> TFn [TList a, TInt, a] (TList a))
        UnBox -> failTc "Type error: Box::unbox is called, as in Box::unbox(b), and cannot be used as a value"
        NewBox -> failTc "Type error: Box::new is called, as in Box::new(x), and cannot be used as a value"
        CloneOf -> failTc "Type error: clone is called, as in clone(x) or x.clone(), and cannot be used as a value"
        NewArray -> failTc "Type error: array needs a size that is a constant, so it is written array(3, x) and cannot be used as a value"
        ArrayFrom -> failTc "Type error: an array literal #[...] cannot be used as a value"
        NewBoxedArray -> failTc "Type error: Array::boxed is called, as in Array::boxed(n, x), and cannot be used as a value"
        NewEmptyArray -> failTc "Type error: Array::empty is called, as in Array::empty(), and cannot be used as a value"
        WriteByte -> return (TFn [TByte] TByte)
        WriteError -> return (TFn [TByte] TByte)
        ReadByte -> return (TFn [] TInt)
        ArgCount -> return (TFn [] TInt)
        ArgByte -> return (TFn [TInt, TInt] TInt)
        PathByte -> return (TFn [TByte] TInt)
        FileLoad -> return (TFn [] TInt)
        FileByte -> return (TFn [TInt] TInt)
        StoreByte -> return (TFn [TByte] TInt)
        FileStore -> return (TFn [] TInt)
        ToByte -> return (TFn [TInt] TByte)
        FromByte -> return (TFn [TByte] TInt)
        ToWord signed bits -> return (TFn [TInt] (TWord signed bits))
        BytesFrom -> return (TFn [TList TInt] (TList TByte))
        Unsize -> failTc "Type error: a Box of an array is given the size of its type by the checker, and unsize cannot be used as a value"
        Plus -> arith
        Minus -> arith
        Times -> arith
        Div -> arith
        Mod -> arith
        And -> return (TFn [TBool, TBool] TBool)
        Or -> return (TFn [TBool, TBool] TBool)
        Not -> return (TFn [TBool] TBool)
        Rel Eq -> list (\a -> TFn [a, a] TBool)
        Rel NotEq -> list (\a -> TFn [a, a] TBool)
        Rel _ -> return (TFn [TInt, TInt] TBool)
        Within -> list (\a -> TFn [a, a] TBool)
        Ctor name fields -> do
            (typeName, declared) <- ctorInfo name
            if map fst declared == fields
                then return (TFn (map snd declared) (TNamed typeName))
                else failTc ("Type error: " ++ name ++ " is built with the wrong fields")
        Is variant -> do
            (typeName, _) <- ctorInfo variant
            return (TFn [TNamed typeName] TBool)
        Cast variant -> do
            (typeName, _) <- ctorInfo variant
            return (TFn [TNamed typeName] (TVariant variant))
        Project variant field -> projectType variant field
        Field _ field -> failTc ("Type error: field " ++ field ++ " must be read from a struct, as in value." ++ field)
        -- addresses and permissions (POINTERS.md)
        AddrNull -> list (\a -> TFn [] (TAddr a))
        AddrOffset -> list (\a -> TFn [TAddr a, TInt] (TAddr a))
        AddrCast -> do
            a <- freshVar
            b <- freshVar
            return (TFn [TAddr a] (TAddr b))
        AddrToInt -> list (\a -> TFn [TAddr a] TInt)
        AddrFromInt -> list (\a -> TFn [TInt] (TAddr a))
        AllocPair -> list (\a -> TFn [TInt] (tupleType [TAddr a, TBlock a]))
        AddrAlloc -> list (\a -> TFn [TInt] (TAddr a))
        BlockNew -> list (\a -> TFn [TAddr a, TInt] (TBlock a))
        AddrGet -> list (\a -> TFn [TAddr a, TInt, TBlock a] a)
        AddrWrite -> list (\a -> TFn [TAddr a, TInt, a, TBlock a] (TBlock a))
        TakePair -> list (\a -> TFn [TAddr a, TInt, TBlock a] (tupleType [a, TBlock a]))
        AddrTake -> list (\a -> TFn [TAddr a, TInt, TBlock a] a)
        BlockTaken -> list (\a -> TFn [TBlock a, TInt] (TBlock a))
        AddrDropValue -> list (\a -> TFn [TAddr a, TInt, TBlock a] (TBlock a))
        AddrDropRange -> list (\a -> TFn [TAddr a, TInt, TInt, TBlock a] (TBlock a))
        ResizePair -> list (\a -> TFn [TAddr a, TInt, TBlock a] (tupleType [TAddr a, TBlock a]))
        AddrResize -> list (\a -> TFn [TAddr a, TInt, TBlock a] (TAddr a))
        BlockResized -> list (\a -> TFn [TBlock a, TAddr a, TInt] (TBlock a))
        AddrFree -> list (\a -> TFn [TAddr a, TBlock a] TInt)
        SplitPair -> list (\a -> TFn [TBlock a, TInt] (tupleType [TBlock a, TBlock a]))
        BlockSplitLo -> list (\a -> TFn [TBlock a, TInt] (TBlock a))
        BlockSplitHi -> list (\a -> TFn [TBlock a, TInt] (TBlock a))
        BlockJoin -> list (\a -> TFn [TBlock a, TBlock a] (TBlock a))
        BlockAssume -> list (\a -> TFn [TAddr a, TInt] (TBlock a))
        BlockCast -> do
            a <- freshVar
            b <- freshVar
            return (TFn [TBlock a] (TBlock b))
        BlockBase -> list (\a -> TFn [TBlock a] (TAddr a))
        BlockCap -> list (\a -> TFn [TBlock a] TInt)
        BlockFilled -> list (\a -> TFn [TBlock a] (TList TBool))
        BlockContents -> list (\a -> TFn [TBlock a] (TList a))
        BlockOrigin -> list (\a -> TFn [TBlock a] TInt)
        BlockStart -> list (\a -> TFn [TBlock a] TInt)
        BlockExtent -> return (TFn [TInt] TInt)
        BlockCount -> list (\a -> TFn [TBlock a] TInt)
        UninitEmpty -> list (\a -> TFn [] (TUninit a))
        UninitNew -> list (\a -> TFn [a] (TUninit a))
        UninitGet -> list (\a -> TFn [TUninit a] a)
        UninitTake -> list (\a -> TFn [TUninit a] a)
        UninitDiscard -> list (\a -> TFn [TUninit a] TInt)
        UninitFilled -> list (\a -> TFn [TUninit a] TBool)
        UninitAt -> list (\a -> TFn [TUninit a] a)
        Replace -> list (\a -> TFn [TList a, TInt, a] (tupleType [TList a, a]))
  where
    list build = build <$> freshVar
    arith = return (TFn [TInt, TInt] TInt)
    projectType variant field = do
        (typeName, declared) <- ctorInfo variant
        case lookup field declared of
            Just fieldTy -> return (TFn [TNamed typeName] fieldTy)
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
        TNamed name -> ensureInstance name >> ofType name
        TVariant variant -> do
            ensureInstance variant
            case Map.lookup variant (tcCtors s) of
                Just (owner, _) -> typeWords (TNamed owner)
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
valueType (VData name _) = TNamed . fst <$> ctorInfo name
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

-- Programs

checkProgram :: [Statement] -> TC [Statement]
checkProgram stmts = snd <$> checkStatements True (Ctx Map.empty Nothing) [Map.empty] stmts

-- Statements run in order; a top-level function is visible to the functions after it, and the
-- returned environment holds the variables the statements defined in the innermost scope.
checkStatements :: Bool -> Ctx -> Env -> [Statement] -> TC (Env, [Statement])
checkStatements _ _ env [] = return (env, [])
checkStatements top ctx env (stmt : rest) = do
    (ctx', env', stmts') <- checkItem top ctx env stmt
    -- (the functions that templates were made into while it was checked come before it)
    made <- if top then takeEmitted else return []
    (envAfter, rest') <- checkStatements top ctx' env' rest
    return (envAfter, made ++ stmts' ++ rest')

takeEmitted :: TC [Statement]
takeEmitted = do
    s <- getState
    putState s{tcEmitted = []}
    return (tcEmitted s)

-- A trait is taken apart here and an impl becomes the functions it defines (and the checks of the trait's contracts, see
-- implementation), so each statement gives back the statements that stand for it
checkItem :: Bool -> Ctx -> Env -> Statement -> TC (Ctx, Env, [Statement])
checkItem top ctx env stmt =
    case stmt of
        TraitDef name params functions
            | top -> checkTrait name params functions >> return (ctx, env, [])
            | otherwise -> failTc "Type error: a trait can only be defined at the top of the program"
        ImplDef trait traitArgs typeName selfName functions
            | top -> do
                (ctx', env', functions') <- checkImpl ctx env trait traitArgs typeName selfName functions
                return (ctx', env', functions')
            | otherwise -> failTc "Type error: an impl can only be written at the top of the program"
        BoundedDef bounds (Assign name (Val (VFunct params ins outs (NativeFunct signature term body) _)))
            | top -> do
                declareTemplate ctx name bounds params signature ins outs term body
                return (ctx, env, [])
            | otherwise -> failTc "Type error: a function with bounds on its types can only be defined at the top of the program"
        BoundedDef{} -> failTc "Type error: only a function can have bounds on its types"
        _ -> do
            (ctx', env', stmt') <- checkStatement top ctx env stmt
            return (ctx', env', [stmt'])

-- Also gives the statement back with its termination clauses resolved
checkStatement :: Bool -> Ctx -> Env -> Statement -> TC (Ctx, Env, Statement)
checkStatement top ctx env stmt =
    case stmt of
        Assign var (Val (VFunct params ins outs (NativeFunct (Signature ptys rty sizes types) term body) proofs)) -> do
            templates <- tcTemplates <$> getState
            when (Map.member var templates) $ failTc ("Type error: " ++ var ++ " is already defined")
            let fnTy = functionType sizes types ptys rty
                ctx' = if top then ctx{ctxFns = Map.insert var fnTy (ctxFns ctx)} else ctx
            env' <- assignVar ctx env var fnTy
            (term', ins', outs', body') <- checkFunction ctx' var params ptys rty sizes types ins outs term body
            return (ctx', env', Assign var (Val (VFunct params ins' outs' (NativeFunct (Signature ptys rty sizes types) term' body') proofs)))
        Assign var expr -> do
            notSize var
            inferred <- inferExprR ctx env expr
            -- (a variable that has a type already is given a value of it)
            (t, expr') <- case [existing | scope <- env, Just existing <- [Map.lookup var scope]] of
                existing : _ -> coerce existing inferred
                [] -> return inferred
            env' <- assignVar ctx env var t
            return (ctx, env', Assign var expr')
        Let var expr -> do
            notSize var
            (t, expr') <- inferExprR ctx env expr
            case env of
                scope : outer -> return (ctx, Map.insert var t scope : outer, Let var expr')
                [] -> return (ctx, [Map.singleton var t], Let var expr')
        Return expr -> do
            inferred <- inferExprR ctx env expr
            (t, expr') <- maybe (return inferred) (\rty -> coerce rty inferred) (ctxReturn ctx)
            case ctxReturn ctx of
                Just rty -> expect "returned value" rty t
                -- the program has no declared type: every return in it has the type of the first
                Nothing -> do
                    s <- getState
                    case tcProgramReturn s of
                        Nothing -> putState s{tcProgramReturn = Just t}
                        Just first -> expect "returned value of the program" first t
            return (ctx, env, Return expr')
        ValidationStatement vs -> do
            (env', vs') <- checkValidation ctx env vs
            return (ctx, env', ValidationStatement vs')
        StructDef name params fields invariant
            | not (null params) -> do
                declareGeneric name params fields
                invariant' <- withGenerics (filter (not . isTypeName) params) (filter isTypeName params) (checkInvariant ctx fields invariant)
                return (ctx, env, StructDef name params fields invariant')
        StructDef name _ fields invariant -> do
            declareType name
            mapM_ (checkType . snd) fields
            registerCtors name [(name, fields)]
            checkFinite name [fields]
            invariant' <- checkInvariant ctx fields invariant
            return (ctx, env, StructDef name [] fields invariant')
        EnumDef name variants -> do
            -- the type is known before its fields are checked, so a variant may hold the enum itself
            declareTypeWith name (map fst variants)
            mapM_ (mapM_ (checkType . snd) . snd) variants
            registerCtors name variants
            checkFinite name (map snd variants)
            return (ctx, env, stmt)
        AxiomDef{} -> return (ctx, env, stmt)
        ProofDef{} -> return (ctx, env, stmt)
        Mark{} -> return (ctx, env, stmt)
        Dissolve var -> lookupVar ctx env var >> return (ctx, env, stmt)
        CopyDef{} -> return (ctx, env, stmt)
        DropDef{} -> return (ctx, env, stmt)
        ExternDef _ -> return (ctx, env, stmt)
        LinearDef name -> do
            getState >>= \s -> putState s{tcLinear = Set.insert name (tcLinear s)}
            return (ctx, env, stmt)
        TraitDef{} -> failTc "Type error: a trait can only be defined at the top of the program"
        ImplDef{} -> failTc "Type error: an impl can only be written at the top of the program"
        BoundedDef{} -> failTc "Type error: a function with bounds on its types cannot be written in an impl or a block"
        Block stmts -> do
            (_, stmts') <- checkStatements False ctx (Map.empty : env) stmts
            return (ctx, env, Block stmts')
        If cond thenStmts elseStmts -> do
            (condTy, cond') <- inferExprR ctx env cond
            expect "condition of if" TBool condTy
            (_, thenStmts') <- checkStatements False ctx (Map.empty : env) thenStmts
            (_, elseStmts') <- checkStatements False ctx (Map.empty : env) elseStmts
            return (ctx, env, If cond' thenStmts' elseStmts')
        While cond invariant term body -> do
            (condTy, cond') <- inferExprR ctx env cond
            expect "condition of while" TBool condTy
            (_, invariant') <- checkValidations ctx env invariant
            term' <- resolveTermination ctx env term
            (_, body') <- checkStatements False ctx (Map.empty : env) body
            return (ctx, env, While cond' invariant' term' body')

-- The body sees its parameters, the functions defined before it (and itself), and nothing else
checkFunction :: Ctx -> Variable -> [Variable] -> [Type] -> Type -> [Variable] -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> Maybe Termination -> [Statement] -> TC (Maybe Termination, [ValidationStatement], [ValidationStatement], [Statement])
checkFunction ctx name params ptys rty sizes types ins outs term body = do
    outer <- getState
    -- the sizes and types the function declares are the names its types may use, and the sizes are the last parameters (Ints)
    putState outer{tcSizeScope = sizes, tcTypeScope = types, tcCurrent = Just name}
    when (length sizes /= length (nub' sizes) || any (`elem` take (length params - length sizes) params) sizes) $
        failTc ("Type error: function " ++ name ++ " names a size twice, or the same as a parameter")
    mapM_ checkType (rty : map unref ptys)
    if length params /= length ptys
        then failTc ("Type error: function " ++ name ++ " has " ++ show (length params) ++ " parameters but " ++ show (length ptys) ++ " types")
        else return ()
    let bodyCtx = ctx{ctxReturn = Just rty}
        paramEnv = [Map.fromList (zip params (map unref ptys))]
    -- (a parameter that is borrowed is only read)
    withBorrowed <- getState
    putState withBorrowed{tcReadOnly = [p | (p, TRef _) <- zip params ptys]}
    (inEnv, ins') <- checkValidations bodyCtx paramEnv ins
    term' <- resolveTermination bodyCtx inEnv term
    (_, outs') <- checkValidations bodyCtx (Map.insert "return" rty (head inEnv) : tail inEnv) outs
    (_, body') <- checkStatements False bodyCtx (Map.empty : paramEnv) body
    -- (the sizes of the function end with it)
    after <- getState
    putState after{tcSizeScope = tcSizeScope outer, tcTypeScope = tcTypeScope outer, tcReadOnly = tcReadOnly outer, tcCurrent = tcCurrent outer}
    return (term', ins', outs', body')
  where
    nub' = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- A size is given by the call and is the same for the whole function
notSize :: Variable -> TC ()
notSize var = do
    s <- getState
    when (var `elem` tcReadOnly s) $
        failTc ("Type error: " ++ var ++ " is borrowed (&), so it is only read: a copy of it can be assigned to another variable")
    when (var `elem` tcSizeScope s) $
        failTc ("Type error: " ++ var ++ " is a size parameter of the function, which a call gives, and it cannot be assigned")

-- What shrinks is an integer, which counts down to 0, or a struct or enum value, which loses a field at a time
resolveTermination :: Ctx -> Env -> Maybe Termination -> TC (Maybe Termination)
resolveTermination ctx env (Just (Shrinks variant)) = do
    (ty', variant') <- inferExprR ctx env variant
    -- (what shrinks is what the value is looked through to, as for a Box: the parts of that are smaller)
    (ty'', variant'') <- derefExpr ctx env (ty', variant')
    ty <- zonk ty''
    case ty of
        TInt -> return (Just (Counting variant''))
        TNamed _ -> return (Just (Parts variant''))
        TVariant _ -> return (Just (Parts variant''))
        TBox _ -> return (Just (Parts variant''))
        _ -> failTc ("Type error: shrinks needs an Int, an enum or a struct, got " ++ renderType ty)
resolveTermination _ _ term = return term

checkValidations :: Ctx -> Env -> [ValidationStatement] -> TC (Env, [ValidationStatement])
checkValidations _ env [] = return (env, [])
checkValidations ctx env (vs : rest) = do
    (env', vs') <- checkValidation ctx env vs
    (envAfter, rest') <- checkValidations ctx env' rest
    return (envAfter, vs' : rest')

checkValidation :: Ctx -> Env -> ValidationStatement -> TC (Env, ValidationStatement)
checkValidation ctx env vs =
    case vs of
        ProofAssert proof -> do
            (t, proof') <- inferProofR ctx env proof
            expect "affirmed proof" TBool t
            return (env, ProofAssert proof')
        Assume proof -> do
            (t, proof') <- inferProofR ctx env proof
            expect "assumed proof" TBool t
            return (env, Assume proof')
        AssignProofVar var expr -> do
            -- (a define is the validator's, so it can read what is known of a permission: `define o = origin(b);`)
            outer <- tcGhost <$> getState
            getState >>= \s -> putState s{tcGhost = True}
            (t, expr') <- inferExprR ctx env expr
            getState >>= \s -> putState s{tcGhost = outer}
            env' <- assignVar ctx env var t
            return (env', AssignProofVar var expr')
        Rewrite rule -> do
            rule' <- case rule of
                Refl proof -> Refl . snd <$> inferProofR ctx env proof
                Eval var -> Eval var <$ lookupVar ctx env var
                EvalAll -> return rule
                CheckGtZero proof -> CheckGtZero . snd <$> inferProofR ctx env proof
                CheckRel proof -> CheckRel . snd <$> inferProofR ctx env proof
                UserRewrite name proofs -> UserRewrite name <$> mapM (fmap snd . inferProofR ctx env) proofs
            return (env, Rewrite rule')

-- Expressions and proofs

-- The type of an expression, and the expression with each call of a function that belongs to a type resolved: x.f(a) and
-- Trait::f(x, a) are calls of Type::f for the type of x, and nothing after the checker sees anything else.
inferExprR :: Ctx -> Env -> Expression -> TC (Type, Expression)
inferExprR ctx env expr =
    case expr of
        Val value -> (\t -> (t, expr)) <$> valueType value
        Var var -> do
            t <- lookupVar ctx env var
            t' <- zonk t
            case t' of
                TForall sizes types _ -> failTc ("Type error: " ++ var ++ " has parameters <" ++ intercalate ", " (types ++ sizes) ++ ">, so it is called, as in " ++ var ++ "(...), and cannot be used as a value")
                _ -> return (t, expr)
        F funct@(Val (VFunct _ _ _ (BuiltinFunct (Field owner field)) _)) [struct] -> do
            (structTy, struct') <- inferExprR ctx env struct
            -- (a field of the value itself is read as it is; a field it does not have is read from what it is looked through to)
            direct <- tryTc (readField owner field structTy)
            case direct of
                Just t -> return (t, F funct [struct'])
                Nothing -> do
                    (targetTy, struct'') <- derefExpr ctx env (structTy, struct')
                    t <- readField owner field targetTy
                    return (t, F funct [struct''])
        F funct@(Val (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args -> do
            inferred0 <- mapM (inferExprR ctx env) args
            -- (a tuple's parts are what they are: it is made of their types)
            declared <- if isJust (tupleGeneric name) then return [] else snd <$> ctorInfo name
            inferred <- if length declared == length inferred0 then mapM (uncurry coerce) (zip (map snd declared) inferred0) else return inferred0
            t <- checkConstruct name fields (map fst inferred)
            return (t, F funct (map snd inferred))
        -- Box::new(x): x held in a Box, which has its value
        F (Var "Box::new") args -> case args of
            [x] -> do
                (xt, x') <- inferExprR ctx env x
                return (TBox xt, F (Val (builtinFunct NewBox)) [x'])
            _ -> failTc ("Type error: Box::new takes 1 argument, got " ++ show (length args))
        -- Box::unbox(b): the value that b holds
        F (Var "Box::unbox") args -> case args of
            [b] -> do
                (bt, b') <- inferExprR ctx env b
                t <- zonk bt
                case t of
                    TBox (TArrayOf _ SizeAny) -> failTc "Type error: Box::unbox cannot take an array of no size out of its Box, since it would not know how much to take: read its elements with get and size"
                    TBox inner -> return (inner, F (Val (builtinFunct UnBox)) [b'])
                    _ -> failTc ("Type error: Box::unbox takes a Box, got " ++ renderType t)
            _ -> failTc ("Type error: Box::unbox takes 1 argument, got " ++ show (length args))
        -- Array::empty(): an array of no elements, of the element type that the program decides
        F (Var "Array::empty") args -> case args of
            [] -> do
                elementTy <- freshVar
                let ty = TArrayOf elementTy SizeAny
                return (TBox ty, F (Val (builtinFunct NewEmptyArray)) [])
            _ -> failTc ("Type error: Array::empty takes no arguments, got " ++ show (length args))
        -- Array::uninit(n): n slots that hold nothing, in a Box that carries the size
        F (Var "Array::uninit") args -> case args of
            [n] -> inferExprR ctx env (F (Var "Array::boxed") [n, F (Var "Uninit::empty") []])
            _ -> failTc ("Type error: Array::uninit takes 1 argument, got " ++ show (length args))
        -- Array::boxed(n, x): n copies of x, n known only when the program runs, in a Box that carries the size
        F (Var "Array::boxed") args -> case args of
            [n, x] -> do
                (nt, n') <- inferExprR ctx env n
                expect "argument 1 of Array::boxed" TInt nt
                (xt, x') <- inferExprR ctx env x
                let ty = TArrayOf xt SizeAny
                arrayOk ty
                requireMarker "Clone" xt
                return (TBox ty, F (Val (builtinFunct NewBoxedArray)) [n', x'])
            _ -> failTc ("Type error: Array::boxed takes 2 arguments, got " ++ show (length args))
        F funct args
            | Just NewArray <- builtinHead ctx env funct -> case args of
                [n, x] -> do
                    (nt, n') <- inferExprR ctx env n
                    expect "argument 1 of array" TInt nt
                    (xt, x') <- inferExprR ctx env x
                    (size, sizeArg) <- arraySize (constantInt n') n'
                    let ty = TArrayOf xt size
                    arrayOk ty
                    requireMarker "Clone" xt
                    return (ty, F funct [sizeArg, x'])
                _ -> failTc ("Type error: array takes 2 arguments, got " ++ show (length args))
        F (Val (VFunct _ _ _ (BuiltinFunct ArrayFrom) _)) [Val literal@(VList items)] -> do
            listTy <- valueType literal
            case listTy of
                TList e -> do
                    let ty = TArray e (fromIntegral (length items))
                    arrayOk ty
                    literalOk e
                    return (ty, expr)
                _ -> failTc "Type error: an array literal is made from a list"
        F (Val (VFunct _ _ _ (BuiltinFunct CloneOf) _)) args -> cloneCall args
        -- clone(x) and x.clone(): a copy of x, which has its value (unless the program has a function of that name)
        F (Var "clone") args
            | not (Map.member "clone" (ctxFns ctx)), not (any (Map.member "clone") env) -> cloneCall args
        F (Var ".clone") args@[receiver] -> do
            (receiverTy, _) <- inferExprR ctx env receiver
            t <- zonk receiverTy
            s <- getState
            let owned = case t of
                    TNamed name -> Map.member (maybe name fst (instanceOf name), "clone") (tcAssoc s)
                    _ -> False
            if owned then methodCall "clone" args else cloneCall args
        F (Var ('.' : method)) (receiver : args) -> methodCall method (receiver : args)
        -- what is known of a permission, in an expression of the validator (a define); in code it is not a value there is
        F (Var name) args
            | Just b <- ghostFunction name, b `notElem` [AddrNull, AddrOffset, AddrCast, AddrToInt, AddrFromInt], not (any (Map.member name) env), not (Map.member name (ctxFns ctx)) -> do
              -- (only of a permission: a function of the program named `count`, as a template is, is the program's)
              ofPermission <- permissionArgument b args (inferExprR ctx env)
              if not ofPermission then general (Var name) args else do
                ghostly <- tcGhost <$> getState
                unless ghostly $ failTc ("Type error: " ++ name ++ " is what the validator knows of a permission, and is not a value the program has: it is written in an affirm, a contract, an invariant or a define")
                inferred <- mapM (inferExprR ctx env) args
                ft <- builtinType b
                case (b, inferred) of
                    _ | b `elem` [BlockFilled, BlockContents], [(ut, u')] <- inferred -> do
                        let b' = if b == BlockFilled then UninitFilled else UninitAt
                        ft' <- builtinType b'
                        result <- checkCall name ft' [ut]
                        return (result, F (Val (builtinFunct b')) [u'])
                    _ | b `elem` [BlockFilled, BlockContents] -> case inferred of
                        [(bt, b'), (it, i')] -> do
                            listTy <- checkCall name ft [bt]
                            expect ("argument 2 of " ++ name) TInt it
                            elementTy <- freshVar
                            expect name (TList elementTy) listTy
                            return (elementTy, F (Val (builtinFunct Get)) [F (Val (builtinFunct b)) [b'], i'])
                        _ -> failTc ("Type error: " ++ name ++ " takes a permission and a slot, as in " ++ name ++ "(b, i)")
                    _ -> do
                        result <- checkCall name ft (map fst inferred)
                        return (result, F (Val (builtinFunct b)) (map snd inferred))
        -- Addr::alloc(n), Addr::get(p, i, b), Block::split(b, i), ...: the operations on addresses and permissions (POINTERS.md)
        F (Var name) args
            | Just b <- pointerBuiltin name, not (any (Map.member name) env), not (Map.member name (ctxFns ctx)) -> do
                inferred0 <- mapM (inferExprR ctx env) args
                ft <- builtinType b
                inferred <- coerceArguments ft inferred0
                result <- checkBuiltinCall (Just b) name ft (map fst inferred)
                return (result, F (Val (builtinFunct b)) (map snd inferred))
        F (Var name@('<' : _)) args -> mapM (inferExprR ctx env) args >>= callResolved name
        F (Var name) args
            | Just (path, function) <- traitPath name -> traitCall path function args
        F funct args -> general funct args
  where
    cloneCall args = case args of
        [x] -> do
            (xt, x') <- inferExprR ctx env x
            requireMarker "Clone" xt
            return (xt, F (Val (builtinFunct CloneOf)) [x'])
        _ -> failTc ("Type error: clone takes 1 argument, got " ++ show (length args))
    methodCall method (receiver : args) = do
            inferred <- mapM (inferExprR ctx env) (receiver : args)
            receiverTy <- zonk (fst (head inferred))
            case (listMethod method, receiverTy) of
                -- l.push(x), l.size(), a.get(i): the function of that name on a list or an array
                -- (with the arguments that are inferred already: a chain of them is inferred once)
                (Just b, ty) | sequenceType ty -> do
                    let funct = Val (builtinFunct b)
                    (ft, funct') <- inferExprR ctx env funct
                    ordinaryBuiltin funct funct' ft inferred
                _ -> do
                    owner <- ownerOfValue method (fst (head inferred))
                    resolveAssociated owner method >>= \name -> callResolved name inferred
    methodCall _ [] = failTc "Type error: a method is called on a value"
    -- Trait::f(x) and Type::f(x)
    traitCall path function args = do
                s <- getState
                case (Map.lookup path (tcTraits s), Map.member path (tcTypes s) || Map.member path (tcGenerics s)) of
                    (Just functions, _) -> do
                        inferred <- mapM (inferExprR ctx env) args
                        owner <- ownerThroughTrait path functions function (map fst inferred)
                        callResolved (implFunctionName owner (Just path) function) inferred
                    (Nothing, True) -> do
                        inferred <- mapM (inferExprR ctx env) args
                        resolveAssociated path function >>= \full -> callResolved full inferred
                    _ -> general (Var (path ++ "::" ++ function)) args
    general funct args = do
        s <- getState
        case funct of
            Var name | Just template <- Map.lookup name (tcTemplates s), not (any (Map.member name) env) -> do
                inferred <- mapM (inferExprR ctx env) args
                (result, instance', args', sizes) <- templateCall name template inferred
                return (result, F (Var instance') (args' ++ sizes))
            _ -> generalCall funct args
    generalCall funct args = do
        (ft, funct') <- case funct of
            Var name | Nothing <- builtinHead ctx env funct -> (\t -> (t, funct)) <$> lookupVar ctx env name
            _ -> inferExprR ctx env funct
        ftz <- zonk ft
        case ftz of
            TForall sizes types inner -> do
                inferredG <- mapM (inferExprR ctx env) args
                (result, args') <- genericCall (describe funct) sizes types inner inferredG
                return (result, F funct' args')
            _ -> ordinary funct funct' ft args
    ordinary funct funct' ft args = do
        inferred0 <- mapM (inferExprR ctx env) args
        -- (size(v), get(v, i), ... on a value of a struct are the functions of its impl)
        owner <- case (builtinHead ctx env funct, inferred0) of
            (Just b, (xt, _) : _) | Just fname <- sequenceFunction b -> (,) fname <$> structOwner xt
            _ -> return ("", Nothing)
        case owner of
            (fname, Just struct) -> resolveAssociated struct fname >>= \full -> callResolved full inferred0
            _ -> ordinaryBuiltin funct funct' ft inferred0
    ordinaryBuiltin funct funct' ft inferred0 = do
        -- (a value that is tested for its variant, cast to one or read for a field is looked through what it holds first, Box or Deref)
        inferred0 <- case (builtinHead ctx env funct, inferred0) of
            (Just b, first : rest) | isLookThrough b -> do
                first' <- derefExpr ctx env first
                return (first' : rest)
            _ -> return inferred0
        -- (a builtin takes what it is given: it looks through a Box itself)
        inferred <- case builtinHead ctx env funct of
            -- (the builtins of bytes take a number written out as a Byte)
            Just b | b `elem` [WriteByte, WriteError, PathByte, StoreByte] -> coerceArguments ft inferred0
            Just _ -> return inferred0
            Nothing -> coerceArguments ft inferred0
        let ats = map fst inferred
        result <- checkBuiltinCall (builtinHead ctx env funct) (describe funct) ft ats
        comparing funct ats
        return (result, F funct' (map snd inferred))
    describe (Var name) = name
    describe _ = "call"
    isSuffixOf' suffix text = reverse suffix == take (length suffix) (reverse text)
    -- the call of a function of the program by name, with arguments that are checked already
    callResolved name inferred0 = do
        -- (a drop is called by native code where a value goes out of scope, and by the check of its impl, and by nothing else)
        current <- tcCurrent <$> getState
        when (" as Drop>::drop" `isSuffixOf'` name && maybe True (\c -> take 9 c /= "Drop for ") current) $
            failTc ("Type error: " ++ name ++ " is a drop, which is called where a value goes out of scope, and not by the program")
        unless (Map.member name (ctxFns ctx)) $
            failTc ("Type error: " ++ name ++ " is not defined before this call (there is no such function, or its impl comes later)")
        ft <- lookupVar ctx env name
        ftz <- zonk ft
        case ftz of
            -- (a function of `impl<T> Vec<T>` has the types and sizes of the impl: the arguments decide them)
            TForall sizes types inner -> do
                (result, args') <- genericCall name sizes types inner inferred0
                return (result, F (Var name) args')
            _ -> do
                inferred <- coerceArguments ft inferred0
                result <- checkCall name ft (map fst inferred)
                return (result, F (Var name) (map snd inferred))

-- The function that Type::f means: the one function of that name that the impls of Type define. If several do, the call has
-- to say which, with Trait::f(x), <Type as Trait>::f(...) or <Type>::f(...).
resolveAssociated :: Name -> Name -> TC Name
resolveAssociated owner function = do
    s <- getState
    case Map.findWithDefault [] (owner, function) (tcAssoc s) of
        [] -> failTc ("Type error: " ++ owner ++ "::" ++ function ++ " is not defined before this call (there is no such function, or its impl comes later)")
        [origin] -> return (implFunctionName owner origin function)
        origins ->
            failTc
                ( "Type error: "
                    ++ owner
                    ++ "::"
                    ++ function
                    ++ " is ambiguous, several impls define it. Call the one that is meant by its path: "
                    ++ intercalate " or " [implFunctionName owner origin function ++ "(...)" | origin <- origins]
                )

-- Trait::function
traitPath :: Name -> Maybe (Name, Name)
traitPath = go ""
  where
    go acc (':' : ':' : rest) | not (null acc) && not (null rest) = Just (reverse acc, rest)
    go acc (c : rest) = go (c : acc) rest
    go _ [] = Nothing

-- The struct or enum a value belongs to, whose function a call names
ownerOfValue :: Name -> Type -> TC Name
ownerOfValue function ty = do
    t <- zonk ty
    case t of
        -- (a struct with types and sizes has the functions of its impl, whatever it is given)
        TNamed name -> return (maybe name fst (instanceOf name))
        TVariant variant -> fst <$> ctorInfo variant
        TVar _ -> failTc ("Type error: the type of the value whose function " ++ function ++ " is called is not known yet; annotate it")
        other@TBox{} -> failTc ("Type error: " ++ function ++ " is called on a " ++ renderType other ++ ", which has no functions: call it on the value inside, as in Box::unbox(b)." ++ function ++ "(...)")
        other -> failTc ("Type error: " ++ function ++ " is called on a " ++ renderType other ++ ", which has no functions")

-- Trait::function(x, ...) is the function of the type of the argument that the trait's signature gives the type Self. That
-- type must implement the trait.
ownerThroughTrait :: Name -> [TraitFn] -> Name -> [Type] -> TC Name
ownerThroughTrait trait functions function ats =
    case [f | f <- functions, traitFnName f == function] of
        [] -> failTc ("Type error: trait " ++ trait ++ " has no function " ++ function)
        f : _ -> do
            let Signature ptys _ _ _ = traitFnSignature f
                path = trait ++ "::" ++ function
            when (length ptys /= length ats) $
                failTc ("Type error: " ++ path ++ " takes " ++ show (length ptys) ++ " arguments, got " ++ show (length ats))
            case [i | (i, t) <- zip [0 :: Int ..] ptys, unref t == TNamed "Self"] of
                [] -> failTc ("Type error: " ++ path ++ " has no Self parameter to tell the type by: call it on the type, as in Type::" ++ function ++ "(...)")
                i : _ -> do
                    owner <- ownerOfValue path (ats !! i)
                    impls <- tcImpls <$> getState
                    unless (Set.member (trait, owner) impls) $ failTc ("Type error: " ++ owner ++ " does not implement " ++ trait)
                    return owner

-- Traits and impls

-- The functions of a trait have their types and contracts checked with Self as a type that has no constructors, so a
-- mistake in the trait is reported at the trait and not at its first impl
checkTrait :: Name -> [Variable] -> [TraitFn] -> TC ()
checkTrait name params functions = do
    s <- getState
    when (Map.member name (tcTraits s) || Map.member name (tcTypes s)) $ failTc ("Type error: " ++ name ++ " is already defined")
    putState s{tcTypes = Map.insert "Self" [] (tcTypes s), tcTraitSelf = Just (functions ++ concat (Map.elems (tcTraits s)))}
    -- (the types of the trait are types in its signatures and contracts)
    withGenerics [] params $ forM_ functions $ \f -> do
        let Signature ptys rty _ _ = traitFnSignature f
            ctx = Ctx Map.empty (Just rty)
            paramEnv = [Map.fromList (zip (traitFnParams f) (map unref ptys))]
        mapM_ checkType (rty : map unref ptys)
        (inEnv, _) <- checkValidations ctx paramEnv (traitFnRequires f)
        _ <- checkValidations ctx (Map.insert "return" rty (head inEnv) : tail inEnv) (traitFnEnsures f)
        return ()
    s' <- getState
    putState s'{tcTypes = Map.delete "Self" (tcTypes s'), tcTraits = Map.insert name functions (tcTraits s'), tcTraitParams = Map.insert name params (tcTraitParams s'), tcTraitSelf = Nothing}

-- The types of a trait replaced by the types an impl gives it
substTraitArgs :: [Variable] -> [Arg] -> Type -> Type
substTraitArgs params args = substitute [] [(p, t) | (p, ArgType t) <- zip params args]

substSelf :: Name -> Type -> Type
substSelf owner (TNamed "Self") = TNamed owner
substSelf owner (TList t) = TList (substSelf owner t)
substSelf owner (TArrayOf t size) = TArrayOf (substSelf owner t) size
substSelf owner (TBox t) = TBox (substSelf owner t)
substSelf owner (TAddr t) = TAddr (substSelf owner t)
substSelf owner (TUninit t) = TUninit (substSelf owner t)
substSelf owner (TBlock t) = TBlock (substSelf owner t)
substSelf owner (TRef t) = TRef (substSelf owner t)
substSelf owner (TFn args ret) = TFn (map (substSelf owner) args) (substSelf owner ret)
substSelf _ t = t

-- The functions of an impl are checked as definitions at the top of the program, in order. For a trait impl they are then
-- compared with the trait: the same functions, with the types the trait gives with Self replaced by the type. Each trait
-- function also gets a function of the program that has the trait's contracts and calls the impl's function:
--
--   fn "Area for Shape::area"(self: Shape) -> Int [{ the trait's input contract }] [{ the trait's output contract }] {
--       return Shape::area(self);
--   };
--
-- The validator checks it like any function, and what it proves is that the impl may be used wherever the trait is: the
-- trait's input contract must give the impl's (the call is checked against the impl's input contract), and the impl's
-- output contract must give the trait's (the return is checked against it).
checkImpl :: Ctx -> Env -> Maybe Name -> [Arg] -> Name -> Name -> [Statement] -> TC (Ctx, Env, [Statement])
checkImpl ctx env trait traitArgs typeName selfName functions = do
    declared <- getState
    -- (a struct with parameters has them in the impl, `impl<T> Vec<T>`, and its type is a different one for each)
    unless (Map.member typeName (tcGenerics declared)) $ void (typeCtors typeName)
    -- (the type implements the trait from the first function on, so a function can call an earlier one through the trait; if the
    -- impl is not accepted the program is refused, so this is never seen)
    (required, traitParams) <- case trait of
        Nothing -> return ([], [])
        Just traitName -> do
            s <- getState
            found <- maybe (failTc ("Type error: unknown trait " ++ traitName)) return (Map.lookup traitName (tcTraits s))
            let params = Map.findWithDefault [] traitName (tcTraitParams s)
            when (length params /= length traitArgs) $
                failTc ("Type error: trait " ++ traitName ++ " has parameters <" ++ intercalate ", " params ++ ">, which impl " ++ traitName ++ " for " ++ typeName ++ " gives " ++ show (length traitArgs))
            when (Set.member (traitName, typeName) (tcImpls s)) $ failTc ("Type error: " ++ typeName ++ " already implements " ++ traitName)
            putState s{tcImpls = Set.insert (traitName, typeName) (tcImpls s), tcImplArgs = Map.insert (traitName, typeName) (selfName, traitArgs) (tcImplArgs s)}
            when (traitName `elem` ["Clone", "Copy"] && null found && null params) $ checkMarkerImpl traitName typeName
            -- (a type with a drop is freed by it: it is not linear, and not copied, since each copy would be freed)
            when (traitName == "Drop") $ do
                s' <- getState
                when (Set.member typeName (tcLinear s')) $ failTc ("Type error: impl Drop for " ++ typeName ++ ": " ++ typeName ++ " is linear, so it is used by the program and not dropped")
                when (Set.member ("Clone", typeName) (tcImpls s') || Set.member ("Copy", typeName) (tcImpls s')) $
                    failTc ("Type error: impl Drop for " ++ typeName ++ ": " ++ typeName ++ " is Clone, and a copy of a value with a drop would be dropped twice")
                -- (a drop frees the memory a value holds: native code tells a value that was moved out by its bytes being 0, which a value
                -- that holds memory never is, since the address of an allocation is not 0, so a type with a drop holds a permission)
                holding <- case Map.lookup typeName (tcGenerics s') of
                    Just (_, fields) -> or <$> mapM (holdsGhost . snd) fields
                    Nothing -> holdsGhost (TNamed typeName)
                unless holding $ failTc ("Type error: impl Drop for " ++ typeName ++ ": " ++ typeName ++ " holds no permission (Block<T>), and a drop is how a value frees the memory it holds; a value that has to be closed is a linear type, closed by a call")
                putState s'{tcDrops = Set.insert typeName (tcDrops s')}
            return (found, params)
    (ctx', env', checked) <- definitions True (ctx, env, []) functions
    case trait of
        Nothing -> return (ctx', env', checked)
        Just traitName -> do
            let here = "impl " ++ traitName ++ " for " ++ typeName
                defined = [(implFunctionPart name, (Signature ptys rty sizes types, term)) | Assign name (Val (VFunct _ _ _ (NativeFunct (Signature ptys rty sizes types) term _) _)) <- checked]
                wanted = map traitFnName required
                -- (what the trait asks for, with Self the type and the types of the trait the ones this impl gives)
                inImpl = substTraitArgs traitParams traitArgs . substSelf selfName
            case map fst defined \\ wanted of
                extra : _ -> failTc ("Type error: " ++ here ++ " has a function " ++ extra ++ ", which " ++ traitName ++ " does not declare")
                [] -> return ()
            case wanted \\ map fst defined of
                missing : _ -> failTc ("Type error: " ++ here ++ " lacks the function " ++ missing)
                [] -> return ()
            wrappers <- forM required $ \f -> do
                let Signature ptys rty _ _ = traitFnSignature f
                    expected = Signature (map inImpl ptys) (inImpl rty) [] []
                case lookup (traitFnName f) defined of
                    Just (Signature aptys arty asizes atypes, term) -> do
                        let actual = Signature aptys arty [] []
                        when (actual /= expected) $
                            failTc ("Type error: " ++ here ++ ": " ++ traitFnName f ++ " is " ++ renderSignature actual ++ ", but " ++ traitName ++ " declares " ++ renderSignature expected)
                        -- (an impl of a struct with types is for any of them, and the check of it is too)
                        return (wrapper traitName typeName f (Signature aptys arty asizes atypes) term)
                    Nothing -> failTc ("Type error: " ++ here ++ " lacks the function " ++ traitFnName f)
            (ctx'', env'', wrapped) <- definitions False (ctx', env', []) wrappers
            return (ctx'', env'', [CopyDef typeName | traitName == "Copy", null required] ++ [DropDef typeName | traitName == "Drop"] ++ checked ++ wrapped)
  where
    -- The functions of the impl can be called as Type::f from the next one on, itself included; the functions that check
    -- the impl against its trait cannot
    definitions _ state [] = return state
    definitions own (c, e, done) (stmt : rest) = do
        case stmt of
            Assign name _ | own -> do
                s <- getState
                putState s{tcAssoc = Map.insertWith (\new old -> old ++ new) (typeName, implFunctionPart name) [trait] (tcAssoc s)}
            _ -> return ()
        (c', e', stmt') <- checkStatement True c e stmt
        definitions own (c', e', done ++ [stmt']) rest
    renderSignature (Signature ptys rty _ _) = renderType (TFn ptys rty)
    wrapper traitName owner f signature term =
        Assign
            (implCheckName traitName owner (traitFnName f))
            ( Val
                ( VFunct
                    (traitFnParams f)
                    (traitFnRequires f)
                    (traitFnEnsures f)
                    (NativeFunct signature (if term == Just MayDiverge then Just MayDiverge else Nothing) [Return (F (Var (implFunctionName owner (Just traitName) (traitFnName f))) (map Var (traitFnParams f)))])
                    []
                )
            )

inferProof :: Ctx -> Env -> VariableProof -> TC Type
inferProof ctx env proof = fst <$> inferProofR ctx env proof

-- The type of a proof, and the proof with each call of a function of the program resolved: `Type::f(x)` and `Trait::f(x)` are calls of
-- the impl's function for the type, and a function with sizes is given them as its last arguments, as a call is.
inferProofR :: Ctx -> Env -> VariableProof -> TC (Type, VariableProof)
inferProofR ctx env proof =
    case proof of
        ATerm var -> (\t -> (t, proof)) <$> lookupProofVar ctx env var
        BVar var -> (\t -> (t, proof)) <$> lookupVar ctx env var
        CTerm value -> (\t -> (t, proof)) <$> valueType value
        FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct (Field owner field)) _)) [struct] -> do
            (structTy, struct') <- inferProofR ctx env struct
            direct <- tryTc (readField owner field structTy)
            case direct of
                Just t -> return (t, FApp funct [struct'])
                Nothing -> do
                    (targetTy, struct'') <- derefProof (structTy, struct')
                    t <- readField owner field targetTy
                    return (t, FApp funct [struct''])
        FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args -> do
            inferred <- mapM (inferProofR ctx env) args
            t <- checkConstruct name fields (map fst inferred)
            return (t, FApp funct (map snd inferred))
        FApp funct@(CTerm (VFunct _ _ _ (BuiltinFunct NewArray) _)) [n, x] -> do
            (nt, n') <- inferProofR ctx env n
            expect "argument 1 of array" TInt nt
            (xt, x') <- inferProofR ctx env x
            size <- proofSize (constantProofInt n) n
            let ty = TArrayOf xt size
            arrayOk ty
            return (ty, FApp funct [n', x'])
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct NewArray) _)) args -> failTc ("Type error: array takes 2 arguments, got " ++ show (length args))
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct ArrayFrom) _)) [CTerm literal@(VList items)] -> do
            listTy <- valueType literal
            case listTy of
                TList e -> do
                    let ty = TArray e (fromIntegral (length items))
                    arrayOk ty
                    literalOk e
                    return (ty, proof)
                _ -> failTc "Type error: an array literal is made from a list"
        -- what is known of a permission (base(b), cap(b), filled(b, i), at(b, i), ...) and the operations on addresses that need none
        FApp (ATerm name) args
            | not (shadowedByFunction name), not (Map.member name (ctxFns ctx)), Just b <- ghostFunction name -> do
              ofPermission <- permissionArgument b args (inferProofR ctx env)
              if not ofPermission then ordinaryCall name args else do
                inferred <- mapM (inferProofR ctx env) args
                ft <- builtinType b
                case b of
                    -- (filled(u) and at(u) of an Uninit)
                    _ | b `elem` [BlockFilled, BlockContents], [(ut, u')] <- inferred -> do
                        let b' = if b == BlockFilled then UninitFilled else UninitAt
                        ft' <- builtinType b'
                        result <- checkCall name ft' [ut]
                        return (result, FApp (CTerm (builtinFunct b')) [u'])
                    -- (filled(b, i) and at(b, i) are elements of the two arrays of the block)
                    _ | b `elem` [BlockFilled, BlockContents] -> case inferred of
                        [(bt, b'), (it, i')] -> do
                            listTy <- checkCall name ft [bt]
                            expect ("argument 2 of " ++ name) TInt it
                            elementTy <- freshVar
                            expect name (TList elementTy) listTy
                            return (elementTy, FApp (CTerm (builtinFunct Get)) [FApp (CTerm (builtinFunct b)) [b'], i'])
                        _ -> failTc ("Type error: " ++ name ++ " takes a permission and a slot, as in " ++ name ++ "(b, i)")
                    _ -> do
                        result <- checkCall name ft (map fst inferred)
                        return (result, FApp (CTerm (builtinFunct b)) (map snd inferred))
            | not (shadowed name), not (Map.member name (ctxFns ctx)), name == "whole" ->
                failTc "Type error: whole(b) is a statement of its own, affirm whole(b); (it is two facts: start(b) = 0 and cap(b) = extent(origin(b)))"
        -- a function with bounds is the function made for the types of the arguments; any other function of the program is itself
        FApp (ATerm name) args | not (shadowed name) -> ordinaryCall name args
        FApp funct args -> do
            (_, funct') <- inferProofR ctx env funct
            inferred0 <- mapM (inferProofR ctx env) args
            inferred <- case (proofBuiltin funct', inferred0) of
                (Just b, first : rest) | isLookThrough b -> do
                    first' <- derefProof first
                    return (first' : rest)
                _ -> return inferred0
            owner <- case (proofBuiltin funct', inferred) of
                (Just b, (xt, _) : _) | Just fname <- sequenceFunction b -> (,) fname <$> structOwner xt
                _ -> return ("", Nothing)
            case owner of
                -- size(v), get(v, i), ...: on a value of a struct they are the functions of its impl, and in a trait on a Self
                (fname, Just "Self") -> do
                    traitFns <- tcTraitSelf <$> getState
                    case [f | Just fs <- [traitFns], f <- fs, traitFnName f == fname] of
                        f : _ | length (fst (signatureTypes f)) == length inferred -> return (snd (signatureTypes f), FApp funct' (map snd inferred))
                        _ -> failTc ("Type error: " ++ fname ++ " is called on a Self, which the trait has no function " ++ fname ++ " for")
                (fname, Just struct) -> do
                    full <- resolveAssociated struct fname
                    ghostCall full inferred
                _ -> general funct' inferred
        Forall index guards body -> do
            let env' = Map.singleton index TInt : env
            guards' <- mapM (\g -> inferProofR ctx env' g >>= \(t, g') -> expect "guard of forall" TBool t >> return g') guards
            (bt, body') <- inferProofR ctx env' body
            expect "body of forall" TBool bt
            return (TBool, Forall index guards' body')
  where
    -- A proof looked through to the value it holds, by a call of its type's `deref`, as an expression is (see derefExpr)
    derefProof (ty, proof) = do
        t <- zonk ty
        case t of
            TBox _ -> return (t, proof)
            _ -> do
                target <- derefTarget t
                case target of
                    Just _ -> do
                        owner <- derefOwner t
                        derefProof =<< ghostCall (implFunctionName owner (Just "Deref") "deref") [(t, proof)]
                    Nothing -> return (t, proof)
    ordinaryCall name args = do
        inferred <- mapM (inferProofR ctx env) args
        s <- getState
        case Map.lookup name (tcTemplates s) of
            Just template -> do
                (result, instance', _, sizes) <- templateCall name template [(t, Val (VInt 0)) | (t, _) <- inferred]
                return (result, FApp (ATerm instance') (map snd inferred ++ map exprToProof sizes))
            Nothing -> do
                target <- ghostTarget name (map fst inferred)
                case target of
                    Just full -> ghostCall full inferred
                    Nothing -> general (ATerm name) inferred
    shadowed name = any (Map.member name) env
    -- (a field or a variable named like a ghost function, `cap`, does not hide it: it is not called)
    shadowedByFunction name = or [isFunction t | scope <- env, Just t <- [Map.lookup name scope]]
    isFunction t = case t of
        TFn{} -> True
        TForall{} -> True
        _ -> False
    signatureTypes f = let Signature ptys rty _ _ = traitFnSignature f in (ptys, rty)
    ghostCall full inferred = do
        ft <- lookupVar ctx env full
        ftz <- zonk ft
        case ftz of
            TForall sizes types inner -> do
                (result, args') <- genericCall full sizes types inner [(t, Val (VInt 0)) | (t, _) <- inferred]
                return (result, FApp (ATerm full) (map snd inferred ++ map exprToProof (drop (length inferred) args')))
            _ -> do
                result <- checkCall full ft (map fst inferred)
                return (result, FApp (ATerm full) (map snd inferred))
    general funct inferred = do
        ft <- inferProof ctx env funct
        result <- checkBuiltinCall (proofBuiltin funct) "call" ft (map fst inferred)
        comparing (proofHead funct) (map fst inferred)
        return (result, FApp funct (map snd inferred))
    -- the function of the program that a name in a call stands for, if it stands for one
    ghostTarget name argTypes
        | take 1 name == "<" = return (Just name)
        | Just (path, function) <- traitPath name = do
            s <- getState
            case (Map.lookup path (tcTraits s), Map.member path (tcTypes s) || Map.member path (tcGenerics s)) of
                (Just functions, _) -> do
                    owner <- ownerThroughTrait path functions function argTypes
                    return (Just (implFunctionName owner (Just path) function))
                (Nothing, True) -> Just <$> resolveAssociated path function
                _ -> return Nothing
        | Map.member name (ctxFns ctx) = return (Just name)
        | otherwise = return Nothing

-- Whether a ghost function is applied to a permission, which is what makes it one: `count(v)` of a value that is not a permission is a call of
-- a function of the program named count (the operations on addresses and `extent`, of an origin, are taken as they are)
permissionArgument :: BuiltinFunct -> [a] -> (a -> TC (Type, a)) -> TC Bool
permissionArgument b args infer
    | b `elem` [AddrNull, AddrOffset, AddrCast, AddrToInt, AddrFromInt, BlockExtent] = return True
    | otherwise = case args of
        first : _ -> do
            (t, _) <- infer first
            t' <- zonk t
            return $ case t' of
                TBlock _ -> True
                TRef (TBlock _) -> True
                TUninit _ -> b `elem` [BlockFilled, BlockContents]
                TRef (TUninit _) -> b `elem` [BlockFilled, BlockContents]
                _ -> False
        [] -> return False

-- The operations on addresses and permissions, by the names a program calls them by
pointerBuiltin :: Name -> Maybe BuiltinFunct
pointerBuiltin name =
    lookup
        name
        [ ("Addr::null", AddrNull)
        , ("Addr::offset", AddrOffset)
        , ("Addr::cast", AddrCast)
        , ("Addr::toInt", AddrToInt)
        , ("Addr::fromInt", AddrFromInt)
        , ("Addr::alloc", AllocPair)
        , ("Addr::get", AddrGet)
        , ("Addr::write", AddrWrite)
        , ("Addr::take", TakePair)
        , ("Addr::dropValue", AddrDropValue)
        , ("Addr::dropRange", AddrDropRange)
        , ("Addr::resize", ResizePair)
        , ("Addr::free", AddrFree)
        , ("Block::split", SplitPair)
        , ("Block::join", BlockJoin)
        , ("Block::assume", BlockAssume)
        , ("Block::cast", BlockCast)
        , ("Uninit::empty", UninitEmpty)
        , ("Uninit::new", UninitNew)
        , ("Uninit::get", UninitGet)
        , ("Uninit::take", UninitTake)
        , ("Uninit::discard", UninitDiscard)
        , ("replace", Replace)
        , ("I8::from", ToWord True 8)
        , ("I16::from", ToWord True 16)
        , ("I32::from", ToWord True 32)
        , ("U16::from", ToWord False 16)
        , ("U32::from", ToWord False 32)
        ]

-- What a proof can say of a permission, and the operations on addresses a proof can use (they need no permission)
ghostFunction :: Name -> Maybe BuiltinFunct
ghostFunction name =
    lookup
        name
        [ ("base", BlockBase)
        , ("cap", BlockCap)
        , ("filled", BlockFilled)
        , ("at", BlockContents)
        , ("origin", BlockOrigin)
        , ("start", BlockStart)
        , ("extent", BlockExtent)
        , ("count", BlockCount)
        , ("Addr::null", AddrNull)
        , ("Addr::offset", AddrOffset)
        , ("Addr::cast", AddrCast)
        , ("Addr::toInt", AddrToInt)
        , ("Addr::fromInt", AddrFromInt)
        ]

-- The builtin that a method of a list or an array is
listMethod :: Name -> Maybe BuiltinFunct
listMethod method = lookup method [("size", Size), ("first", First), ("last", Last), ("get", Get), ("push", Push), ("pop", Pop), ("set", Set)]

-- Whether a type is a list or an array, which have the functions of the builtins as methods
sequenceType :: Type -> Bool
sequenceType ty = case ty of
    TList _ -> True
    TArrayOf{} -> True
    TBox TArrayOf{} -> True
    _ -> False

-- The functions of a list that a struct can have of its own: `size(v)` is the function `size` of the impl of the type of `v`
sequenceFunction :: BuiltinFunct -> Maybe Name
sequenceFunction b = case b of
    Size -> Just "size"
    First -> Just "first"
    Last -> Just "last"
    Get -> Just "get"
    Push -> Just "push"
    Pop -> Just "pop"
    Set -> Just "set"
    _ -> Nothing

-- The struct (without the types it is given) that a type is, or Self in a trait
structOwner :: Type -> TC (Maybe Name)
structOwner ty = do
    t <- zonk ty
    return $ case t of
        TNamed name -> Just (maybe name fst (instanceOf name))
        _ -> Nothing

-- (a name in a proof is a variable of the program or the builtin of that name, as for an expression)
proofBuiltin :: VariableProof -> Maybe BuiltinFunct
proofBuiltin (CTerm (VFunct _ _ _ (BuiltinFunct b) _)) = Just b
proofBuiltin _ = Nothing

-- Equality is structural, which functions do not have
comparing :: Expression -> [Type] -> TC ()
comparing (Val (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) (t : _)
    | rel `elem` [Eq, NotEq] = do
        t' <- zonk t
        case t' of
            TFn{} -> failTc "Type error: functions cannot be compared"
            TUninit _ -> failTc "Type error: an Uninit cannot be compared, since it may hold nothing: what it holds is compared, as in Uninit::get(a) = Uninit::get(b)"
            _ -> do
                ghostly <- holdsGhost t'
                when ghostly $ failTc ("Type error: " ++ renderType t' ++ " holds a permission, which cannot be compared: what a permission says is compared, as in at(a, 0) = at(b, 0)")
comparing _ _ = return ()

proofHead :: VariableProof -> Expression
proofHead (CTerm value) = Val value
proofHead _ = Var ""

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
        TNamed n | Just (_, args) <- instanceOf n -> or [usesParam u | ArgType u <- args]
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
genericCall :: String -> [Variable] -> [Variable] -> Type -> [(Type, Expression)] -> TC (Type, [Expression])
genericCall name names types inner inferred = do
    (instantiated, sizes, given') <- instantiateGenerics names types inner
    case instantiated of
        TFn pts rty
            | length pts - length names /= length inferred ->
                failTc ("Type error: " ++ name ++ " takes " ++ show (length pts - length names) ++ " arguments, got " ++ show (length inferred))
            | otherwise -> do
                args <- mapM (\(i, pt, arg) -> coerce (unref pt) arg >>= \(at, arg') -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) (unref pt) at >> return arg') (zip3 [1 ..] pts inferred)
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
                return (result, args ++ given)
        _ -> failTc ("Type error: " ++ name ++ " is not a function")

-- The argument that a call gives a size parameter of a function: a constant, or a size parameter of the function that calls
sizeArgument :: String -> Variable -> Size -> TC Expression
sizeArgument name n size = case size of
    SizeConst c -> return (Val (VInt c))
    SizeParam p -> return (Var p)
    _ -> failTc ("Type error: the size " ++ n ++ " of " ++ name ++ " cannot be worked out from its arguments: an argument has to be an array of that size")

-- Functions with bounds

declareTemplate :: Ctx -> Name -> [Bound] -> [Variable] -> Signature -> [ValidationStatement] -> [ValidationStatement] -> Maybe Termination -> [Statement] -> TC ()
declareTemplate ctx name bounds params signature@(Signature _ _ _ types) ins outs term body = do
    s <- getState
    when (Map.member name (ctxFns ctx) || Map.member name (tcTemplates s) || Map.member name stdLibCtx) $ failTc ("Type error: " ++ name ++ " is already defined")
    forM_ bounds $ \(param, trait, args) -> do
        unless (param `elem` types) $ failTc ("Type error: " ++ param ++ " is bounded by " ++ trait ++ " but is not a type of " ++ name)
        case Map.lookup trait (tcTraitParams s) of
            Nothing | Map.member trait (tcTraits s) -> unless (null args) $ failTc ("Type error: trait " ++ trait ++ " has no types, but the bound on " ++ param ++ " gives it some")
            Nothing -> failTc ("Type error: unknown trait " ++ trait ++ " in the bound on " ++ param ++ " of " ++ name)
            Just params' -> when (length params' /= length args) $
                failTc ("Type error: trait " ++ trait ++ " has parameters <" ++ intercalate ", " params' ++ ">, which the bound on " ++ param ++ " of " ++ name ++ " gives " ++ show (length args))
    putState s{tcTemplates = Map.insert name (Template bounds ctx params signature ins outs term body) (tcTemplates s)}

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
                TNamed "Self" -> return (trait == "Clone")
                -- (a tuple has what all of its parts have)
                TNamed name | Just (base, args) <- instanceOf name, Just _ <- tupleGeneric base -> allM' [go (depth + 1) lenient t | ArgType t <- args]
                TNamed name -> declared depth lenient name
                TVariant variant -> ctorInfo variant >>= \(owner, _) -> declared depth lenient owner
                _ -> return False
    allM' [] = return True
    allM' (m : ms) = m >>= \ok -> if ok then allM' ms else return False
    declared depth lenient name = do
        s <- getState
        let base = maybe name fst (instanceOf name)
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
        TNamed name -> maybe name fst (instanceOf name)
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
            Just (selfName, given) ->
                let (sizesBound, typesBound) = case instanceOf selfName of
                        Just (_, selfArgs) -> ([(p, s) | (ArgSize (SizeParam p), ArgSize s) <- zip selfArgs args], [(p, t) | (ArgType (TParam p), ArgType t) <- zip selfArgs args])
                        Nothing -> ([], [])
                in Just [substitute sizesBound typesBound t | ArgType t <- given]
    case ty of
        TList e -> return (builtin e ["Sequence", "Growable"] >>= nonEmpty)
        TArrayOf e _ -> return (builtin e ["Sequence"] >>= nonEmpty)
        TBox (TArrayOf e _) -> return (builtin e ["Sequence"] >>= nonEmpty)
        TNamed name -> return (maybe (own name []) (\(base, args) -> own base args) (instanceOf name))
        TVariant variant -> (\(enum, _) -> own enum []) <$> ctorInfo variant
        _ -> return Nothing
  where
    nonEmpty xs = if null xs then Nothing else Just xs

-- A call of a function with bounds: the types of the arguments give the types of the function, each of which has to implement what its bounds say,
-- and the function is checked for those types, once (it is a function of the program named after them: total[Vec<Int>]). The call is a call of that.
templateCall :: Name -> Template -> [(Type, Expression)] -> TC (Type, Name, [Expression], [Expression])
templateCall name template inferred = do
    let Signature ptys rty sizes types = tmplSignature template
    (instantiated, sizeVars, typeVars) <- instantiateGenerics sizes types (TFn ptys rty)
    case instantiated of
        TFn pts result
            | length pts - length sizes /= length inferred ->
                failTc ("Type error: " ++ name ++ " takes " ++ show (length pts - length sizes) ++ " arguments, got " ++ show (length inferred))
            | otherwise -> do
                args <- mapM (\(i, pt, arg) -> coerce (unref pt) arg >>= \(at, arg') -> expect ("argument " ++ show (i :: Int) ++ " of " ++ name) (unref pt) at >> return arg') (zip3 [1 ..] pts inferred)
                let given = zip types typeVars
                -- (a bound on a type that another bound decides waits until that one has: the passes end when all are met, or none can be)
                let attempt pending = do
                        results <- forM pending $ \bound@(param, _, _) -> do
                            t <- maybe (return TInt) zonk (lookup param given)
                            case t of
                                TVar _ -> return (Just bound)
                                _ -> checkBound given bound t >> return Nothing
                        let left = [bound | Just bound <- results]
                        if null left
                            then return ()
                            else
                                if length left == length pending
                                    then failTc ("Type error: the type " ++ (\(param, _, _) -> param) (head left) ++ " of " ++ name ++ " cannot be worked out from its arguments")
                                    else attempt left
                attempt (tmplBounds template)
                concrete <- mapM zonk typeVars
                forM_ (zip types concrete) $ \(n, t) -> do
                    when (unknown t) $ failTc ("Type error: the type " ++ n ++ " of " ++ name ++ " cannot be worked out from its arguments")
                    when (mentionsParameter t) $
                        failTc ("Type error: the type " ++ n ++ " of " ++ name ++ " would be " ++ renderType t ++ ", which is made of a type parameter of the function that calls: a function with bounds is made for types a call writes")
                let instanceName' = name ++ "[" ++ intercalate ", " (map typeText concrete) ++ "]"
                instances <- tcInstances <$> getState
                active <- tcActive <$> getState
                unless (Map.member instanceName' instances) $ do
                    -- (a function that calls itself with a type that is not its own would be made for a new one at each depth)
                    when (name `elem` active) $
                        failTc ("Type error: " ++ name ++ " calls itself with the types " ++ intercalate ", " (map renderType concrete) ++ ", which are not those it is made for: a function with bounds is made for each type, and one that is made for a bigger type at each call would never end")
                    makeInstance instanceName' (zip types concrete)
                sizeGiven <- mapM (\(n, size) -> zonkSize size >>= sizeArgument name n) (zip sizes sizeVars)
                resultTy <- zonk result
                return (resultTy, instanceName', args, sizeGiven)
        _ -> failTc ("Type error: " ++ name ++ " is not a function")
  where
    -- the type meets the bound: it implements the trait, with the types that the bound writes
    checkBound given (param, trait, wanted) t = do
        gives <- traitArguments trait t
        case gives of
            Nothing -> failTc ("Type error: " ++ name ++ " needs " ++ param ++ " to implement " ++ trait ++ ", and " ++ renderType t ++ " does not")
            Just actual -> do
                when (length actual /= length wanted) $
                    failTc ("Type error: " ++ renderType t ++ " gives " ++ trait ++ " " ++ show (length actual) ++ " types, but the bound on " ++ param ++ " of " ++ name ++ " has " ++ show (length wanted))
                forM_ (zip actual wanted) $ \(have, want) -> do
                    have' <- zonk have
                    want' <- zonk (substitute [] given want)
                    ok <- unify have' want'
                    unless ok $ do
                        h <- zonk have'
                        w <- zonk want'
                        failTc ("Type error: " ++ name ++ " needs " ++ param ++ " to implement " ++ trait ++ "<" ++ renderType w ++ ">, and " ++ renderType t ++ " implements " ++ trait ++ "<" ++ renderType h ++ ">")
    unknown t = case t of
        TVar _ -> True
        TList u -> unknown u
        TBox u -> unknown u
        TAddr u -> unknown u
        TUninit u -> unknown u
        TBlock u -> unknown u
        TNamed n | Just (_, args) <- instanceOf n -> or [unknown u | ArgType u <- args]
        TRef u -> unknown u
        TArrayOf u _ -> unknown u
        TFn args r -> any unknown (r : args)
        _ -> False
    -- the function with the types it was called with in place of its own, which is checked like any function
    makeInstance instanceName' bindings = do
        let Signature ptys rty sizes _ = tmplSignature template
            ptys' = map (substitute [] bindings) ptys
            rty' = substitute [] bindings rty
            fnTy = functionType sizes [] ptys' rty'
            ctx = (tmplCtx template){ctxFns = Map.insert instanceName' fnTy (ctxFns (tmplCtx template))}
        s <- getState
        putState s{tcInstances = Map.insert instanceName' fnTy (tcInstances s), tcActive = name : tcActive s}
        (term', ins', outs', body') <- checkFunction ctx instanceName' (tmplParams template) ptys' rty' sizes [] (tmplRequires template) (tmplEnsures template) (tmplTermination template) (tmplBody template)
        let function = Assign instanceName' (Val (VFunct (tmplParams template) ins' outs' (NativeFunct (Signature ptys' rty' sizes []) term' body') []))
        s' <- getState
        putState s'{tcEmitted = tcEmitted s' ++ [function], tcActive = tcActive s}

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
