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
    ) where

import Control.Monad (forM, forM_, unless, when)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (intercalate, (\\))
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
    }

newtype TC a = TC (TcState -> Either String (a, TcState))

runTc :: TC a -> Either String a
runTc tc = fmap fst (runTcState tc initialTcState)

initialTcState :: TcState
initialTcState = TcState Map.empty 0 Map.empty Map.empty Nothing Map.empty Set.empty Map.empty Map.empty [] Map.empty [] [] Nothing

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
zonk (TNamed name) | Just (base, sizes) <- instanceOf name = (\sizes' -> TNamed (instanceName base sizes')) <$> mapM zonkSize sizes
zonk (TBox t) = TBox <$> zonk t
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
        (TBool, TBool) -> return True
        (TNamed x, TNamed y)
            | x == y -> return True
            -- two instances of one struct with sizes are the same type if their sizes are
            | Just (b, xs) <- instanceOf x, Just (c, ys) <- instanceOf y, b == c, length xs == length ys -> allM (uncurry unifySize) (zip xs ys)
            | otherwise -> return False
        (TVariant x, TVariant y) -> return (x == y)
        -- a value read as one variant is still a value of its enum
        -- (only one way: a Circle is a Shape, but a Shape is not a Circle)
        (TNamed t, TVariant v) -> variantOf t v
        (TVariant _, TNamed _) -> return False
        (TList x, TList y) -> unify x y
        (TArrayOf x n, TArrayOf y m) -> unifySize n m >>= \same -> if same then unify x y else return False
        (TBox x, TBox y) -> unify x y
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
        _ -> return (actual, expr)

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

-- A struct with sizes is a struct for each list of sizes (Packet<4>), which is declared the first time it is looked at
ensureInstance :: Name -> TC ()
ensureInstance name = do
    s <- getState
    unless (Map.member name (tcCtors s)) $
        case instanceOf name of
            Just (base, sizes) | Just (params, fields) <- Map.lookup base (tcGenerics s) -> do
                when (length sizes /= length params) $
                    failTc ("Type error: " ++ base ++ " has " ++ show (length params) ++ " sizes (" ++ intercalate ", " params ++ "), got " ++ show (length sizes))
                when (SizeAny `elem` sizes) $
                    failTc ("Type error: " ++ name ++ " has a size that is not given: a struct with a size of ? cannot be held yet")
                mapM_ sizeKnown sizes
                let fields' = [(f, substSizes (zip params sizes) t) | (f, t) <- fields]
                s' <- getState
                putState s'{tcTypes = Map.insert name [name] (tcTypes s'), tcCtors = Map.insert name (name, fields') (tcCtors s')}
            _ -> return ()
  where
    -- (a size can come to be an Int, as the size of a function that is given the struct, so it has to fit in one)
    sizeKnown size = case size of
        SizeParam _ -> sizeInScope size
        SizeConst c | not (inIntRange c) -> failTc ("Type error: the size " ++ show c ++ " in " ++ name ++ " is more than an Int can hold (an Int is 64 bits)")
        _ -> return ()

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
            Just (params, _) -> failTc ("Type error: " ++ name ++ " has sizes <" ++ intercalate ", " params ++ ">, which a type gives: " ++ instanceName name (map SizeParam params))
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
    -- (a Box is looked into for the base of an update as for a field)
    held <- zonk structTy >>= \t -> return (case t of TBox inner -> inner; _ -> t)
    case owner of
        Just name -> expect ("base of an update of " ++ name) (TNamed name) held
        Nothing -> return ()
    fieldType field structTy

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

-- A struct with sizes: the declaration, from which each Packet<4> is made
declareGeneric :: Name -> [Variable] -> [(Variable, Type)] -> TC ()
declareGeneric name sizes fields = do
    s <- getState
    if Map.member name (tcTypes s) || Map.member name (tcTraits s) || Map.member name (tcGenerics s)
        then failTc ("Type already defined: " ++ name)
        else do
            when (length sizes /= length (nubSizes sizes)) $ failTc ("Type error: " ++ name ++ " names a size twice")
            putState s{tcGenerics = Map.insert name (sizes, fields) (tcGenerics s)}
            -- (the fields are checked with the sizes in scope, and the struct may hold itself in a Box)
            withSizes sizes (mapM_ (checkType . snd) fields)
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
checkType (TList t) = checkType t
-- (a Box holds any type that has a size; the one place an array of no size can be is behind it)
checkType (TBox t@(TArrayOf e SizeAny)) = checkType e >> arrayOk t
checkType (TBox t) = checkType t
checkType (TArrayOf _ SizeAny) = failTc unsizedByValue
checkType ty@(TArrayOf t size) = checkType t >> sizeInScope size >> arrayOk ty
checkType (TForall _ _ t) = checkType t
checkType (TParam name) = do
    s <- getState
    unless (name `elem` tcTypeScope s) $ failTc ("Type error: " ++ name ++ " is not a type here: a function declares a type parameter, as in fn f<" ++ name ++ ">(a: " ++ name ++ ")")
checkType (TFn args ret) = mapM_ checkType (ret : map unref args)
checkType (TRef _) = failTc "Type error: & is for the parameter of a function, as in fn f(a: &List<Int>), and a type is not a reference anywhere else"
checkType _ = return ()

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
        Set -> list (\a -> TFn [TList a, TInt, a] (TList a))
        UnBox -> failTc "Type error: Box::unbox is called, as in Box::unbox(b), and cannot be used as a value"
        NewBox -> failTc "Type error: Box::new is called, as in Box::new(x), and cannot be used as a value"
        NewArray -> failTc "Type error: array needs a size that is a constant, so it is written array(3, x) and cannot be used as a value"
        ArrayFrom -> failTc "Type error: an array literal #[...] cannot be used as a value"
        NewBoxedArray -> failTc "Type error: Array::boxed is called, as in Array::boxed(n, x), and cannot be used as a value"
        Unsize -> failTc "Type error: a Box of an array is given the size of its type by the checker, and unsize cannot be used as a value"
        Plus -> arith
        Minus -> arith
        Times -> arith
        Div -> arith
        Mod -> arith
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
    | b `elem` [Size, First, Last, Get, Set] = do
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
    (envAfter, rest') <- checkStatements top ctx' env' rest
    return (envAfter, stmts' ++ rest')

-- A trait is taken apart here and an impl becomes the functions it defines (and the checks of the trait's contracts, see
-- implementation), so each statement gives back the statements that stand for it
checkItem :: Bool -> Ctx -> Env -> Statement -> TC (Ctx, Env, [Statement])
checkItem top ctx env stmt =
    case stmt of
        TraitDef name functions
            | top -> checkTrait name functions >> return (ctx, env, [])
            | otherwise -> failTc "Type error: a trait can only be defined at the top of the program"
        ImplDef trait typeName functions
            | top -> do
                (ctx', env', functions') <- checkImpl ctx env trait typeName functions
                return (ctx', env', functions')
            | otherwise -> failTc "Type error: an impl can only be written at the top of the program"
        _ -> do
            (ctx', env', stmt') <- checkStatement top ctx env stmt
            return (ctx', env', [stmt'])

-- Also gives the statement back with its termination clauses resolved
checkStatement :: Bool -> Ctx -> Env -> Statement -> TC (Ctx, Env, Statement)
checkStatement top ctx env stmt =
    case stmt of
        Assign var (Val (VFunct params ins outs (NativeFunct (Signature ptys rty sizes types) term body) proofs)) -> do
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
        StructDef name sizes fields | not (null sizes) -> declareGeneric name sizes fields >> return (ctx, env, stmt)
        StructDef name _ fields -> do
            declareType name
            mapM_ (checkType . snd) fields
            registerCtors name [(name, fields)]
            checkFinite name [fields]
            return (ctx, env, stmt)
        EnumDef name variants -> do
            -- the type is known before its fields are checked, so a variant may hold the enum itself
            declareTypeWith name (map fst variants)
            mapM_ (mapM_ (checkType . snd) . snd) variants
            registerCtors name variants
            checkFinite name (map snd variants)
            return (ctx, env, stmt)
        AxiomDef{} -> return (ctx, env, stmt)
        ProofDef{} -> return (ctx, env, stmt)
        TraitDef{} -> failTc "Type error: a trait can only be defined at the top of the program"
        ImplDef{} -> failTc "Type error: an impl can only be written at the top of the program"
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
    ty <- zonk ty'
    case ty of
        TInt -> return (Just (Counting variant'))
        TNamed _ -> return (Just (Parts variant'))
        TVariant _ -> return (Just (Parts variant'))
        TBox _ -> return (Just (Parts variant'))
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
            t <- inferProof ctx env proof
            expect "affirmed proof" TBool t
            return (env, vs)
        AssignProofVar var expr -> do
            (t, expr') <- inferExprR ctx env expr
            env' <- assignVar ctx env var t
            return (env', AssignProofVar var expr')
        Rewrite rule -> do
            case rule of
                Refl proof -> () <$ inferProof ctx env proof
                Eval var -> () <$ lookupVar ctx env var
                EvalAll -> return ()
                CheckGtZero proof -> () <$ inferProof ctx env proof
                CheckRel proof -> () <$ inferProof ctx env proof
                UserRewrite _ proofs -> mapM_ (inferProof ctx env) proofs
            return (env, vs)

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
            t <- readField owner field structTy
            return (t, F funct [struct'])
        F funct@(Val (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args -> do
            inferred0 <- mapM (inferExprR ctx env) args
            (_, declared) <- ctorInfo name
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
        -- Array::boxed(n, x): n copies of x, n known only when the program runs, in a Box that carries the size
        F (Var "Array::boxed") args -> case args of
            [n, x] -> do
                (nt, n') <- inferExprR ctx env n
                expect "argument 1 of Array::boxed" TInt nt
                (xt, x') <- inferExprR ctx env x
                let ty = TArrayOf xt SizeAny
                arrayOk ty
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
        F (Var ('.' : method)) (receiver : args) -> do
            inferred <- mapM (inferExprR ctx env) (receiver : args)
            owner <- ownerOfValue method (fst (head inferred))
            resolveAssociated owner method >>= \name -> callResolved name inferred
        -- <Type as Trait>::f, written in full
        F (Var name@('<' : _)) args -> mapM (inferExprR ctx env) args >>= callResolved name
        F (Var name) args
            | Just (path, function) <- traitPath name -> do
                s <- getState
                case (Map.lookup path (tcTraits s), Map.member path (tcTypes s)) of
                    (Just functions, _) -> do
                        inferred <- mapM (inferExprR ctx env) args
                        owner <- ownerThroughTrait path functions function (map fst inferred)
                        callResolved (implFunctionName owner (Just path) function) inferred
                    (Nothing, True) -> do
                        inferred <- mapM (inferExprR ctx env) args
                        resolveAssociated path function >>= \full -> callResolved full inferred
                    _ -> general (Var name) args
        F funct args -> general funct args
  where
    general funct args = do
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
        -- (a builtin takes what it is given: it looks through a Box itself)
        inferred <- case builtinHead ctx env funct of
            Just _ -> return inferred0
            Nothing -> coerceArguments ft inferred0
        let ats = map fst inferred
        result <- checkBuiltinCall (builtinHead ctx env funct) (describe funct) ft ats
        comparing funct ats
        return (result, F funct' (map snd inferred))
    describe (Var name) = name
    describe _ = "call"
    -- the call of a function of the program by name, with arguments that are checked already
    callResolved name inferred0 = do
        unless (Map.member name (ctxFns ctx)) $
            failTc ("Type error: " ++ name ++ " is not defined before this call (there is no such function, or its impl comes later)")
        ft <- lookupVar ctx env name
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
        TNamed name -> return name
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
            case [i | (i, TNamed "Self") <- zip [0 :: Int ..] ptys] of
                [] -> failTc ("Type error: " ++ path ++ " has no Self parameter to tell the type by: call it on the type, as in Type::" ++ function ++ "(...)")
                i : _ -> do
                    owner <- ownerOfValue path (ats !! i)
                    impls <- tcImpls <$> getState
                    unless (Set.member (trait, owner) impls) $ failTc ("Type error: " ++ owner ++ " does not implement " ++ trait)
                    return owner

-- Traits and impls

-- The functions of a trait have their types and contracts checked with Self as a type that has no constructors, so a
-- mistake in the trait is reported at the trait and not at its first impl
checkTrait :: Name -> [TraitFn] -> TC ()
checkTrait name functions = do
    s <- getState
    when (Map.member name (tcTraits s) || Map.member name (tcTypes s)) $ failTc ("Type error: " ++ name ++ " is already defined")
    putState s{tcTypes = Map.insert "Self" [] (tcTypes s)}
    forM_ functions $ \f -> do
        let Signature ptys rty _ _ = traitFnSignature f
            ctx = Ctx Map.empty (Just rty)
            paramEnv = [Map.fromList (zip (traitFnParams f) (map unref ptys))]
        mapM_ checkType (rty : map unref ptys)
        (inEnv, _) <- checkValidations ctx paramEnv (traitFnRequires f)
        _ <- checkValidations ctx (Map.insert "return" rty (head inEnv) : tail inEnv) (traitFnEnsures f)
        return ()
    s' <- getState
    putState s'{tcTypes = Map.delete "Self" (tcTypes s'), tcTraits = Map.insert name functions (tcTraits s')}

substSelf :: Name -> Type -> Type
substSelf owner (TNamed "Self") = TNamed owner
substSelf owner (TList t) = TList (substSelf owner t)
substSelf owner (TArrayOf t size) = TArrayOf (substSelf owner t) size
substSelf owner (TBox t) = TBox (substSelf owner t)
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
checkImpl :: Ctx -> Env -> Maybe Name -> Name -> [Statement] -> TC (Ctx, Env, [Statement])
checkImpl ctx env trait typeName functions = do
    _ <- typeCtors typeName
    -- (the type implements the trait from the first function on, so a function can call an earlier one through the trait; if the
    -- impl is not accepted the program is refused, so this is never seen)
    required <- case trait of
        Nothing -> return []
        Just traitName -> do
            s <- getState
            found <- maybe (failTc ("Type error: unknown trait " ++ traitName)) return (Map.lookup traitName (tcTraits s))
            when (Set.member (traitName, typeName) (tcImpls s)) $ failTc ("Type error: " ++ typeName ++ " already implements " ++ traitName)
            putState s{tcImpls = Set.insert (traitName, typeName) (tcImpls s)}
            return found
    (ctx', env', checked) <- definitions True (ctx, env, []) functions
    case trait of
        Nothing -> return (ctx', env', checked)
        Just traitName -> do
            let here = "impl " ++ traitName ++ " for " ++ typeName
                defined = [(implFunctionPart name, (Signature ptys rty sizes types, term)) | Assign name (Val (VFunct _ _ _ (NativeFunct (Signature ptys rty sizes types) term _) _)) <- checked]
                wanted = map traitFnName required
            case map fst defined \\ wanted of
                extra : _ -> failTc ("Type error: " ++ here ++ " has a function " ++ extra ++ ", which " ++ traitName ++ " does not declare")
                [] -> return ()
            case wanted \\ map fst defined of
                missing : _ -> failTc ("Type error: " ++ here ++ " lacks the function " ++ missing)
                [] -> return ()
            wrappers <- forM required $ \f -> do
                let Signature ptys rty _ _ = traitFnSignature f
                    expected = Signature (map (substSelf typeName) ptys) (substSelf typeName rty) [] []
                case lookup (traitFnName f) defined of
                    Just (actual, term) -> do
                        when (actual /= expected) $
                            failTc ("Type error: " ++ here ++ ": " ++ traitFnName f ++ " is " ++ renderSignature actual ++ ", but " ++ traitName ++ " declares " ++ renderSignature expected)
                        return (wrapper traitName typeName f expected term)
                    Nothing -> failTc ("Type error: " ++ here ++ " lacks the function " ++ traitFnName f)
            (ctx'', env'', wrapped) <- definitions False (ctx', env', []) wrappers
            return (ctx'', env'', checked ++ wrapped)
  where
    -- The functions of the impl can be called as Type::f from the next one on, itself included; the functions that check
    -- the impl against its trait cannot
    definitions _ state [] = return state
    definitions own (c, e, done) (stmt : rest) = do
        case stmt of
            Assign name (Val (VFunct _ _ _ (NativeFunct (Signature _ _ sizes types) _ _) _))
                | not (null sizes && null types) ->
                    failTc ("Type error: " ++ name ++ " has size or type parameters, which a function of an impl cannot have yet")
            _ -> return ()
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
inferProof ctx env proof =
    case proof of
        ATerm var -> lookupProofVar ctx env var
        BVar var -> lookupVar ctx env var
        CTerm value -> valueType value
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Field owner field)) _)) [struct] ->
            inferProof ctx env struct >>= readField owner field
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args ->
            mapM (inferProof ctx env) args >>= checkConstruct name fields
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct NewArray) _)) [n, x] -> do
            inferProof ctx env n >>= expect "argument 1 of array" TInt
            xt <- inferProof ctx env x
            size <- proofSize (constantProofInt n) n
            let ty = TArrayOf xt size
            arrayOk ty
            return ty
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct NewArray) _)) args -> failTc ("Type error: array takes 2 arguments, got " ++ show (length args))
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct ArrayFrom) _)) [CTerm literal@(VList items)] -> do
            listTy <- valueType literal
            case listTy of
                TList e -> do
                    let ty = TArray e (fromIntegral (length items))
                    arrayOk ty
                    literalOk e
                    return ty
                _ -> failTc "Type error: an array literal is made from a list"
        FApp funct args -> do
            ft <- inferProof ctx env funct
            ats <- mapM (inferProof ctx env) args
            result <- checkBuiltinCall (proofBuiltin funct) "call" ft ats
            comparing (proofHead funct) ats
            return result
        Forall index guards body -> do
            let env' = Map.singleton index TInt : env
            mapM_ (\g -> inferProof ctx env' g >>= expect "guard of forall" TBool) guards
            inferProof ctx env' body >>= expect "body of forall" TBool
            return TBool

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
            _ -> return ()
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
        TRef u -> usesParam u
        TArrayOf u _ -> usesParam u
        TFn args ret -> any usesParam (ret : args)
        _ -> False

hasFunction :: Type -> Bool
hasFunction ty = case ty of
    TFn{} -> True
    TList t -> hasFunction t
    TBox t -> hasFunction t
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
                given <- mapM (\(n, size) -> zonkSize size >>= sizeArgument n) (zip names sizes)
                -- (a type parameter is a type of value: not a function, which native code has no copy of the function for)
                forM_ (zip types given') $ \(n, t) -> do
                    t' <- zonk t
                    when (hasFunction t') $ failTc ("Type error: the type " ++ n ++ " of " ++ name ++ " would be " ++ renderType t' ++ ", and a type parameter is not a function")
                    -- (a function that calls itself with a type made of its own, as f(push([], a), n - 1), would need a copy for each depth)
                    current <- tcCurrent <$> getState
                    scope <- tcTypeScope <$> getState
                    when (current == Just name && isExpanding scope t') $
                        failTc ("Type error: " ++ name ++ " calls itself with the type " ++ renderType t' ++ " for " ++ n ++ ", which is made of its own type parameters: a call of itself gives each type parameter as it is, or a type that does not use them, since a copy of the function is made for each type and would be needed for each depth")
                result <- zonk rty
                return (result, args ++ given)
        _ -> failTc ("Type error: " ++ name ++ " is not a function")
  where
    sizeArgument n size = case size of
        SizeConst c -> return (Val (VInt c))
        SizeParam p -> return (Var p)
        _ -> failTc ("Type error: the size " ++ n ++ " of " ++ name ++ " cannot be worked out from its arguments: an argument has to be an array of that size")

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
