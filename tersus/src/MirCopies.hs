{-# LANGUAGE PatternSynonyms #-}

module MirCopies
    ( makeCopies
    , copyName
    , boundCallParts
    ) where

import Data.List (intercalate, isPrefixOf, stripPrefix)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import qualified Data.Set as Set

import BuiltinRegistry (methodBuiltinByName)
import Mir
import MirPacks (Expanded (..), expandPack, isPackName)
import Pretty (renderType)
import StdLib (builtinFunct)
import Syntax (Expression (..), Proof (..), RwRule (..), Termination (..), ValidationStatement (..), Value (..), VariableProof)
import qualified Types as T
import Types (Arg (..), BuiltinFunct, Name, Rel (..), Size (..), Type (..), Variable, instanceName, pattern TBox, pattern TList, renderTypeForName, substitute, tupleGeneric, baseNameOf)
import Utils (Result (..))

-- The copy step (MIR.md, "Copies of functions with bounds"). A function with bounds is checked once against its bounds,
-- lowered once with its type parameters, and checked for moves once; the program names each copy it calls (`f[Int]`,
-- an Instance record, progInstances). This makes each copy the program reaches from the generic MIR, by substitution:
-- the types and the sizes its bounds name are put in, the references of the body are made the copies they name, and a
-- call through a bound (`<$param T as Tr>::g`) is made what a copy calls for the type (resolveBound). The functions with
-- bounds are then dropped, so nothing after this step sees a type parameter that a bound was on.

-- A copy: the function with bounds, its type arguments and the values of the sizes its bounds name
type Key = (Name, [Type], [Integer])

-- The name of a copy that no reference wrote (one made for a copy, from a body with type parameters)
copyName :: Name -> [Type] -> [Integer] -> Name
copyName f tys sizes = f ++ "[" ++ intercalate ", " (map renderTypeForName tys ++ map show sizes) ++ "]"

-- `<$param T as Tr>::g` as the parameter, the trait and the function
boundCallParts :: Name -> Maybe (Variable, Name, Name)
boundCallParts name = do
    rest <- stripPrefix "<$param " name
    let (p, afterP) = breakOn " as " rest
    afterAs <- stripPrefix " as " afterP
    let (trait, afterTrait) = breakOn ">::" afterAs
    function <- stripPrefix ">::" afterTrait
    if null p || null trait || null function then Nothing else Just (p, trait, function)
  where
    breakOn pat text = go "" text
      where
        go acc rest
            | pat `isPrefixOf` rest = (reverse acc, rest)
            | otherwise = case rest of
                c : more -> go (c : acc) more
                [] -> (reverse acc, [])

makeCopies :: Program -> Result Program String
makeCopies program
    | Map.null (progBounded program) && Map.null (progInstances program) = Ok program
    | otherwise = case run of
        Left e -> Error e
        Right (rootsDone, mainDone, made) -> Ok (finish program rootsDone mainDone made)
  where
    generics = progBounded program
    lifted = Set.fromList (concatMap boundedLifted (Map.elems generics))
    named = Map.fromList [(key, name) | (name, (f, args)) <- Map.toList (progInstances program), Just key <- [concreteKey program f args]]
    roots = [fn | fn <- Map.elems (progFunctions program), fnName fn `Map.notMember` generics, fnName fn `Set.notMember` lifted]
    rootCx = Cx program named [] [] Map.empty "" [] Map.empty Map.empty Map.empty Map.empty
    run = do
        (rootsDone, needs1) <- transformAll rootCx roots
        (mainDone, needs2) <- transformAll rootCx [progMain program]
        made <- build program named (needs1 ++ needs2) Map.empty []
        Right (rootsDone, head mainDone, reverse made)

-- What a body is copied with: the program, the names references wrote, the type and bounded size arguments, the lifted
-- functions' copies, the name of the copy (for messages) and the copies being made around it, with their bigness
data Cx = Cx
    { cxProgram :: Program
    , cxNamed :: Map Key Name
    , cxTypes :: [(Variable, Type)]
    , cxSizes :: [(Variable, Integer)]
    , cxLifted :: Map Name Name
    , cxCopy :: Name
    , cxChain :: [(Name, Int)]
    , cxRenames :: Map Name Name -- the struct instances the function being copied names (`Pair<'T>`), with the copy's types put in
    , cxGeneric :: Map Local LocalDecl -- the locals of the function being copied, with their types as it has them
    , cxBlockTypes :: Map BlockId [(Variable, Type)] -- in a copy of a variadic function, the element types each block binds besides cxTypes
    , cxLocalTypes :: Map Local [(Variable, Type)] -- and each local
    }

-- A queued copy and the copies around it (its chain, for the growth refusal)
type Need = (Key, [(Name, Int)])

transformAll :: Cx -> [Function] -> Either String ([Function], [Need])
transformAll cx fns = do
    results <- mapM (transformFunction cx) fns
    Right (map fst results, concatMap snd results)

-- The copies made, in the order they were made: each with the function with bounds it is a copy of, and its lifted copies
type Made = (Name, Function, [Function])

build :: Program -> Map Key Name -> [Need] -> Map Key Name -> [Made] -> Either String [Made]
build _ _ [] _ made = Right made
build program named ((key@(f, tys, sizes), chain) : rest) done made
    | Map.member key done = build program named rest done made
    | otherwise = case (Map.lookup f (progFunctions program), Map.lookup f (progBounded program)) of
        (Just generic, Just bounded) -> do
            let name = nameOf named key
                bigness = sum (map typeBigness tys)
            case [() | (g, b) <- chain, g == f, b <= bigness] of
                _ : _ -> Left ("Type error: " ++ f ++ " calls itself with the types " ++ intercalate ", " (map renderType tys) ++ ", which are not those it is made for: a function with bounds is made for each type, and one that is made for a bigger type at each call would never end")
                [] -> Right ()
            let packs = filter isPackName (fnTypeParams generic)
                fixed = filter (not . isPackName) (fnTypeParams generic)
                arityOk = if null packs then length tys == length (fnTypeParams generic) else length tys >= length fixed
            if not arityOk || length sizes /= length (boundedSizes bounded)
                then Left ("internal compiler error: " ++ name ++ " gives " ++ f ++ " " ++ show (length tys) ++ " types and " ++ show (length sizes) ++ " sizes, and it has " ++ show (length (fnTypeParams generic)) ++ " and " ++ show (length (boundedSizes bounded)))
                else Right ()
            -- (a variadic function is expanded for the number of its arguments first: MirPacks)
            (body, blockTypes, localTypes, typeArgs) <- case packs of
                [pack] -> do
                    let elements = drop (length fixed) tys
                        bind indexes = [(v, elements !! fromInteger k) | (v, k) <- Map.toList indexes, k >= 0, k < toInteger (length elements)]
                    Expanded expanded blockIndexes localIndexes <- expandPack bounded pack (toInteger (length elements)) generic
                    Right (expanded, Map.map bind blockIndexes, Map.map bind localIndexes, zip fixed tys ++ [(pack ++ "#" ++ show k, t) | (k, t) <- zip [0 :: Int ..] elements])
                _ -> Right (generic, Map.empty, Map.empty, zip (fnTypeParams generic) tys)
            let liftedNames = Map.fromList [(l, name ++ drop (length f) l) | l <- boundedLifted bounded]
                cx = Cx program named typeArgs (zip (boundedSizes bounded) sizes) liftedNames name (chain ++ [(f, bigness)]) Map.empty Map.empty blockTypes localTypes
            (copy, needs) <- transformFunction cx body
            liftedCopies <- mapM (\l -> maybe (Left ("internal compiler error: " ++ f ++ " lifts " ++ l ++ ", which the program does not have")) (transformFunction cx) (Map.lookup l (progFunctions program))) (boundedLifted bounded)
            frameRefusal program f name body copy
            mapM_ (\(g, c) -> frameRefusal program f name g c) (zip [g | l <- boundedLifted bounded, Just g <- [Map.lookup l (progFunctions program)]] (map fst liftedCopies))
            -- (the check of an impl function against its trait is made with each copy of it, as the trait's contract is
            -- met by each copy)
            let companion = [((c, tys, sizes), chain ++ [(f, bigness)]) | Just c <- [companionOf f], Map.member c (progBounded program)]
            build program named (rest ++ needs ++ concatMap snd liftedCopies ++ companion) (Map.insert key name done) ((f, copy, map fst liftedCopies) : made)
        _ -> Left ("internal compiler error: the copy " ++ nameOf named key ++ " is of " ++ f ++ ", which is not a function with bounds of the program")

nameOf :: Map Key Name -> Key -> Name
nameOf named key@(f, tys, sizes) = Map.findWithDefault (copyName f tys sizes) key named

-- `Tr for O::g`, the check of the impl function `<O as Tr>::g` against its trait
companionOf :: Name -> Maybe Name
companionOf name = do
    rest <- stripPrefix "<" name
    let (owner, afterOwner) = span (/= ' ') rest
    afterAs <- stripPrefix " as " afterOwner
    let (trait, afterTrait) = span (/= '>') afterAs
    function <- stripPrefix ">::" afterTrait
    if null owner || null trait || null function || '<' `elem` owner then Nothing else Just (trait ++ " for " ++ owner ++ "::" ++ function)

-- The key of a reference whose arguments are all known
concreteKey :: Program -> Name -> [Arg] -> Maybe Key
concreteKey _ f args =
    let tys = [t | ArgType t <- args]
        sizes = [s | ArgSize s <- args]
     in if any mentionsParam tys then Nothing else (\cs -> (f, tys, cs)) <$> mapM constantSize sizes
  where
    constantSize s = case s of
        SizeConst c -> Just c
        _ -> Nothing

mentionsParam :: Type -> Bool
mentionsParam ty = case ty of
    TParam _ -> True
    TList t -> mentionsParam t
    TBox t -> mentionsParam t
    TAddr t -> mentionsParam t
    TBlock t -> mentionsParam t
    TUninit t -> mentionsParam t
    TRef t -> mentionsParam t
    TMutRef t -> mentionsParam t
    TArrayOf t _ -> mentionsParam t
    TFn args ret -> any mentionsParam (ret : args)
    TNamed _ args -> or [mentionsParam t | ArgType t <- args]
    TForall _ _ t -> mentionsParam t
    _ -> False

-- How big a type is, for the growth refusal
typeBigness :: Type -> Int
typeBigness ty = case ty of
    TArrayOf t _ -> 1 + typeBigness t
    TAddr t -> 1 + typeBigness t
    TBlock t -> 1 + typeBigness t
    TUninit t -> 1 + typeBigness t
    TRef t -> 1 + typeBigness t
    TMutRef t -> 1 + typeBigness t
    TNamed _ args -> 1 + sum [typeBigness t | ArgType t <- args]
    TFn args ret -> 1 + sum (map typeBigness (args ++ [ret]))
    _ -> 1

-- An array held in a frame that a copy makes too big (the definition could not say, as its type had a parameter)
frameRefusal :: Program -> Name -> Name -> Function -> Function -> Either String ()
frameRefusal program f name generic copy =
    case [ (ty, words')
         | (l, LocalDecl ty _) <- Map.toList (fnLocals copy)
         , Just (LocalDecl gty _) <- [Map.lookup l (fnLocals generic)]
         , gty /= ty
         , TArrayOf _ (SizeConst _) <- [ty]
         , let words' = typeWords withCopy ty
         , words' > 8192
         ] of
        (ty, n) : _ -> Left ("Type error: " ++ f ++ " cannot be made as " ++ name ++ " for this call: " ++ renderType ty ++ " takes " ++ show n ++ " words, more than the 8192 that an array held in a frame can have")
        [] -> Right ()
  where
    -- (with the structs the copy names declared)
    withCopy = completeInstances program{progFunctions = Map.singleton (fnName copy) copy}

-- The words of a value held inline, as the elaborator counts them for an array of a type it knows (its typeWords): a
-- word, an address and a reference one, a Box of an array of no size two, an array of a size that many of its element,
-- a struct (a list and a Box are structs) the words of its fields, and an enum its tag and its widest variant
typeWords :: Program -> Type -> Integer
typeWords program ty = case ty of
    TNamed "Box" [ArgType (TArrayOf _ SizeAny)] -> 2
    TArrayOf t (SizeConst n) -> n * typeWords program t
    TNamed base args -> declared (instanceName base args)
    TVariant v | Just owner <- ownerOf program v -> declared owner
    _ -> 1
  where
    declared name = case Map.lookup name (progTypes program) of
        Just (StructDecl fields) -> sum [typeWords program t | (_, t) <- fields]
        Just (EnumDecl variants) -> 1 + maximum (0 : [sum [typeWords program t | (_, t) <- fields] | (_, fields) <- variants])
        Nothing -> 1

-- The state of the copying of one function: the copies it needs and the locals it adds
data CS = CS {csNeeds :: [Need], csNext :: Int, csLocals :: [(Local, LocalDecl)], csNextBlock :: Int}

newtype C a = C {runC :: CS -> Either String (a, CS)}

instance Functor C where
    fmap f (C g) = C (\s -> fmap (\(a, s') -> (f a, s')) (g s))

instance Applicative C where
    pure a = C (\s -> Right (a, s))
    C f <*> C g = C (\s -> case f s of
        Left e -> Left e
        Right (h, s') -> fmap (\(a, s'') -> (h a, s'')) (g s'))

instance Monad C where
    C g >>= f = C (\s -> case g s of
        Left e -> Left e
        Right (a, s') -> runC (f a) s')

failC :: String -> C a
failC e = C (\_ -> Left e)

need :: Need -> C ()
need n = C (\s -> Right ((), s{csNeeds = n : csNeeds s}))

newBlock :: C BlockId
newBlock = C (\s -> Right (BlockId (csNextBlock s), s{csNextBlock = csNextBlock s + 1}))

newTemp :: Type -> C Local
newTemp ty = C (\s -> let l = Local (csNext s) in Right (l, s{csNext = csNext s + 1, csLocals = (l, LocalDecl ty Nothing) : csLocals s}))

-- What a reference of the body stands for in the copy: a function (with the size arguments the call adds for its size
-- parameters), or what a call is in a copy when it is not a call
data Target = Named Name [Operand] | Inline Inline

-- A copy of the value (the language's Clone of a word, a tuple, or a type with no Clone impl), a comparison of words, or a
-- builtin
data Inline = InlineCopy | InlineEq | InlineBuiltin BuiltinFunct ListOp

transformFunction :: Cx -> Function -> Either String (Function, [Need])
transformFunction cx0 fn = do
    -- (a function lifted out of the body has the copy's types and bounded sizes, but not those its own parameters hide)
    let lifted = Map.member (fnName fn) (cxLifted cx0)
        cx1 = if lifted then cx0{cxTypes = [(n, t) | (n, t) <- cxTypes cx0, n `notElem` fnTypeParams fn], cxSizes = [(n, c) | (n, c) <- cxSizes cx0, n `notElem` fnSizeParams fn], cxBlockTypes = Map.empty, cxLocalTypes = Map.empty} else cx0
        cx = cx1{cxRenames = renamesOf cx1 fn, cxGeneric = fnLocals fn}
        types = typeIn cx
        localType' l d = case Map.lookup l (cxLocalTypes cx) of
            Just extra | not (null extra) -> typeIn cx{cxTypes = extra ++ cxTypes cx} (localType d)
            _ -> types (localType d)
        locals = Map.mapWithKey (\l d -> d{localType = localType' l d}) (fnLocals fn)
        sizeLocals = drop (length (fnParams fn) - length (fnSizeParams fn)) (fnParams fn)
        constants = Map.fromList [(l, c) | (l, n) <- zip sizeLocals (fnSizeParams fn), Just c <- [lookup n (cxSizes cx)]]
        start = CS [] (1 + maximum (0 : [i | Local i <- Map.keys locals])) [] (1 + maximum (0 : [i | BlockId i <- Map.keys (fnBlocks fn)]))
        fn0 = fn{fnLocals = locals, fnReturns = fmap types (fnReturns fn)}
    (fn', st) <- runC (transformBody cx constants fn0) start
    let name = if null (cxCopy cx) then fnName fn else Map.findWithDefault (cxCopy cx) (fnName fn) (cxLifted cx)
    Right
        ( fn'
            { fnName = name
            , fnTypeParams = if null (cxCopy cx) then fnTypeParams fn else [p | p <- fnTypeParams fn, p `notElem` map fst (cxTypes cx)]
            , fnLocals = Map.union (fnLocals fn') (Map.fromList (csLocals st))
            }
        , reverse (csNeeds st)
        )

typeIn :: Cx -> Type -> Type
typeIn cx
    | null (cxTypes cx) && null (cxSizes cx) = id
    | otherwise = substitute [(n, SizeConst c) | (n, c) <- cxSizes cx] (cxTypes cx)

transformBody :: Cx -> Map Local Integer -> Function -> C Function
transformBody cx constants fn = do
    blocks <- mapM (\(b, block) -> transformBlock (blockCx cx fn b) constants fn b block) (Map.toList (fnBlocks fn))
    spec' <- transformSpec cx constants fn (fnSpec fn)
    return fn{fnBlocks = mergeInlined (fnSpec fn) (concat blocks), fnSpec = spec'}

-- A block that ended in a call the copy made statements goes on into the block the call returned to, as a builtin's
-- statements in the body of a function made for its types do, when nothing else enters that block and it does not start
-- a loop or an iteration (the validator reads a loop's test in the block its loop starts at)
mergeInlined :: FunctionSpec -> [(BlockId, BasicBlock, Bool)] -> Map BlockId BasicBlock
mergeInlined spec blocks = go (Map.fromList [(b, (block, inlined)) | (b, block, inlined) <- blocks])
  where
    kept = Map.keysSet (specLoops spec) `Set.union` Set.fromList (map loopBody (Map.elems (specLoops spec)))
    go m = case [(b, n) | (b, (BasicBlock _ (Goto n), True)) <- Map.toList m, n /= b, Set.notMember n kept, entries m n == 1, Map.member n m] of
        [] -> Map.map fst m
        (b, n) : _ ->
            let (BasicBlock stmts _, _) = m Map.! b
                (BasicBlock stmts' term', inlined') = m Map.! n
             in go (Map.insert b (BasicBlock (stmts ++ stmts') term', inlined') (Map.delete n m))
    entries m n = length [() | (BasicBlock _ t, _) <- Map.elems m, s <- successors t, s == n] + (if n == BlockId 0 then 1 else 0)

-- The context of a block of a copy: in a copy of a variadic function, with the element types the block binds (an iteration
-- of an unrolled loop binds its element's)
blockCx :: Cx -> Function -> BlockId -> Cx
blockCx cx fn b = case Map.lookup b (cxBlockTypes cx) of
    Just extra | not (null extra) -> let cx' = cx{cxTypes = extra ++ cxTypes cx} in cx'{cxRenames = renamesOf cx' fn{fnLocals = cxGeneric cx}}
    _ -> cx

transformSpec :: Cx -> Map Local Integer -> Function -> FunctionSpec -> C FunctionSpec
transformSpec cx constants fn spec = do
    requires <- mapM (validation cx) (specRequires spec)
    ensures <- mapM (validation cx) (specEnsures spec)
    term <- mapM (termination cx) (specTermination spec)
    loops <- Map.traverseWithKey (\h l -> let cxl = blockCx cx fn h in (\inv t -> l{loopInvariant = inv, loopTermination = t, loopEnv = env cxl constants (loopEnv l)}) <$> mapM (validation cxl) (loopInvariant l) <*> mapM (termination cxl) (loopTermination l)) (specLoops spec)
    return spec{specRequires = requires, specEnsures = ensures, specTermination = term, specLoops = loops, specEnv = env cx constants (specEnv spec)}

-- (an environment names every function of the program; a reference's copy is named again when its arguments are known,
-- and is in the program when something made it, finish keeping only the functions that are)
env :: Cx -> Map Local Integer -> Env -> Env
env cx constants = Map.mapMaybe entry
  where
    entry o = case o of
        Const (CFn n)
            | Just l <- Map.lookup n (cxLifted cx) -> Just (Const (CFn l))
            | Just _ <- boundCallParts n -> Nothing
            | Just (f, args) <- Map.lookup n (progInstances (cxProgram cx)) -> case concreteKey (cxProgram cx) f (map (argIn cx) args) of
                Just key -> Just (Const (CFn (nameOf (cxNamed cx) key)))
                Nothing -> Nothing
        _ -> Just (operandWith constants o)

operandWith :: Map Local Integer -> Operand -> Operand
operandWith constants o = case o of
    Copy l | Just c <- Map.lookup l constants -> Const (CInt c)
    Move l | Just c <- Map.lookup l constants -> Const (CInt c)
    _ -> o

argIn :: Cx -> Arg -> Arg
argIn cx arg = case arg of
    ArgType t -> ArgType (typeIn cx t)
    ArgSize (SizeParam n) | Just c <- lookup n (cxSizes cx) -> ArgSize (SizeConst c)
    _ -> arg

-- The function a name the body uses stands for in the copy, with the copy it needs made
target :: Cx -> Map Local Integer -> Function -> Name -> [Operand] -> Maybe Local -> C Target
target cx constants fn name args dest
    | Just l <- Map.lookup name (cxLifted cx) = return (Named l [])
    | Just (p, trait, function) <- boundCallParts name = case lookup p (cxTypes cx) of
        Just t -> resolveBound cx constants fn (Map.lookup name (progInstances (cxProgram cx)) == Just (libraryBuiltin, [])) trait function t args dest
        Nothing -> failC ("internal compiler error: " ++ name ++ " is a call through a bound of " ++ p ++ ", which " ++ shown ++ " has no type for")
    | Just (f, args0) <- Map.lookup name (progInstances (cxProgram cx)) = case concreteKey (cxProgram cx) f (map (argIn cx) args0) of
        Just key -> (\n -> Named n []) <$> copyNamed cx key
        Nothing -> failC ("Type error: the size in a bound of " ++ f ++ " cannot be worked out from its arguments, in " ++ shown)
    | otherwise = return (Named name [])
  where
    shown = if null (cxCopy cx) then fnName fn else cxCopy cx

-- The Instance record that marks a function a bound gives as one of the library's Sequence or Growable, which a list, an
-- array and a Box of an array implement with the builtins (the elaborator's sequenceTraits)
libraryBuiltin :: Name
libraryBuiltin = "$builtin"

-- The name of the copy for the key, which is made
copyNamed :: Cx -> Key -> C Name
copyNamed cx key = do
    need (key, cxChain cx)
    return (nameOf (cxNamed cx) key)

-- A call through a bound with the type the copy gives the parameter (MIR.md, the copy step): Clone is the clone the type
-- has (cloneTarget), word Eq is a comparison, a sequence function of the library's traits on a list, an array or a Box of
-- an array is the builtin, anything else is the function of the type's impl of the trait (a copy of it when it has
-- bounds), and a sequence function no impl gives is the builtin (a list, an array and a Box of an array implement a
-- Sequence or Growable of the program's own by being one)
resolveBound :: Cx -> Map Local Integer -> Function -> Bool -> Name -> Name -> Type -> [Operand] -> Maybe Local -> C Target
resolveBound cx constants fn library trait function t args dest
    | trait == "Clone", function == "clone" = traitClone cx constants fn t args dest
    | trait == "Eq", function == "eq", word t = return (Inline InlineEq)
    | trait == "Eq", function == "eq", Just e <- unsizedBoxed t, Map.member "eqBoxedArrays" (progBounded (cxProgram cx)) = (\n -> Named n []) <$> withBoundsCopy cx "eqBoxedArrays" [e]
    | library, Just builtin <- sequenceBuiltin = return builtin
    | Just owner <- ownerOfType (cxProgram cx) t, let callee = implName owner, Map.member callee (progFunctions (cxProgram cx)) = calling cx constants fn (Just t) callee args dest
    | Just builtin <- sequenceBuiltin, trait `elem` ["Sequence", "Growable"] = return builtin
    | otherwise = failC ("internal compiler error: " ++ trait ++ "::" ++ function ++ " is called on a " ++ renderType t ++ " in " ++ cxCopy cx ++ ", which has no impl of it")
  where
    implName owner = "<" ++ owner ++ " as " ++ trait ++ ">::" ++ function
    sequenceBuiltin = case (methodBuiltinByName function, sequenceLike t) of
        (Just b, True) | Just op <- listOpOf b -> Just (Inline (InlineBuiltin b op))
        _ -> Nothing
    word ty = case unref ty of
        TInt -> True
        TByte -> True
        TBool -> True
        TWord _ _ -> True
        TAddr _ -> True
        _ -> False
    sequenceLike ty = case unref ty of
        TList _ -> True
        TArrayOf _ _ -> True
        TBox (TArrayOf _ _) -> True
        _ -> False

-- The clone of a value of a type, as the elaborator writes clone(x) and x.clone() for a type it knows (cloneCall): a word,
-- an address, a function and a reference are copied as they are, whatever impls of a trait named Clone the program has,
-- and any other type is cloned as Clone::clone is (traitClone)
cloneTarget :: Cx -> Map Local Integer -> Function -> Type -> [Operand] -> Maybe Local -> C Target
cloneTarget cx constants fn t args dest
    | ownCopy (unref t) = return (Inline InlineCopy)
    | otherwise = traitClone cx constants fn t args dest

-- Clone::clone of a value of a type: a Box of an array of no size is cloned by the library's cloneBoxedArray when the
-- program has it, a tuple is copied as it is, and any other type by its impl of Clone when it has one
traitClone :: Cx -> Map Local Integer -> Function -> Type -> [Operand] -> Maybe Local -> C Target
traitClone cx constants fn t args dest = case unref t of
    ty | Just e <- unsizedBoxed ty, Map.member "cloneBoxedArray" (progBounded (cxProgram cx)) -> (\n -> Named n []) <$> withBoundsCopy cx "cloneBoxedArray" [e]
    TNamed base _ | Just _ <- tupleGeneric base -> return (Inline InlineCopy)
    ty -> case ownerOfType (cxProgram cx) ty of
        Just owner | let callee = "<" ++ owner ++ " as Clone>::clone", Map.member callee (progFunctions (cxProgram cx)) -> calling cx constants fn (Just t) callee args dest
        _ -> return (Inline InlineCopy)

ownCopy :: Type -> Bool
ownCopy ty = case ty of
    TInt -> True
    TByte -> True
    TBool -> True
    TWord _ _ -> True
    TAddr _ -> True
    TFn _ _ -> True
    TRef _ -> True
    TMutRef _ -> True
    _ -> False

-- A call of a function of the program from a copy: of the copy of it for the types the call gives, when it has bounds, and
-- with the sizes the call gives its size parameters, which the arguments' types decide
calling :: Cx -> Map Local Integer -> Function -> Maybe Type -> Name -> [Operand] -> Maybe Local -> C Target
calling cx constants fn self callee args dest = case Map.lookup callee (progFunctions program) of
    Nothing -> failC ("internal compiler error: " ++ callee ++ ", which a copy of " ++ cxCopy cx ++ " calls, is not a function of the program")
    Just generic -> do
        -- (from the operands and the destination, and, where a proof names the function and gives neither, from the type
        -- the bound is for, which a parameter or the result of the impl's function of the type's own kind is)
        let paramTypes = [p | param <- fnParams generic, Just p <- [localType <$> Map.lookup param (fnLocals generic)]]
            pairs = [(p, a) | (p, arg) <- zip paramTypes args, Just a <- [operandType arg]] ++ [(r, d) | Just r <- [fnReturns generic], Just l <- [dest], Just d <- [localType <$> Map.lookup l (fnLocals fn)]] ++ [(p, ty) | Just ty <- [self], p <- paramTypes ++ maybe [] pure (fnReturns generic), sameOwner p ty]
            types = concat [matchTy p a | (p, a) <- pairs]
            sizes = concat [matchSizes p a | (p, a) <- pairs]
            missing what v = failC ("internal compiler error: the " ++ what ++ " " ++ v ++ " of " ++ callee ++ " is not known from a call of it in " ++ cxCopy cx)
        extras <- mapM (\s -> maybe (missing "size" s) (sizeOperand s) (lookup s sizes)) (fnSizeParams generic)
        case Map.lookup callee (progBounded program) of
            Just bounded -> do
                tys <- mapM (\v -> maybe (missing "type" v) return (lookup v types)) (fnTypeParams generic)
                bsizes <- mapM (\s -> case lookup s sizes of Just (SizeConst c) -> return c; _ -> missing "size" s) (boundedSizes bounded)
                (\n -> Named n extras) <$> copyNamed cx (callee, tys, bsizes)
            Nothing -> return (Named callee extras)
  where
    program = cxProgram cx
    sameOwner p ty = case (unref p, unref ty) of
        (TNamed a _, TNamed b _) -> a == b
        (TArrayOf _ _, TArrayOf _ _) -> True
        _ -> False
    operandType o = case o of
        Copy l -> localType <$> Map.lookup l (fnLocals fn)
        Move l -> localType <$> Map.lookup l (fnLocals fn)
        _ -> Nothing
    -- (a size the copy knows is a constant; one of its own size parameters is the parameter, which its caller gives)
    sizeOperand s size = case size of
        SizeConst c -> return (Const (CInt c))
        SizeParam q | Just l <- lookup q (zip (fnSizeParams fn) (drop (length (fnParams fn) - length (fnSizeParams fn)) (fnParams fn))) -> return (operandWith constants (Copy l))
        _ -> failC ("internal compiler error: the size " ++ s ++ " of " ++ callee ++ " is not known in " ++ cxCopy cx)

withBoundsCopy :: Cx -> Name -> [Type] -> C Name
withBoundsCopy cx f tys
    | Map.member f (progBounded (cxProgram cx)) = copyNamed cx (f, tys, [])
    | otherwise = failC ("internal compiler error: " ++ f ++ ", which a copy of " ++ cxCopy cx ++ " calls, is not a function with bounds of the program")

-- The type whose impls a function of a value of the type is of (the elaborator's traitOwner)
ownerOfType :: Program -> Type -> Maybe Name
ownerOfType program ty = case unref ty of
    TArrayOf _ _ -> Just "Array"
    TBox _ -> Just "Box"
    TList _ -> Just "List"
    TNamed base _ -> Just base
    TVariant v -> ownerOf program v
    TInt -> Just "Int"
    TByte -> Just "Byte"
    TBool -> Just "Bool"
    _ -> Nothing

unref :: Type -> Type
unref ty = case ty of
    TRef t -> t
    TMutRef t -> t
    _ -> ty

unsizedBoxed :: Type -> Maybe Type
unsizedBoxed ty = case unref ty of
    TBox (TArrayOf e SizeAny) -> Just e
    _ -> Nothing

listOpOf :: BuiltinFunct -> Maybe ListOp
listOpOf b = lookup b [(T.Size, Length), (T.Get, Get), (T.Set, Set), (T.Push, Push), (T.Pop, Pop), (T.First, First), (T.Last, Last)]

-- What the type parameters of a type are, given the type it stands for (MirMono's match)
matchTy :: Type -> Type -> [(Variable, Type)]
matchTy pat actual = case (pat, actual) of
    (TParam name, a) -> [(name, a)]
    (TRef p, a) -> matchTy p a
    (p, TRef a) -> matchTy p a
    (TMutRef p, a) -> matchTy p a
    (p, TMutRef a) -> matchTy p a
    (TAddr p, TAddr a) -> matchTy p a
    (TUninit p, TUninit a) -> matchTy p a
    (TBlock p, TBlock a) -> matchTy p a
    (TArrayOf p _, TArrayOf a _) -> matchTy p a
    (TNamed bp ps, TNamed ba as)
        | bp == ba, length ps == length as -> concat [matchTy p a | (ArgType p, ArgType a) <- zip ps as]
    (TFn ps p, TFn as a) -> concat (zipWith matchTy (p : ps) (a : as))
    _ -> []

-- What the size parameters of a type are, given the type it stands for
matchSizes :: Type -> Type -> [(Variable, Size)]
matchSizes pat actual = case (pat, actual) of
    (TRef p, a) -> matchSizes p a
    (p, TRef a) -> matchSizes p a
    (TMutRef p, a) -> matchSizes p a
    (p, TMutRef a) -> matchSizes p a
    (TAddr p, TAddr a) -> matchSizes p a
    (TUninit p, TUninit a) -> matchSizes p a
    (TBlock p, TBlock a) -> matchSizes p a
    (TArrayOf p sp, TArrayOf a sa) -> bind sp sa ++ matchSizes p a
    (TNamed bp ps, TNamed ba as)
        | bp == ba, length ps == length as -> concat [case (x, y) of (ArgType p, ArgType a) -> matchSizes p a; (ArgSize sp, ArgSize sa) -> bind sp sa; _ -> [] | (x, y) <- zip ps as]
    _ -> []
  where
    bind (SizeParam s) sa = [(s, sa)]
    bind _ _ = []

-- A block of the body in the copy: a call through a bound that is not a call there is the statements it is (and the
-- block goes on into the block the call returned to, mergeInlined), and a clone of a value of a type parameter in a
-- function lifted out of the body that is a call there ends the block in it (the rest of the block is a block of its own)
transformBlock :: Cx -> Map Local Integer -> Function -> BlockId -> BasicBlock -> C [(BlockId, BasicBlock, Bool)]
transformBlock cx constants fn here (BasicBlock stmts term) = go here [] stmts []
  where
    go b acc0 [] done = do
        (acc, term0) <- materialized acc0 term
        (extra, term') <- terminator term0
        let inlinedCall = case (term, term') of
                (Call{}, Goto _) -> True
                _ -> False
        return (reverse ((b, BasicBlock (reverse acc ++ extra) term', inlinedCall) : done))
    go b acc (s : rest) done = case s of
        Assign dest (CopyOf o) | not (null (cxCopy cx)), Just ty <- genericType o, mentionsParam ty -> do
            let o' = operandWith constants o
            t <- cloneTarget cx constants fn (typeIn cx ty) [o'] (Just dest)
            case t of
                Named callee extras -> do
                    next <- newBlock
                    o'' <- op o'
                    (lend, input) <- cloneInput (reverse acc) o''
                    let acc' = if null lend then acc else unread acc o''
                    go next [] rest ((b, BasicBlock (reverse acc' ++ lend) (Call (Const (CFn callee)) (input : extras) dest next), False) : done)
                _ -> do
                    s' <- statement s
                    go b (s' : acc) rest done
        _ -> do
            s' <- statement s
            go b (s' : acc) rest done
    -- (a clone through the bound given a borrow of a place is given the value there when the type copies it as it is (a
    -- word, a tuple, a type with no Clone impl) or when it is an array a Box holds, as the elaborator writes
    -- the clone of a value of a type it knows, cloneCall and cloneInput)
    materialized acc term0 = case term0 of
        Call (Const (CFn name)) [Copy r] dest next
            | Just (p, "Clone", "clone") <- boundCallParts name
            , Just t <- lookup p (cxTypes cx)
            , (later, Assign _ (Borrow root steps _) : earlier) <- break (borrows r) acc
            , Just rootTy <- localType <$> Map.lookup root (fnLocals fn)
            , byValue t || (null steps && boxedValue rootTy) -> do
                read <- placeRead root rootTy steps
                case read of
                    Just (stmts, value) -> return (later ++ reverse stmts ++ earlier, Call (Const (CFn name)) [value] dest next)
                    Nothing -> return (acc, term0)
        _ -> return (acc, term0)
    borrows r s = case s of
        Assign d (Borrow _ _ _) -> d == r
        _ -> False
    boxedValue ty = case ty of
        TNamed "Box" [ArgType (TArrayOf _ _)] -> True
        _ -> False
    byValue t = case unref t of
        ty | Just _ <- unsizedBoxed ty -> False
        TNamed base _ | Just _ <- tupleGeneric base -> True
        ty -> case ownerOfType (cxProgram cx) ty of
            Just owner -> Map.notMember ("<" ++ owner ++ " as Clone>::clone") (progFunctions (cxProgram cx))
            Nothing -> True
    -- (the value at a place, read: what a Box holds, a field, an element)
    placeRead root rootTy steps = case (rootTy, steps) of
        (TRef _, _) -> return Nothing
        (TMutRef _, _) -> return Nothing
        (TNamed "Box" [ArgType payload], []) -> do
            tmp <- newTemp payload
            return (Just ([Assign tmp (Unbox (Copy root))], Copy tmp))
        (_, []) -> return (Just ([], Copy root))
        _ -> walk (Copy root) rootTy steps []
    walk cur _ [] acc' = return (Just (acc', cur))
    walk cur ty (st : rest) acc' = case st of
        RefIndex i | Just e <- elementOf ty -> do
            tmp <- newTemp e
            walk (Copy tmp) e rest (acc' ++ [Assign tmp (ListOp Get [cur, i])])
        RefField owner f | Just ft <- fieldOf owner f -> do
            tmp <- newTemp ft
            walk (Copy tmp) ft rest (acc' ++ [Assign tmp (ReadField cur owner f)])
        _ -> return Nothing
    elementOf ty = case ty of
        TList e -> Just e
        TArrayOf e _ -> Just e
        TNamed "Box" [ArgType (TArrayOf e _)] -> Just e
        _ -> Nothing
    fieldOf owner f = case Map.lookup owner (progTypes (cxProgram cx)) of
        Just (StructDecl fields) -> lookup f fields
        _ -> Nothing
    -- (the clone of a value read from a place is given a borrow of the place, as the elaborator writes the clone of a value
    -- of a type it knows, cloneInput: a place through a Box gives the value read, and so does a Box whose value is an
    -- array)
    cloneInput before o = case o of
        Copy l | Just (root, steps, boxed) <- placeOf before l, not (null steps) || boxed, Just ty <- localType <$> Map.lookup l (fnLocals fn) -> case (steps, boxed) of
            ([], True) | lentPayload ty -> lend root [] ty
            (_ : _, False) -> lend root steps ty
            _ -> return ([], o)
        _ -> return ([], o)
    lend root steps ty = do
        r <- newTemp (TRef ty)
        return ([Assign r (Borrow root steps False)], Copy r)
    lentPayload ty = case ty of
        TArrayOf _ _ -> False
        _ -> True
    -- (a temporary that only the clone read, now given a borrow of its place, is not read: nor are the temporaries only it
    -- was read from)
    unread acc o = case o of
        Copy l | temporary l, uses l <= 1, (later, def : earlier) <- break (defines l) acc ->
            foldl unread (later ++ earlier) [x | x <- definedFrom def]
        _ -> acc
    temporary l = maybe False (\d -> localName d == Nothing) (Map.lookup l (fnLocals fn))
    defines l s = case s of
        Assign d _ -> d == l
        Peek d _ -> d == l
        _ -> False
    definedFrom s = case s of
        Assign _ rv -> rvalueOperands rv
        Peek _ rv -> rvalueOperands rv
        _ -> []
    uses l = length [() | BasicBlock stmts t <- Map.elems (fnBlocks fn), o <- concatMap statementOperands stmts ++ terminatorOperands t, readsLocal l o]
    readsLocal l o = case o of
        Copy x -> x == l
        Move x -> x == l
        _ -> False
    statementOperands s = case s of
        Assign _ rv -> rvalueOperands rv ++ borrowRoots rv
        Peek _ rv -> rvalueOperands rv ++ borrowRoots rv
        AssignRef root _ rv -> Copy root : rvalueOperands rv
        _ -> []
    borrowRoots rv = case rv of
        Borrow root _ _ -> [Copy root]
        TakeField root _ _ -> [Copy root]
        _ -> []
    terminatorOperands t = case t of
        SwitchBool o _ _ -> [o]
        Call callee args _ _ -> callee : args
        _ -> []
    -- (the place a local of the block was read from: its root, the steps to it and whether it is what a Box holds)
    placeOf before l = case [rv | s <- reverse before, Just (d, rv) <- [assigned s], d == l] of
        rv : _ -> case rv of
            Unbox (Copy x) | Just (root, [], False) <- placeOf before x -> Just (root, [], True)
            ReadField (Copy x) owner f | Just (root, steps, False) <- placeOf before x -> Just (root, steps ++ [RefField owner f], False)
            ListOp Get [Copy x, i] | stable i, Just (root, steps, False) <- placeOf before x -> Just (root, steps ++ [RefIndex i], False)
            _ -> Nothing
        [] -> Just (l, [], False)
    assigned s = case s of
        Assign d rv -> Just (d, rv)
        Peek d rv -> Just (d, rv)
        _ -> Nothing
    stable i = case i of
        Const _ -> True
        _ -> False
    genericType o = case o of
        Copy l -> localType <$> Map.lookup l (cxGeneric cx)
        Move l -> localType <$> Map.lookup l (cxGeneric cx)
        _ -> Nothing
    terminator t = case t of
        Call (Const (CFn name)) args dest next -> do
            let args' = map (operandWith constants) args
            resolved <- target cx constants fn name args' (Just dest)
            case resolved of
                Named callee extras -> do
                    args'' <- mapM (operand cx constants fn) args'
                    return ([], Call (Const (CFn callee)) (args'' ++ extras) dest next)
                Inline inline -> do
                    (extra, rv) <- inlined inline args'
                    return (extra ++ [Assign dest rv], Goto next)
        Call callee args dest next -> do
            callee' <- operand cx constants fn callee
            args' <- mapM op args
            return ([], Call callee' args' dest next)
        SwitchBool o yes no -> (\o' -> ([], SwitchBool o' yes no)) <$> op o
        _ -> return ([], t)
    statement s = case s of
        Assign l rv -> Assign l <$> rvalue rv
        Peek l rv -> Peek l <$> rvalue rv
        AssignRef root steps rv -> AssignRef root <$> mapM step steps <*> rvalue rv
        Ghost e g -> Ghost (env cx constants e) <$> ghost g
        Drop _ -> return s
    ghost g = case g of
        GhostValidation v -> GhostValidation <$> validation cx v
        GhostAxiom n ps ins outs -> GhostAxiom n ps <$> mapM (validation cx) ins <*> mapM (validation cx) outs
        GhostProof n ps ins outs body -> GhostProof n ps <$> mapM (validation cx) ins <*> mapM (validation cx) outs <*> mapM (validation cx) body
        GhostFunction n source top | Just l <- Map.lookup n (cxLifted cx) -> return (GhostFunction l source top)
        _ -> return g
    step st = case st of
        RefField n f -> return (RefField (typeNameIn cx n) f)
        RefIndex o -> RefIndex <$> op o
    op = operand cx constants fn . operandWith constants
    rvalue rv = case rv of
        Use o -> Use <$> op o
        BinaryOp b x y -> BinaryOp b <$> op x <*> op y
        ListOp l os -> ListOp l <$> mapM op os
        MakeList os -> MakeList <$> mapM op os
        MakeBox o -> MakeBox <$> op o
        Unbox o -> Unbox <$> op o
        Unsize o -> Unsize <$> op o
        MakeData n fields -> MakeData (typeNameIn cx n) <$> mapM (\(f, o) -> (,) f <$> op o) fields
        ReadField o n f -> (\o' -> ReadField o' (typeNameIn cx n) f) <$> op o
        IsVariant o n -> (\o' -> IsVariant o' (typeNameIn cx n)) <$> op o
        AsVariant o n -> (\o' -> AsVariant o' (typeNameIn cx n)) <$> op o
        CopyOf o -> CopyOf <$> op o
        TakeField l n f -> return (TakeField l (typeNameIn cx n) f)
        Borrow root steps m -> (\steps' -> Borrow root steps' m) <$> mapM step steps
        Deref o -> Deref <$> op o
    -- (a reference argument is read where it is to: the copy of a value, a comparison and a builtin take values)
    plain o = case o of
        Copy l | Just ty <- localType <$> Map.lookup l (fnLocals fn), isRef ty -> deref l (unref ty)
        Move l | Just ty <- localType <$> Map.lookup l (fnLocals fn), isRef ty -> deref l (unref ty)
        _ -> return ([], o)
    deref l ty = do
        tmp <- newTemp ty
        return ([Assign tmp (Deref (Copy l))], Copy tmp)
    isRef ty = case ty of
        TRef _ -> True
        TMutRef _ -> True
        _ -> False
    inlined inline args = case (inline, args) of
        (InlineCopy, [a]) -> do
            (extra, a') <- plain a
            return (extra, CopyOf a')
        (InlineEq, [a, b]) -> do
            (ea, a') <- plain a
            (eb, b') <- plain b
            return (ea ++ eb, BinaryOp (Compare Eq) a' b')
        (InlineBuiltin _ l, _) -> do
            parts <- mapM plain args
            return (concatMap fst parts, ListOp l (map snd parts))
        _ -> failC ("internal compiler error: a call through a bound in " ++ cxCopy cx ++ " has " ++ show (length args) ++ " arguments")

rvalueOperands :: Rvalue -> [Operand]
rvalueOperands rv = case rv of
    Use o -> [o]
    BinaryOp _ a b -> [a, b]
    ListOp _ os -> os
    MakeList os -> os
    MakeBox o -> [o]
    Unbox o -> [o]
    Unsize o -> [o]
    MakeData _ fields -> map snd fields
    ReadField o _ _ -> [o]
    IsVariant o _ -> [o]
    AsVariant o _ -> [o]
    CopyOf o -> [o]
    TakeField{} -> []
    Borrow _ steps _ -> [o | RefIndex o <- steps]
    Deref o -> [o]

-- The name of a struct instance a body writes (`Pair<'T>`), with the copy's types put in
typeNameIn :: Cx -> Name -> Name
typeNameIn cx name = Map.findWithDefault name name (cxRenames cx)

renamesOf :: Cx -> Function -> Map Name Name
renamesOf cx fn
    | null (cxTypes cx) && null (cxSizes cx) = Map.empty
    | otherwise = Map.fromList [(renderNamed b a, case typeIn cx (TNamed b a) of TNamed b' a' -> renderNamed b' a'; _ -> renderNamed b a) | ty <- [localType d | d <- Map.elems (fnLocals fn)] ++ maybe [] pure (fnReturns fn), (b, a) <- namedSubs ty]
  where
    renderNamed = instanceName
    namedSubs ty = case ty of
        TNamed b a -> (b, a) : concat [namedSubs u | ArgType u <- a]
        TArrayOf u _ -> namedSubs u
        TAddr u -> namedSubs u
        TBlock u -> namedSubs u
        TUninit u -> namedSubs u
        TRef u -> namedSubs u
        TMutRef u -> namedSubs u
        TFn as r -> concatMap namedSubs (r : as)
        _ -> []

operand :: Cx -> Map Local Integer -> Function -> Operand -> C Operand
operand cx constants fn o = case o of
    Const c -> Const <$> constant c
    _ -> return (operandWith constants o)
  where
    constant c = case c of
        CFn n -> target cx constants fn n [] Nothing >>= \t -> case t of
            Named n' _ -> return (CFn n')
            Inline _ -> failC ("internal compiler error: " ++ n ++ " is used as a value in " ++ cxCopy cx ++ ", and it is not a function there")
        CData n fields -> CData (typeNameIn cx n) <$> mapM (\(f, v) -> (,) f <$> constant v) fields
        CList cs -> CList <$> mapM constant cs
        CArray cs -> CArray <$> mapM constant cs
        _ -> return c

validation :: Cx -> ValidationStatement -> C ValidationStatement
validation cx v = case v of
    ProofAssert p -> ProofAssert <$> proof cx p
    Assume p -> Assume <$> proof cx p
    AssignProofVar n e -> AssignProofVar n <$> expression cx e
    Rewrite rule -> Rewrite <$> case rule of
        Refl p -> Refl <$> proof cx p
        CheckGtZero p -> CheckGtZero <$> proof cx p
        CheckRel p -> CheckRel <$> proof cx p
        UserRewrite n ps -> UserRewrite n <$> mapM (proof cx) ps
        _ -> return rule

-- A proof names a copy and a function a bound gives as a term; a library sequence function of a list, an array or a Box
-- of an array is the builtin's term, as a proof writes it for one
proof :: Cx -> VariableProof -> C VariableProof
proof cx p = case p of
    ATerm n -> nameTerm n
    FApp f args -> FApp <$> proof cx f <*> mapM (proof cx) args
    Forall n guards body -> Forall n <$> mapM (proof cx) guards <*> proof cx body
    _ -> return p
  where
    nameTerm n = proofName cx n >>= \r -> return (either ATerm (CTerm . builtinFunct) r)

proofName :: Cx -> Name -> C (Either Name BuiltinFunct)
proofName cx n
    | Map.member n (progInstances (cxProgram cx)) || Map.member n (cxLifted cx) || isBound = do
        t <- target cx Map.empty noFunction n [] Nothing
        case t of
            Named n' _ -> return (Left n')
            Inline (InlineBuiltin b _) -> return (Right b)
            Inline _ -> failC ("internal compiler error: " ++ n ++ " is in a proof in " ++ cxCopy cx ++ ", which has no proof form for the type it is copied for")
    | otherwise = return (Left n)
  where
    isBound = maybe False (const True) (boundCallParts n)
    noFunction = Function "" [] Nothing Map.empty Map.empty [] [] [] [] [] emptySpec

termination :: Cx -> Termination -> C Termination
termination cx t = case t of
    Shrinks e -> Shrinks <$> expression cx e
    Counting e -> Counting <$> expression cx e
    Parts e -> Parts <$> expression cx e
    Recursing inner -> Recursing <$> mapM (termination cx) inner
    MayDiverge -> return MayDiverge

expression :: Cx -> Expression -> C Expression
expression cx e = case e of
    Var n -> proofName cx n >>= \r -> return (either Var (Val . builtinFunct) r)
    F f args -> F <$> expression cx f <*> mapM (expression cx) args
    Val (VFnRef n) -> proofName cx n >>= \r -> return (either (Val . VFnRef) (Val . builtinFunct) r)
    _ -> return e

-- The program with the copies in place of the functions with bounds: each marker of a function with bounds is the
-- markers of its copies, environments name the functions there are, and the tables are empty
finish :: Program -> [Function] -> Function -> [Made] -> Program
finish program roots main' made =
    completeInstances
        program
            { progTypes = Map.filterWithKey (\name _ -> not (derived name)) (progTypes program)
            , progFunctions = Map.map completeEnvs functions
            , progMain = completeEnvs (replaceMarkers main')
            , progBounded = Map.empty
            , progInstances = Map.empty
            }
  where
    -- (the instances of the structs with parameters are declared again for the functions there are: those that only the
    -- functions with bounds named go with them)
    derived name =
        let base = baseNameOf name
         in base /= name && maybe False (const True) (maybe (tupleGeneric base) Just (Map.lookup base (progGenerics program)))
    functions = Map.fromList [(fnName f, f) | f <- roots ++ concat [copy : liftedCopies | (_, copy, liftedCopies) <- made]]
    names = Set.insert (fnName main') (Map.keysSet functions)
    copyEnv = Map.fromList [(n, Const (CFn n)) | (_, copy, liftedCopies) <- made, n <- map fnName (copy : liftedCopies)]
    -- (an environment keeps the functions there are: a name a unit gave a copy or a bound, which another unit's lowering
    -- does not have, is not one)
    scrub = Map.filterWithKey (\k o -> Map.notMember k (progInstances program) && case o of Const (CFn n) -> n `Set.member` names; _ -> True)
    -- (the markers of the functions with bounds go, and each copy is defined where the program starts, wherever the
    -- function it is of was defined: a program linked from units and the same program lowered whole have the same copies)
    copyNames = Set.toAscList (Set.fromList [fnName copy | (_, copy, _) <- made])
    replaceMarkers fn = fn{fnBlocks = Map.mapWithKey (\b (BasicBlock stmts term) -> BasicBlock ([Ghost markerEnv (GhostFunction n n True) | b == BlockId 0, n <- copyNames] ++ filter (not . boundedMarker) stmts) term) (fnBlocks fn)}
    markerEnv = Map.fromList [(n, Const (CFn n)) | n <- Map.keys functions]
    boundedMarker s = case s of
        Ghost _ (GhostFunction n _ _) -> Map.member n (progBounded program)
        _ -> False
    completeEnvs fn = fn{fnSpec = completeSpec (fnSpec fn), fnBlocks = Map.map completeBlock (fnBlocks fn)}
      where
        completeBlock (BasicBlock stmts term) = BasicBlock (map completeStatement stmts) term
        completeStatement (Ghost e g) = Ghost (complete e) g
        completeStatement other = other
        completeSpec spec = spec{specEnv = complete (specEnv spec), specLoops = Map.map (\loop -> loop{loopEnv = complete (loopEnv loop)}) (specLoops spec)}
        complete e = Map.union (scrub e) copyEnv
