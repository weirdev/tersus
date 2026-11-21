{-# LANGUAGE PatternSynonyms #-}

module MirCopies
    ( makeCopies
    , makeCopiesWith
    , copyName
    , isCopyName
    , opaqueKey
    , boundCallParts
    , genericKey
    , coveredKey
    , isStubName
    , withoutGeneric
    , contractSuffix
    ) where

import Data.Char (isDigit)
import Data.Containers.ListUtils (nubOrd)
import Data.List (intercalate, isPrefixOf, stripPrefix)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (isJust)
import qualified Data.Set as Set

import BuiltinRegistry (methodBuiltinByName)
import Mir
import MirPacks (Expanded (..), expandPack, isPackName)
import Pretty (renderType)
import StdLib (builtinFunct)
import Syntax (Expression (..), FunctBody (..), Proof (..), RwRule (..), Termination (..), ValidationStatement (..), Value (..), VariableProof, exprToProof, parseImplCheckName)
import qualified Types as T
import Types (Arg (..), BuiltinFunct, Name, Rel (..), Size (..), Type (..), Variable, instanceName, pattern TBox, pattern TList, renderTypeForName, substitute, tupleGeneric, baseNameOf)
import Utils (Result (..))

-- The copy step (MIR.md, "Copies of functions with bounds"). A function with bounds is checked once against its bounds,
-- lowered once with its type parameters, and checked for moves once; the program names each copy it calls (`f[Int]`,
-- an Instance record, progInstances). This makes each copy the program reaches from the generic MIR, by substitution:
-- the types and the sizes its bounds name are put in, the references of the body are made the copies they name, and a
-- call through a bound (`<$param T as Tr>::g`) is made what a copy calls for the type (resolveBound): the check function of
-- the type's impl (`Tr for O::g`), which has the trait's contracts, or what the language gives. The functions with
-- bounds are then dropped, so nothing after this step sees a type parameter that a bound was on.

-- A copy: the function with bounds, its type arguments and the values of the sizes its bounds name
type Key = (Name, [Type], [Integer])

-- The name of a copy that no reference wrote (one made for a copy, from a body with type parameters)
copyName :: Name -> [Type] -> [Integer] -> Name
copyName f tys sizes = f ++ "[" ++ intercalate ", " (map renderTypeForName tys ++ map show sizes) ++ "]"

-- The entry of a copy's environment that marks a local opaque to its proofs (no program writes a name with `$`)
opaqueKey :: Local -> Name
opaqueKey (Local n) = "$opaque " ++ show n

-- Whether a function is a copy of a function with bounds (or lifted out of one), by the naming scheme copyName and the
-- elaborator's Instance names share (no name a program writes has a `[`), and not the check function of an impl
isCopyName :: Name -> Bool
isCopyName name = '[' `elem` name && parseImplCheckName name == Nothing

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
makeCopies = makeCopiesWith Set.empty

-- With the functions with bounds of the compiler's libraries, which are validated generically only where the program
-- uses them (every other function with bounds is, where it is defined)
makeCopiesWith :: Set.Set Name -> Program -> Result Program String
makeCopiesWith library program
    | Map.null (progBounded program) && Map.null (progInstances program) = Ok program
    | otherwise = case run of
        Left e -> Error e
        Right (rootsDone, mainDone, made, used) -> Ok (divergingCopies (finish program named used rootsDone mainDone made))
  where
    generics = progBounded program
    lifted = Set.fromList (concatMap boundedLifted (Map.elems generics))
    named = Map.fromList [(key, name) | (name, (f, args)) <- Map.toList (progInstances program), Just key <- [concreteKey program f args]]
    roots = [fn | fn <- Map.elems (progFunctions program), fnName fn `Map.notMember` generics, fnName fn `Set.notMember` lifted]
    rootCx = Cx program named [] [] Map.empty "" [] Map.empty Map.empty Map.empty Map.empty
    -- (a function with bounds is validated generically where it is defined, and one of the libraries where the program uses it:
    -- a copy of it is made, or a body validated generically names it generically; such a body names the copies its concrete
    -- references are. The library's justification of the builtins a copy runs for a Box of an array of a size is one where a
    -- copy has such a Box.)
    always = Set.fromList [f | f <- Map.keys generics, not (isStubName f), Set.notMember f library]
    -- (a copy with a Box of an array of a size may run the builtins for it, resolveBound)
    sizedBoxedUsed made = Set.fromList [f | any (any (sizedBoxed . localType) . Map.elems . fnLocals) [copy | (_, copy, _) <- made], f <- sizedBoxedJustification, Map.member f generics]
    sizedBoxed t = case t of
        TBox (TArrayOf _ size) -> size /= SizeAny
        TRef inner -> sizedBoxed inner
        TMutRef inner -> sizedBoxed inner
        _ -> False
    instanceRefs f = [(g, args) | fn <- bodyAndLifted f, n <- usedNames fn, Nothing <- [boundCallParts n], Just (g, args) <- [Map.lookup n (progInstances program)], Map.member g generics, not (isStubName g)]
    bodyAndLifted f = [fn | n <- f : maybe [] boundedLifted (Map.lookup f generics), Just fn <- [Map.lookup n (progFunctions program)]]
    genericNeeds used = [((g, tys, sizes), []) | f <- Set.toList used, (g, args) <- instanceRefs f, Just (_, tys, sizes) <- [concreteKey program g args]]
    usedClosure used =
        let more = Set.fromList [g | f <- Set.toList used, (g, args) <- instanceRefs f, Nothing <- [concreteKey program g args]]
         in if more `Set.isSubsetOf` used then used else usedClosure (Set.union used more)
    run = do
        (rootsDone, needs1) <- transformAll rootCx roots
        (mainDone, needs2) <- transformAll rootCx [progMain program]
        let grow used = do
                made <- build program named (needs1 ++ needs2 ++ genericNeeds used) Map.empty []
                let used' = usedClosure (Set.unions [always, sizedBoxedUsed made, Set.fromList [g | (g, _, _) <- made]])
                if used' == used then Right (made, used) else grow used'
        (made, used) <- grow (usedClosure always)
        Right (rootsDone, head mainDone, reverse made, used)

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
            (body, blockTypes, localTypes, typeArgs, spreadInstances) <- case packs of
                [pack] -> do
                    let elements = drop (length fixed) tys
                        bind indexes = [(v, elements !! fromInteger k) | (v, k) <- Map.toList indexes, k >= 0, k < toInteger (length elements)]
                    Expanded expanded blockIndexes localIndexes spreads <- expandPack bounded pack (toInteger (length elements)) generic
                    -- (a forwarding call names the reference it spreads with the pack in place of the elements: the spread
                    -- names them, so the callee's copy is named by their types)
                    spreadInstances <- mapM (spreadInstance pack program) (Map.toList spreads)
                    Right (expanded, Map.map bind blockIndexes, Map.map bind localIndexes, zip fixed tys ++ [(pack ++ "#" ++ show k, t) | (k, t) <- zip [0 :: Int ..] elements], Map.fromList spreadInstances)
                _ -> Right (generic, Map.empty, Map.empty, zip (fnTypeParams generic) tys, Map.empty)
            let liftedNames = Map.fromList [(l, name ++ drop (length f) l) | l <- boundedLifted bounded]
                program' = program{progInstances = Map.union spreadInstances (progInstances program)}
                cx = Cx program' named typeArgs (zip (boundedSizes bounded) sizes) liftedNames name (chain ++ [(f, bigness)]) Map.empty Map.empty blockTypes localTypes
            (copy, needs) <- transformFunction cx body
            liftedCopies <- mapM (\l -> maybe (Left ("internal compiler error: " ++ f ++ " lifts " ++ l ++ ", which the program does not have")) (transformFunction cx) (Map.lookup l (progFunctions program))) (boundedLifted bounded)
            frameRefusal program f name body copy
            mapM_ (\(g, c) -> frameRefusal program f name g c) (zip [g | l <- boundedLifted bounded, Just g <- [Map.lookup l (progFunctions program)]] (map fst liftedCopies))
            -- (the check of an impl function against its trait is made with each copy of it, as the trait's contract is
            -- met by each copy)
            let companion = [((c, tys, sizes), chain ++ [(f, bigness)]) | Just c <- [companionOf f], Map.member c (progBounded program)]
            build program named (rest ++ needs ++ concatMap snd liftedCopies ++ companion) (Map.insert key name done) ((f, copy, map fst liftedCopies) : made)
        _ -> Left ("internal compiler error: the copy " ++ nameOf named key ++ " is of " ++ f ++ ", which is not a function with bounds of the program")

-- The reference a spread names: the forwarded reference's arguments with the elements from lo to hi - 1 in place of the pack
spreadInstance :: Name -> Program -> (Name, (Name, Integer, Integer)) -> Either String (Name, (Name, [Arg]))
spreadInstance pack program (spread, (g, lo, hi)) = case Map.lookup g (progInstances program) of
    Just (f, args) -> Right (spread, (f, concatMap element args))
    Nothing -> Left ("internal compiler error: a call forwards a pack to " ++ g ++ ", which names no copy")
  where
    element a = case a of
        ArgType (TParam p) | p == pack -> [ArgType (TParam (pack ++ "#" ++ show k)) | k <- [lo .. hi - 1]]
        _ -> [a]

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
        -- (a value whose type in the body is a type parameter the copy fills is opaque to the copy's proofs: it knows of it
        -- what the bounds promise, not what its type is, so copies that differ only in such types prove the same; the facts a
        -- type gives reach into a part of it only through a reference or a Box (SelfHostedMir.typeSteps), so a value that
        -- holds one there is opaque too)
        filled ty = case ty of
            TParam p -> types (TParam p) /= TParam p
            TRef inner -> filled inner
            TMutRef inner -> filled inner
            TBox inner -> filled inner
            _ -> False
        opaque = if null (cxCopy cx) then [] else [l | (l, d) <- Map.toList (fnLocals fn), filled (localType d)]
        spec'' = (fnSpec fn'){specEnv = Map.union (Map.fromList [(opaqueKey l, Copy l) | l <- opaque]) (specEnv (fnSpec fn'))}
    Right
        ( fn'
            { fnName = name
            , fnSpec = spec''
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
    | library, Just builtin <- sequenceBuiltin, sizedBoxedArray t = return builtin
    | Just owner <- ownerOfType (cxProgram cx) t, let callee = implName owner, Map.member callee (progFunctions (cxProgram cx)) = checkOrSize callee >>= \check -> calling cx constants fn (Just t) check args dest
    | Just builtin <- sequenceBuiltin, trait `elem` ["Sequence", "Growable"] = return builtin
    | otherwise = failC ("internal compiler error: " ++ trait ++ "::" ++ function ++ " is called on a " ++ renderType t ++ " in " ++ cxCopy cx ++ ", which has no impl of it")
  where
    implName owner = "<" ++ owner ++ " as " ++ trait ++ ">::" ++ function
    -- (the library's size and get of a list, an array and a Box of an array stay their impls', which are the builtins: the
    -- trait's contracts of those impls are written with the builtin size and get, so a copy relates what it knows of a call
    -- of set or push through the trait to what it knows of size and get)
    checkOrSize callee
        | library, function `elem` ["size", "get"], sequenceType t = return callee
        | otherwise = checkOf cx callee
    -- (the prelude's impl for a Box of an array is for one of no size: a Box of an array of a size has no impl, and its
    -- sequence functions are the builtins, which give a copy more than the trait promises)
    sizedBoxedArray ty = case unref ty of
        TBox (TArrayOf _ size) -> size /= SizeAny
        _ -> False
    sequenceBuiltin = case (methodBuiltinByName function, sequenceType t) of
        (Just b, True) | Just op <- listOpOf b -> Just (Inline (InlineBuiltin b op))
        _ -> Nothing
    word ty = case unref ty of
        TInt -> True
        TByte -> True
        TBool -> True
        TWord _ _ -> True
        TAddr _ -> True
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
        Just owner | let callee = "<" ++ owner ++ " as Clone>::clone", Map.member callee (progFunctions (cxProgram cx)) -> checkOf cx callee >>= \check -> calling cx constants fn (Just t) check args dest
        _ -> return (Inline InlineCopy)

-- The check function of an impl's function, `Tr for O::g`, which a copy calls through a bound: it has the trait's contracts,
-- so a copy knows of the call what the bound promises and nothing the impl promises more (the validator takes it as the
-- impl's function, SelfHostedMir.validatorSymbol)
checkOf :: Cx -> Name -> C Name
checkOf cx callee = case companionOf callee of
    Just check | Map.member check (progFunctions (cxProgram cx)) -> return check
    _ -> failC ("internal compiler error: " ++ callee ++ " has no check function, which a call through a bound in " ++ cxCopy cx ++ " calls")

sequenceType :: Type -> Bool
sequenceType ty = case unref ty of
    TList _ -> True
    TArrayOf _ _ -> True
    TBox (TArrayOf _ _) -> True
    _ -> False

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

-- A proof names a copy and a function a bound gives as a term; the library's size and get of a list, an array or a Box of
-- an array are the builtins' terms, which their impls promise to be (a caller's proof of a copy's contract needs no
-- second-level facts to relate them)
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
    | Just (p, _, function) <- boundCallParts n
    , function `elem` ["size", "get"]
    , Map.lookup n (progInstances (cxProgram cx)) == Just (libraryBuiltin, [])
    , Just t <- lookup p (cxTypes cx)
    , sequenceType t
    , Just b <- methodBuiltinByName function = return (Right b)
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

-- The program with the copies in place of the functions with bounds, and the functions with bounds themselves beside
-- them, generic, which the validator checks once (`$generic`) in place of their copies (`$covered`): the copies are for
-- native code and for what their callers prove of them. A call through a bound in a generic body is a call of the trait's
-- stub (`Tr for $Self::g`, which the elaborator writes for each function of each trait), and a reference to a copy for
-- types that are not known is a reference to the generic callee. Environments name the functions there are, and the
-- tables are empty.
-- A body with bounds is validated once, and a call through a bound promises to end there; a copy is not validated again, and
-- in it the call is the impl's function, which may be `~`. Such a copy may not end either, so it is marked `~`, and so is every
-- copy that calls one, and the validator refuses a caller that has to end.
divergingCopies :: Program -> Program
divergingCopies program = program{progFunctions = Map.map mark functions}
  where
    functions = progFunctions program
    diverges f = specTermination (fnSpec f) == Just MayDiverge
    callees f = [n | BasicBlock _ (Call (Const (CFn n)) _ _ _) <- Map.elems (fnBlocks f)]
    diverging = grow (Map.keysSet (Map.filter diverges functions))
    grow known =
        let more = Map.keysSet (Map.filter (\f -> isCopyName (fnName f) && fnName f `Set.notMember` known && any (`Set.member` known) (callees f)) functions)
         in if Set.null more then known else grow (Set.union known more)
    mark f
        | isCopyName (fnName f) && not (diverges f) && fnName f `Set.member` diverging = f{fnSpec = (fnSpec f){specTermination = Just MayDiverge}}
        | otherwise = f

finish :: Program -> Map Key Name -> Set.Set Name -> [Function] -> Function -> [Made] -> Program
finish program named used roots main' made =
    completeInstances
        program
            { progTypes = Map.filterWithKey (\name _ -> not (derived name)) (progTypes program)
            , progFunctions = Map.map checkContracts (Map.union (Map.map completeEnvs functions) (Map.map completeGeneric generic))
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
    functions = Map.fromList [(fnName f, covered f) | f <- roots ++ concat [copy : liftedCopies | (_, copy, liftedCopies) <- made]]
    names = Set.unions [Set.singleton (fnName main'), Map.keysSet functions, Map.keysSet generic]
    copyEnv = Map.fromList [(n, Const (CFn n)) | n <- Set.toList names, n /= fnName main']
    -- (an environment keeps the functions there are: a name a unit gave a copy or a bound, which another unit's lowering
    -- does not have, is not one)
    scrub = Map.filterWithKey (\k o -> Map.notMember k (progInstances program) && case o of Const (CFn n) -> n `Set.member` names; _ -> True)
    -- (the markers of the functions with bounds that are not kept go, and each copy is defined where the program starts,
    -- wherever the function it is of was defined: a program linked from units and the same program lowered whole have the
    -- same copies)
    -- (the generic bodies' markers go first with the copies', as a library prefix and a whole program put their definitions
    -- in different places among the program's statements)
    copyNames = Set.toAscList (Set.fromList ([fnName copy | (_, copy, _) <- made] ++ [n | n <- Map.keys generic, Map.member n (progBounded program) || Map.notMember n (progFunctions program)]))
    replaceMarkers fn = fn{fnBlocks = Map.mapWithKey (\b (BasicBlock stmts term) -> BasicBlock ([Ghost markerEnv (GhostFunction n n True) | b == BlockId 0, n <- copyNames] ++ filter (not . boundedMarker) stmts) term) (fnBlocks fn)}
    markerEnv = Map.fromList [(n, Const (CFn n)) | n <- Map.keys functions ++ Map.keys generic]
    boundedMarker s = case s of
        Ghost _ (GhostFunction n _ _) -> Map.member n (progBounded program)
        _ -> False
    -- (the contracts of a check function name the check functions of the same impl, as the trait's contracts name the trait's
    -- functions: a copy that calls one proves what it asks of what it knows of the others)
    checkContracts fn = case parseImplCheckName (fnName fn) of
        Just (_, owner, _) | not (isStubName (fnName fn)) -> fn{fnSpec = (fnSpec fn){specEnv = Map.map (toCheck owner) (specEnv (fnSpec fn))}}
        _ -> fn
    toCheck owner o = case o of
        Const (CFn n) | Just c <- companionOf n, Just (_, owner', _) <- parseImplCheckName c, owner' == owner, c `Set.member` names -> Const (CFn c)
        _ -> o
    completeEnvs fn = mapEnvs (\e -> Map.union (scrub e) copyEnv) fn
    -- The functions with bounds validated generically, with the functions lifted out of them (but those that name what has no
    -- generic form: a call through a bound of a trait with no stub); and the stubs, which are not validated
    bounded = progBounded program
    variadic f = maybe False (any isPackName . fnTypeParams) (Map.lookup f (progFunctions program))
    lifted = Set.fromList (concatMap boundedLifted (Map.elems bounded))
    kept = keep (Set.fromList [f | f <- Set.toList used, Map.member f bounded, not (isStubName f), Set.notMember f lifted, Map.member f (progFunctions program)])
    keep cs =
        let bad = Set.fromList [f | f <- Set.toList cs, any (refusedRef cs) (concatMap usedNames (bodyAndLifted f))]
         in if Set.null bad then cs else keep (cs `Set.difference` bad)
    refusedRef cs n
        | Just (_, trait, function) <- boundCallParts n = Map.notMember (stubName trait function) (progFunctions program)
        | otherwise = case Map.lookup n (progInstances program) of
            Just (g, args) | Nothing <- concreteKey program g args -> not (isStubName g) && Set.notMember g cs && Map.member g bounded
            _ -> False
    bodyAndLifted f = [fn | n <- f : maybe [] boundedLifted (Map.lookup f bounded), Just fn <- [Map.lookup n (progFunctions program)]]
    stubs = [f | f <- Map.keys bounded, isStubName f, Map.member f (progFunctions program)]
    bodies = [g | f <- Set.toList kept, g <- genericOf f]
    stubFns = Map.fromList [(f, renameFunction rename fn) | f <- stubs, Just fn <- [Map.lookup f (progFunctions program)]]
    -- (only the stubs the generic bodies call or name, and those the contracts of those name)
    stubsUsed = grow (Set.fromList [n | g <- bodies, n <- usedNames g, Map.member n stubFns])
      where
        grow s = let s' = Set.union s (Set.fromList [n | f <- Set.toList s, Just fn <- [Map.lookup f stubFns], n <- usedNames fn, Map.member n stubFns]) in if s' == s then s else grow s'
    generic = Map.fromList ([(fnName g, g) | g <- bodies] ++ [(f, fn) | (f, fn) <- Map.toList stubFns, Set.member f stubsUsed] ++ [(n, stub) | any variadic (Set.toList kept), (n, stub) <- [(packSliceName, packSlice), (packConsName, packCons)]])
    genericOf f = case bodyAndLifted f of
        body : liftedFns -> let generic0 = marked (maybe id (variadicBody (progFunctions program)) (Map.lookup f bounded) (renameFunction rename body)) in generic0 : map marked (maybe [] pure (packContracts generic0)) ++ [marked (renameFunction rename l){fnTypeParams = nubOrd (fnTypeParams body ++ fnTypeParams l)} | l <- liftedFns]
        [] -> []
    marked fn = fn{fnSpec = (fnSpec fn){specEnv = Map.insert genericKey (Const (CInt 0)) (specEnv (fnSpec fn))}}
    keptCopies = Set.fromList [n | (f, copy, liftedCopies) <- made, Set.member f kept, n <- map fnName (copy : liftedCopies)]
    covered fn
        | Set.member (fnName fn) keptCopies = fn{fnSpec = (fnSpec fn){specEnv = Map.insert coveredKey (Const (CInt 0)) (specEnv (fnSpec fn))}}
        | otherwise = fn
    rename n
        | Just (_, trait, function) <- boundCallParts n = stubName trait function
        | Just (g, args) <- Map.lookup n (progInstances program) = case concreteKey program g args of
            Just key -> nameOf named key
            Nothing -> g
        | otherwise = n
    -- (a generic body's proofs name the functions there are, as a copy's do: a name an environment gives a copy or a bound
    -- is the function it stands for, and the environment keeps the functions there are, the stubs and generic bodies included)
    completeGeneric fn = mapEnvs (\e -> Map.union (Map.filterWithKey (\k o -> not (instanceKey k) && case o of Const (CFn n) -> n `Set.member` names; _ -> True) e) copyEnv) (proofsNamed instanceKey fn)
    instanceKey k = Map.member k (progInstances program) || isJust (boundCallParts k)

-- The prelude's functions whose bodies are the builtins a copy runs for the library's Sequence on a Box of an array of a
-- size (resolveBound), with Sequence's contracts
sizedBoxedJustification :: [Name]
sizedBoxedJustification = ["sizedBoxedSize", "sizedBoxedGet", "sizedBoxedSet"]

-- The marks of a function the validator checks generically and of a copy it does not check (no name a program writes has `$`)
genericKey, coveredKey :: Name
genericKey = "$generic"
coveredKey = "$covered"

-- `Tr for $Self::g`, the stub the elaborator writes for each function of each trait (traitStub, lib/elaborate/traits.tersus):
-- a function with bounds whose contracts are the trait's, for any Self that implements it
stubName :: Name -> Name -> Name
stubName trait function = trait ++ " for $Self::" ++ function

isStubName :: Name -> Bool
isStubName name = case parseImplCheckName name of
    Just (_, "$Self", _) -> True
    _ -> False

mapEnvs :: (Env -> Env) -> Function -> Function
mapEnvs f fn = fn{fnSpec = completeSpec (fnSpec fn), fnBlocks = Map.map completeBlock (fnBlocks fn)}
  where
    completeBlock (BasicBlock stmts term) = BasicBlock (map completeStatement stmts) term
    completeStatement (Ghost e g) = Ghost (f e) g
    completeStatement other = other
    completeSpec spec = spec{specEnv = f (specEnv spec), specLoops = Map.map (\loop -> loop{loopEnv = f (loopEnv loop)}) (specLoops spec)}

-- The names a function's code and proofs use (not every name its environments hold)
usedNames :: Function -> [Name]
usedNames fn = Set.toList (Set.fromList (codeNames ++ proofTargets))
  where
    spec = fnSpec fn
    codeNames = concat [concatMap stmtCode ss ++ termCode t | BasicBlock ss t <- Map.elems (fnBlocks fn)]
    stmtCode st = case st of
        Assign _ rv -> [n | Const (CFn n) <- rvalueOperands rv]
        _ -> []
    termCode t = case t of
        Call c args _ _ -> [n | Const (CFn n) <- c : args]
        _ -> []
    envs = Map.unions (specEnv spec : map loopEnv (Map.elems (specLoops spec)) ++ [e | BasicBlock ss _ <- Map.elems (fnBlocks fn), Ghost e _ <- ss])
    proofNames = concatMap validationNames (specRequires spec ++ specEnsures spec ++ concatMap loopInvariant (Map.elems (specLoops spec)) ++ [v | BasicBlock ss _ <- Map.elems (fnBlocks fn), Ghost _ (GhostValidation v) <- ss])
    validationNames v = case v of
        ProofAssert p -> termNames p
        Assume p -> termNames p
        AssignProofVar _ e -> termNames (exprToProof e)
        Rewrite (UserRewrite _ ps) -> concatMap termNames ps
        _ -> []
    termNames p = case p of
        ATerm n -> [n]
        FApp f as -> termNames f ++ concatMap termNames as
        Forall _ gs b -> concatMap termNames gs ++ termNames b
        _ -> []
    proofTargets = [v | n <- proofNames, Just (Const (CFn v)) <- [Map.lookup n envs]]

-- A variadic body as the validator checks it generically (MIR.md, "Copies of variadic functions"): the pack is a list of
-- its elements, a read of it at a number a `get`, each loop over it a loop whose index stays in its bounds (with the
-- invariant the program wrote, if any) and whose measure is what is left of them, a forward the call of the generic callee
-- with the slice `slice(args, lo, hi)` gives, and a function that calls itself through a slice is measured by `size(args)`
-- when it says nothing. A read of the pack in a validation statement is checked in range, as one in code is.
variadicBody :: Map Name Function -> BoundedFn -> Function -> Function
variadicBody functions bounded fn = case [l | l <- fnParams fn, Just d <- [Map.lookup l (fnLocals fn)], TParam q <- [localType d], isPackName q] of
    [p] -> withPack p
    _ -> fn
  where
    withPack p =
        let listTy = case localType (fnLocals fn Map.! p) of
                TParam q -> TList (TParam q)
                t -> t
            name = maybe "args" id (localName (fnLocals fn Map.! p))
            isPack o = case o of
                Copy x -> x == p
                Move x -> x == p
                _ -> False
            taken = Map.fromList [(packElement pl, packIndex pl) | pl <- boundedPackLoops bounded]
            asList st = case st of
                Assign d (Use (Const (CFn "$pack element"))) | Just i <- Map.lookup d taken -> Assign d (ListOp Get [Copy p, Copy i])
                Assign d (ReadField o "$pack" k) | isPack o -> Assign d (ListOp Get [Copy p, Const (CInt (read k))])
                Assign d (Borrow r (RefField "$pack" k : steps) m) | r == p -> Assign d (Borrow r (RefIndex (Const (CInt (read k))) : steps) m)
                _ -> st
            -- (an element read at a number is written as a field of the pack in a proof, as in code)
            elementTerm pr = case pr of
                FApp (CTerm (VFunct _ _ _ (BuiltinFunct (T.Field (Just "$pack") k)) _)) [ATerm a] | a == name, all isDigit k, not (null k) -> FApp (CTerm (builtinFunct T.Get)) [ATerm a, CTerm (VInt (read k))]
                FApp f as -> FApp (elementTerm f) (map elementTerm as)
                Forall v gs b -> Forall v (map elementTerm gs) (elementTerm b)
                _ -> pr
            elementExpr e = case e of
                F (Val (VFunct _ _ _ (BuiltinFunct (T.Field (Just "$pack") k)) _)) [Var a] | a == name, all isDigit k, not (null k) -> F (Val (builtinFunct T.Get)) [Var a, Val (VInt (read k))]
                F f as -> F (elementExpr f) (map elementExpr as)
                _ -> e
            elements v = case v of
                ProofAssert pr -> ProofAssert (elementTerm pr)
                Assume pr -> Assume (elementTerm pr)
                AssignProofVar n e -> AssignProofVar n (elementExpr e)
                Rewrite (UserRewrite n ps) -> Rewrite (UserRewrite n (map elementTerm ps))
                _ -> v
            checked st0 = case elementsIn st0 of
              st -> case st of
                Ghost e (GhostValidation v) | obligations@(_ : _) <- validationObligations name v -> [Ghost e (GhostValidation (ProofAssert o)) | o <- obligations] ++ [st]
                _ -> [st]
            elementsIn st = case st of
                Ghost e (GhostValidation v) -> Ghost e (GhostValidation (elements v))
                _ -> st
            locals0 = Map.adjust (\d -> d{localType = listTy}) p (fnLocals fn)
            blocks0 = Map.map (\(BasicBlock ss t) -> BasicBlock (concatMap checked (map asList ss)) t) (fnBlocks fn)
            next0 = (1 + maximum (0 : [i | Local i <- Map.keys locals0]), 1 + maximum (0 : [i | BlockId i <- Map.keys blocks0]))
            (blocks1, locals1, next1) = foldl forward (blocks0, locals0, next0) (Map.toList blocks0)
            -- (the plain arguments before the forwarded part that the callee's pack takes go before it in the list)
            forward (bs, ls, (nl, nb)) (b, BasicBlock ss t) = case t of
                Call callee@(Const (CFn g)) args d next | (before, pa : lo : hi : after) <- break isPack args ->
                    let fixed = maybe (length before) packAt (Map.lookup g functions)
                        (plain, leading) = splitAt fixed before
                        slice = Local nl
                        conses = [(Local (nl + 1 + k), BlockId (nb + k)) | k <- [0 .. length leading - 1]]
                        final = maybe slice fst (lastMaybe conses)
                        callBlock = BlockId (nb + length leading)
                        firstNext = maybe callBlock snd (headMaybe conses)
                        consBlocks = [ (blk, BasicBlock [] (Call (Const (CFn packConsName)) [e, Copy prev] l (maybe callBlock snd (headMaybe rest))))
                                     | ((l, blk), e, prev, rest) <- zip4' conses (reverse leading) (slice : map fst conses) (drop 1 (tails' conses))
                                     ]
                     in ( Map.insert callBlock (BasicBlock [] (Call callee (plain ++ [Copy final] ++ after) d next)) (Map.union (Map.fromList consBlocks) (Map.insert b (BasicBlock ss (Call (Const (CFn packSliceName)) [pa, lo, hi] slice firstNext)) bs))
                        , Map.union (Map.fromList [(l, LocalDecl listTy Nothing) | l <- slice : map fst conses]) ls
                        , (nl + 1 + length leading, nb + 1 + length leading)
                        )
                _ -> (bs, ls, (nl, nb))
            packAt callee = length (takeWhile (\l -> not (maybe False isPackParam (Map.lookup l (fnLocals callee)))) (fnParams callee))
            isPackParam d = case localType d of
                TParam q -> isPackName q
                TRef (TParam q) -> isPackName q
                _ -> False
            headMaybe xs = case xs of
                x : _ -> Just x
                [] -> Nothing
            lastMaybe xs = headMaybe (reverse xs)
            tails' xs = case xs of
                [] -> [[]]
                _ : rest -> xs : tails' rest
            zip4' (a : as) (b' : bs') (c : cs) (d' : ds) = (a, b', c, d') : zip4' as bs' cs ds
            zip4' _ _ _ _ = []
            -- (a loop over a range of the pack runs no times when hi < lo: its index is bounded by max(lo, hi), worked out
            -- before the loop, so its bounds hold on entry whatever the pack's size)
            (blocks2, locals2, tops, _) = foldl topOf (blocks1, locals1, Map.empty, next1) (boundedPackLoops bounded)
            topOf (bs, ls, ts, (nl, nb)) pl = case [(b, ss) | (b, BasicBlock ss (Goto h)) <- Map.toList bs, h == packHeader pl, b `notElem` packBlocks pl] of
                [(pre, ss)] ->
                    let top = Local nl
                        below = Local (nl + 1)
                     in ( Map.insert (BlockId (nb + 1)) (BasicBlock [Assign top (Use (Copy (packHi pl)))] (Goto (packHeader pl))) (Map.insert (BlockId nb) (BasicBlock [Assign top (Use (Copy (packLo pl)))] (Goto (packHeader pl))) (Map.insert pre (BasicBlock (ss ++ [Assign below (BinaryOp (Compare Lt) (Copy (packHi pl)) (Copy (packLo pl)))]) (SwitchBool (Copy below) (BlockId nb) (BlockId (nb + 1)))) bs))
                        , Map.insert below (LocalDecl TBool Nothing) (Map.insert top (LocalDecl TInt Nothing) ls)
                        , Map.insert (packHeader pl) top ts
                        , (nl + 2, nb + 2)
                        )
                _ -> (bs, ls, ts, (nl, nb))
            loopOf pl =
                let env = Map.fromList [("$i", Copy (packIndex pl)), ("$lo", Copy (packLo pl)), ("$hi", Copy (Map.findWithDefault (packHi pl) (packHeader pl) tops))]
                    bounds = [relation LtEq (ATerm "$lo") (ATerm "$i"), relation LtEq (ATerm "$i") (ATerm "$hi")]
                    measure = Just (Counting (F (Val (builtinFunct T.Minus)) [Var "$hi", Var "$i"]))
                 in case Map.lookup (packHeader pl) (specLoops (fnSpec fn)) of
                        Just written -> written{loopInvariant = bounds ++ loopInvariant written, loopTermination = measure, loopEnv = Map.union env (loopEnv written)}
                        Nothing -> LoopSpec bounds measure (Map.union env (specEnv (fnSpec fn))) (packBody pl)
            loops = Map.fromList [(packHeader pl, loopOf pl) | pl <- boundedPackLoops bounded]
            selfCall = or [n == fnName fn | BasicBlock _ (Call (Const (CFn n)) _ _ _) <- Map.elems blocks2]
            term = case specTermination (fnSpec fn) of
                Nothing | selfCall -> Just (Counting (F (Val (builtinFunct T.Size)) [Var name]))
                other -> other
            -- (a loop invariant's read of the pack is in range wherever the invariant is checked: each is an invariant too)
            specElements sp = sp{specRequires = map elements (specRequires sp), specEnsures = map elements (specEnsures sp), specLoops = Map.map (\l -> l{loopInvariant = concatMap (\v -> let v' = elements v in [ProofAssert o | o <- validationObligations name v'] ++ [v']) (loopInvariant l)}) (specLoops sp)}
         in fn{fnLocals = locals2, fnBlocks = blocks2, fnSpec = specElements ((fnSpec fn){specLoops = Map.union loops (specLoops (fnSpec fn)), specTermination = term})}

-- What a validation statement asks of the pack it reads: each index it reads the pack at is in range, for every value of a
-- forall's variable the read is under
validationObligations :: Name -> ValidationStatement -> [VariableProof]
validationObligations name v = case v of
    ProofAssert pr -> rangeObligations name pr
    Assume pr -> rangeObligations name pr
    AssignProofVar _ e -> rangeObligations name (exprToProof e)
    Rewrite (UserRewrite _ ps) -> concatMap (rangeObligations name) ps
    _ -> []

rangeObligations :: Name -> VariableProof -> [VariableProof]
rangeObligations name pr = case pr of
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct T.Get) _)) [ATerm a, e] | a == name -> inRange e ++ rangeObligations name e
    FApp (ATerm "get") [ATerm a, e] | a == name -> inRange e ++ rangeObligations name e
    FApp f as -> rangeObligations name f ++ concatMap (rangeObligations name) as
    Forall x gs b -> [if mentions x o then Forall x gs o else o | o <- concatMap (rangeObligations name) gs ++ rangeObligations name b]
    _ -> []
  where
    inRange e = [FApp (CTerm (builtinFunct (T.Rel LtEq))) [CTerm (VInt 0), e], FApp (CTerm (builtinFunct (T.Rel Lt))) [e, sizeTerm (ATerm name)]]
    mentions x o = case o of
        BVar y -> x == y
        FApp f as -> mentions x f || any (mentions x) as
        Forall y gs b -> y /= x && (any (mentions x) gs || mentions x b)
        _ -> False

-- A generic variadic body's contracts read the pack in range: a function the validator checks (`f$contract`) with the body's
-- parameters and its result as one more, which proves each read of an input contract under the input contract before it,
-- and each read of an output contract under the input contract and the output contract before it
packContracts :: Function -> Maybe Function
packContracts fn = case [n | l <- fnParams fn, Just d <- [Map.lookup l (fnLocals fn)], TList (TParam q) <- [localType d], isPackName q, Just n <- [localName d]] of
    [name] | any (not . null . validationObligations name) (specRequires spec ++ specEnsures spec) ->
        let result = Local (1 + maximum (0 : [i | Local i <- Map.keys (fnLocals fn)]))
            resultTy = maybe TInt id (fnReturns fn)
            env = specEnv spec
            withResult = Map.insert "return" (Copy result) env
            (plain, sizes) = splitAt (length (fnParams fn) - length (fnSizeParams fn)) (fnParams fn)
            params = plain ++ [result] ++ sizes
            clauses e vs = concat [[Ghost e (GhostValidation (ProofAssert o)) | o <- validationObligations name v] ++ [Ghost e (GhostValidation (assumed v))] | v <- vs]
            statements = clauses env (specRequires spec) ++ clauses withResult (specEnsures spec) ++ [Assign (Local 0) (Use (Const (CInt 0)))]
            locals = Map.insert (Local 0) (LocalDecl TInt Nothing) (Map.insert result (LocalDecl resultTy (Just "return")) (Map.filterWithKey (\l _ -> l `elem` fnParams fn) (fnLocals fn)))
         in Just (Function (fnName fn ++ contractSuffix) params (Just TInt) locals (Map.singleton (BlockId 0) (BasicBlock statements Return)) (fnSizeParams fn) (fnTypeParams fn) (fnBorrowed fn ++ [result]) (fnMutBorrowed fn) [] emptySpec{specEnv = env})
    _ -> Nothing
  where
    spec = fnSpec fn
    assumed v = case v of
        ProofAssert p -> Assume p
        _ -> v

contractSuffix :: String
contractSuffix = "$contract"

relation :: Rel -> VariableProof -> VariableProof -> ValidationStatement
relation r a b = ProofAssert (FApp (CTerm (builtinFunct (T.Rel r))) [a, b])

sizeTerm :: VariableProof -> VariableProof
sizeTerm x = FApp (CTerm (builtinFunct T.Size)) [x]

-- The list of an element before the elements of a list: the plain arguments a forward gives the callee's pack first
packConsName :: Name
packConsName = "<$packcons>"

packCons :: Function
packCons = Function packConsName [Local 1, Local 2] (Just listTy) (Map.fromList [(Local 0, LocalDecl listTy Nothing), (Local 1, LocalDecl (TParam "..A") (Just "x")), (Local 2, LocalDecl listTy (Just "xs"))]) (Map.singleton (BlockId 0) (BasicBlock [] Unreachable)) [] ["..A", "..S"] [Local 1, Local 2] [] [] spec
  where
    listTy = TList (TParam "..S")
    getOf x i = FApp (CTerm (builtinFunct T.Get)) [x, i]
    spec = emptySpec
        { specEnsures =
            [ relation Eq (sizeTerm (ATerm "return")) (FApp (CTerm (builtinFunct T.Plus)) [sizeTerm (ATerm "xs"), CTerm (VInt 1)])
            , relation Eq (getOf (ATerm "return") (CTerm (VInt 0))) (ATerm "x")
            , ProofAssert (Forall "k" [FApp (CTerm (builtinFunct (T.Rel GtEq))) [BVar "k", CTerm (VInt 0)], FApp (CTerm (builtinFunct (T.Rel Lt))) [BVar "k", sizeTerm (ATerm "xs")]] (FApp (CTerm (builtinFunct (T.Rel Eq))) [getOf (ATerm "return") (FApp (CTerm (builtinFunct T.Plus)) [BVar "k", CTerm (VInt 1)]), getOf (ATerm "xs") (BVar "k")]))
            ]
        , specEnv = Map.fromList [("x", Copy (Local 1)), ("xs", Copy (Local 2))]
        }

-- `slice(xs, lo, hi)` of a pack a generic variadic body forwards: the elements from lo to hi - 1 (no name a program writes
-- has `$`)
packSliceName :: Name
packSliceName = "<$packslice>"

packSlice :: Function
packSlice = Function packSliceName [Local 1, Local 2, Local 3] (Just listTy) (Map.fromList [(Local 0, LocalDecl listTy Nothing), (Local 1, LocalDecl listTy (Just "xs")), (Local 2, LocalDecl TInt (Just "lo")), (Local 3, LocalDecl TInt (Just "hi"))]) (Map.singleton (BlockId 0) (BasicBlock [] Unreachable)) [] ["..S"] [Local 1] [] [] spec
  where
    listTy = TList (TParam "..S")
    getOf x i = FApp (CTerm (builtinFunct T.Get)) [x, i]
    spec = emptySpec
        { specRequires = [relation LtEq (CTerm (VInt 0)) (ATerm "lo"), relation LtEq (ATerm "lo") (ATerm "hi"), relation LtEq (ATerm "hi") (sizeTerm (ATerm "xs"))]
        , specEnsures =
            [ relation Eq (sizeTerm (ATerm "return")) (FApp (CTerm (builtinFunct T.Minus)) [ATerm "hi", ATerm "lo"])
            , ProofAssert (Forall "k" [FApp (CTerm (builtinFunct (T.Rel GtEq))) [BVar "k", CTerm (VInt 0)], FApp (CTerm (builtinFunct (T.Rel Lt))) [BVar "k", sizeTerm (ATerm "return")]] (FApp (CTerm (builtinFunct (T.Rel Eq))) [getOf (ATerm "return") (BVar "k"), getOf (ATerm "xs") (FApp (CTerm (builtinFunct T.Plus)) [ATerm "lo", BVar "k"])]))
            ]
        , specEnv = Map.fromList [("xs", Copy (Local 1)), ("lo", Copy (Local 2)), ("hi", Copy (Local 3))]
        }

-- A validated program without what only the validator reads: the generic bodies, the stubs and their markers, and the
-- marks on the copies
withoutGeneric :: Program -> Program
withoutGeneric program =
    completeInstances program{progTypes = Map.filterWithKey (\name _ -> not (derived name)) (progTypes program), progFunctions = Map.map strip kept, progMain = strip (progMain program)}
  where
    derived name =
        let base = baseNameOf name
         in base /= name && maybe False (const True) (maybe (tupleGeneric base) Just (Map.lookup base (progGenerics program)))
    validatorOnly fn = Map.member genericKey (specEnv (fnSpec fn)) || isStubName (fnName fn) || fnName fn `elem` [packSliceName, packConsName]
    kept = Map.filter (not . validatorOnly) (progFunctions program)
    gone n = Map.member n (progFunctions program) && Map.notMember n kept
    strip fn = mapEnvs (Map.filterWithKey (\k o -> k /= coveredKey && case o of Const (CFn n) -> not (gone n); _ -> True)) fn{fnBlocks = Map.map block (fnBlocks fn)}
    block (BasicBlock ss t) = BasicBlock (filter (not . marker) ss) t
    marker st = case st of
        Ghost _ (GhostFunction n _ _) -> gone n
        _ -> False

-- A function whose proofs name, for each name the predicate picks, the function its environment gives it, which the
-- environment then gives by its own name
proofsNamed :: (Name -> Bool) -> Function -> Function
proofsNamed picked fn = fn{fnSpec = spec', fnBlocks = Map.map block (fnBlocks fn)}
  where
    spec = fnSpec fn
    spec' =
        let e = specEnv spec
         in spec
                { specRequires = map (statement e) (specRequires spec)
                , specEnsures = map (statement e) (specEnsures spec)
                , specTermination = fmap (termination e) (specTermination spec)
                , specEnv = extended e (specRequires spec ++ specEnsures spec) (maybe [] terminationExprs (specTermination spec))
                , specLoops = Map.map (\l -> l{loopInvariant = map (statement (loopEnv l)) (loopInvariant l), loopTermination = fmap (termination (loopEnv l)) (loopTermination l), loopEnv = extended (loopEnv l) (loopInvariant l) (maybe [] terminationExprs (loopTermination l))}) (specLoops spec)
                }
    block (BasicBlock ss t) = BasicBlock (map ghost ss) t
    ghost st = case st of
        Ghost e (GhostValidation v) -> Ghost (extended e [v] []) (GhostValidation (statement e v))
        _ -> st
    target e n
        | picked n, Just (Const (CFn f)) <- Map.lookup n e = Just f
        | otherwise = Nothing
    named e n = maybe n id (target e n)
    extended e vs es = Map.union e (Map.fromList [(f, Const (CFn f)) | n <- concatMap validationTerms vs ++ concatMap expressionTerms es, Just f <- [target e n]])
    statement e v = case v of
        ProofAssert p -> ProofAssert (proofR e p)
        Assume p -> Assume (proofR e p)
        AssignProofVar n x -> AssignProofVar n (exprR e x)
        Rewrite r -> Rewrite (case r of
            Refl p -> Refl (proofR e p)
            CheckGtZero p -> CheckGtZero (proofR e p)
            CheckRel p -> CheckRel (proofR e p)
            UserRewrite n ps -> UserRewrite n (map (proofR e) ps)
            _ -> r)
    proofR e p = case p of
        ATerm n -> ATerm (named e n)
        FApp f as -> FApp (proofR e f) (map (proofR e) as)
        Forall n gs b -> Forall n (map (proofR e) gs) (proofR e b)
        _ -> p
    exprR e x = case x of
        Var n -> Var (named e n)
        F f as -> F (exprR e f) (map (exprR e) as)
        Val (VFnRef n) -> Val (VFnRef (named e n))
        _ -> x
    termination e t = case t of
        Shrinks x -> Shrinks (exprR e x)
        Counting x -> Counting (exprR e x)
        Parts x -> Parts (exprR e x)
        Recursing inner -> Recursing (fmap (termination e) inner)
        MayDiverge -> MayDiverge
    terminationExprs t = case t of
        Shrinks x -> [x]
        Counting x -> [x]
        Parts x -> [x]
        Recursing inner -> maybe [] terminationExprs inner
        MayDiverge -> []
    validationTerms v = case v of
        ProofAssert p -> proofTerms p
        Assume p -> proofTerms p
        AssignProofVar _ x -> expressionTerms x
        Rewrite (Refl p) -> proofTerms p
        Rewrite (CheckGtZero p) -> proofTerms p
        Rewrite (CheckRel p) -> proofTerms p
        Rewrite (UserRewrite _ ps) -> concatMap proofTerms ps
        _ -> []
    proofTerms p = case p of
        ATerm n -> [n]
        FApp f as -> proofTerms f ++ concatMap proofTerms as
        Forall _ gs b -> concatMap proofTerms gs ++ proofTerms b
        _ -> []
    expressionTerms x = case x of
        Var n -> [n]
        F f as -> expressionTerms f ++ concatMap expressionTerms as
        Val (VFnRef n) -> [n]
        _ -> []

-- A function with its callees, function constants and the functions its environments name made what the rename says
renameFunction :: (Name -> Name) -> Function -> Function
renameFunction rn fn = (mapEnvs (Map.map opR) fn){fnBlocks = Map.map block (fnBlocks (mapEnvs (Map.map opR) fn))}
  where
    block (BasicBlock ss t) = BasicBlock (map stmt ss) (termR t)
    stmt st = case st of
        Assign l rv -> Assign l (rvR rv)
        Peek l rv -> Peek l (rvR rv)
        AssignRef r steps rv -> AssignRef r steps (rvR rv)
        _ -> st
    termR t = case t of
        Call c args d n -> Call (opR c) (map opR args) d n
        SwitchBool o a b -> SwitchBool (opR o) a b
        _ -> t
    opR o = case o of
        Const c -> Const (constR c)
        _ -> o
    constR c = case c of
        CFn n -> CFn (rn n)
        CData n fs -> CData n [(f, constR v) | (f, v) <- fs]
        CList cs -> CList (map constR cs)
        CArray cs -> CArray (map constR cs)
        _ -> c
    rvR rv = case rv of
        Use o -> Use (opR o)
        BinaryOp b x y -> BinaryOp b (opR x) (opR y)
        ListOp l os -> ListOp l (map opR os)
        MakeList os -> MakeList (map opR os)
        MakeBox o -> MakeBox (opR o)
        Unbox o -> Unbox (opR o)
        Unsize o -> Unsize (opR o)
        MakeData n fs -> MakeData n [(f, opR o) | (f, o) <- fs]
        ReadField o n f -> ReadField (opR o) n f
        IsVariant o n -> IsVariant (opR o) n
        AsVariant o n -> AsVariant (opR o) n
        CopyOf o -> CopyOf (opR o)
        Deref o -> Deref (opR o)
        _ -> rv
