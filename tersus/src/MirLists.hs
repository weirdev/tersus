{-# LANGUAGE ViewPatterns #-}

module MirLists
    ( lowerLists
    , hasLists
    , ownerSourceId
    ) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, listToMaybe)

import PreludeSource (nativeStorageModules, nativeHelperName)
import Link (linkWithLibraries)
import MirMono (namedTypesByName)
import LibPackage (libModuleId, stripDeclaredFromUnits)
import PackageData (ModuleId (..))
import Utils (Result (..), bindResult, mapResult)
import Mir
import Types (Arg (..), Name, Storage (..), Type (..), boxContent, instanceName, listElement, listOf, listType, mentionsParameter, renameArg)

-- A list is checked, validated and run by the executor as a list. Native code has no list: a `List<T>` is the struct `List<T>` of
-- lib/std/lists/lists.tersus (the elements in an array on the heap, and how many are in use), and this makes the program that is validated the
-- program with those. It runs after the validator, so the proofs about lists are the proofs of lists, and before ownership, which then
-- sees an ordinary struct that owns a Box of an array.
--
-- Each operation on a list becomes a call of the function of the library (a call ends a block, so a block with one is cut there), each
-- `List<T>` in a type becomes `List<T>`, and a list written as a constant (`[1, 2]`) is made by a call of `listNew` and one of
-- `listPush` for each element; a non-empty one of Ints, Bools or Bytes (the bytes of a string literal) is made as `Box::new(#[1, 2])`
-- is, a constant array copied into memory of its own. A comparison of lists stays as it is: native code compares a `List` as a list (the elements in use,
-- not the room that is left), and prints it as one.

-- A Box is lowered the same way (step 29): a `Box<T>` whose T is not an array is the struct `Box<T>` of lib/std/box/box.tersus, one filled slot at
-- an address that its drop frees, and `Box::new(x)` and `Box::unbox(b)` are calls of `boxNew` and `boxUnbox`. A field read, a test of a
-- variant or a cast through a Box stays one through the `Box`, which native code reads at its address as it read a Box (the address is
-- the struct's only word), so a `match` still takes the fields out of a Box that is not used again.
--
-- A Box of an array, of a size or of any (`Box<Array<T, n>>`, `Box<Array<T>>`), is a `List<T>` with as many elements as it has room for:
-- `size`, `get`, `first`, `last` and `set` of one are those of a list, `Array::boxed(n, x)` is a call of `listFilled`, `Array::empty()` one
-- of `listNew`, and the unsizing of a Box of an array of a size is the list as it is. `Box::new` of an inline array and `Box::unbox` of a
-- Box of an array stay `MakeBox` and `Unbox`, which the emitters make of the list: the array's bytes are moved into memory of their own, or
-- out of it.

-- Whether the program has a list or a Box (of what is not an array) anywhere
hasLists :: Program -> Bool
hasLists = not . null . storageModules

storageModules :: Program -> [String]
storageModules program =
    [name | name <- nativeStorageModules, name `elem` concatMap storageTypes (programTypes program) || name == "lists" && any hasListConstant functions]
  where
    functions = progMain program : Map.elems (progFunctions program)
    st = progStorage program
    storageTypes ty = case ty of
        (listElement st -> Just t) -> "lists" : storageTypes t
        (boxContent st -> Just (TArrayOf t _)) -> "lists" : storageTypes t
        (boxContent st -> Just t) -> "box" : storageTypes t
        TArrayOf t _ -> storageTypes t
        TAddr t -> storageTypes t
        TUninit t -> storageTypes t
        TRef t -> storageTypes t
        TMutRef t -> storageTypes t
        TFn args ret -> concatMap storageTypes (ret : args)
        TNamed _ args -> concat [storageTypes t | ArgType t <- args]
        _ -> []
    hasListConstant fn = or [constantList c | BasicBlock stmts term <- Map.elems (fnBlocks fn), c <- concatMap statementConstants stmts ++ terminatorConstants term]
    constantList c = case c of
        CList _ -> True
        CData _ fs -> any (constantList . snd) fs
        CArray cs -> any constantList cs
        _ -> False

programTypes :: Program -> [Type]
programTypes program =
    concat [localType d : [] | fn <- progMain program : Map.elems (progFunctions program), d <- Map.elems (fnLocals fn)]
        ++ [t | fn <- progMain program : Map.elems (progFunctions program), Just t <- [fnReturns fn]]
        ++ [t | StructDecl fields <- Map.elems (progTypes program), (_, t) <- fields]
        ++ [t | EnumDecl variants <- Map.elems (progTypes program), (_, fields) <- variants, (_, t) <- fields]
        ++ [t | (_, fields) <- Map.elems (progGenerics program), (_, t) <- fields]

statementConstants :: Statement -> [Constant]
statementConstants s = case s of
    Assign _ rv -> rvalueOperands rv
    Peek _ rv -> rvalueOperands rv
    _ -> []
  where
    rvalueOperands rv = [c | Const c <- operandsOf rv]

terminatorConstants :: Terminator -> [Constant]
terminatorConstants t = case t of
    SwitchBool o _ _ -> [c | Const c <- [o]]
    Call callee args _ _ -> [c | Const c <- callee : args]
    _ -> []

operandsOf :: Rvalue -> [Operand]
operandsOf rv = case rv of
    Use o -> [o]
    BinaryOp _ a b -> [a, b]
    ListOp _ os -> os
    MakeList os -> os
    MakeBox o -> [o]
    Unbox o -> [o]
    Unsize o -> [o]
    MakeData _ fs -> map snd fs
    ReadField o _ _ -> [o]
    IsVariant o _ -> [o]
    AsVariant o _ -> [o]
    CopyOf o -> [o]
    TakeField{} -> []
    Borrow _ steps _ -> [o | RefIndex o <- steps]
    Deref o -> [o]

-- The unit of core's List and Box drops as the native storage program has them before the erasure, which the erased
-- ones are told to be by (lowerLists)
ownerSourceId :: ModuleId
ownerSourceId = ModuleId "native" (Just "storage-drops")

lowerLists :: Result [(ModuleId, Program)] String -> Program -> Result Program String
lowerLists library program
    | not (hasLists program) = Ok program
    | otherwise = library `bindResult` \units -> mapResult completeErasedInstances (linkWithLibraries (selected units ++ owned units) [(ModuleId "native" Nothing, completeErasedInstances (lowered units))])
  where
    -- (the drops of a list and a Box are their owning module's, core's, and native code has them as the native storage
    -- does: physical, without their ghosts. A function of the program is taken in that form only where it is that very
    -- function, as core's unit has it before the erasure or after it; any other stays the program's own)
    ownerId = libModuleId "core"
    sources units = Map.unions [progFunctions unit | (modu, unit) <- units, modu == ownerSourceId]
    same units name erasedFn = case (Map.lookup name (progFunctions program), Map.lookup name (sources units)) of
        (Just own, Just original) -> body own == body original || body own == body erasedFn
        _ -> False
    body f = (fnParams f, fnReturns f, fnTypeParams f, fnSizeParams f, fnLocals f, fnBlocks f)
    owned units = [(modu, unit{progFunctions = Map.filterWithKey (same units) (progFunctions unit)}) | (modu, unit) <- units, modu == ownerId]
    ownedNames units = Set.unions [Map.keysSet (progFunctions unit) | (_, unit) <- owned units]
    wanted = storageModules program
    st = progStorage program
    unusedTypes = [ty | (modu, ty) <- [("lists", storageList st), ("box", storageBox st)], modu `notElem` wanted]
    selected units = stripDeclaredFromUnits unusedTypes [(modu, unit) | (modu, unit) <- units, modu `elem` map libModuleId wanted]
    lowered units =
        program
            { progTypes = Map.fromList [(renameName renames n, renameDecl d) | (n, d) <- Map.toList (progTypes program), Set.notMember n boxedArrays]
            , progFunctions = Map.map (lowerFunction renames program) (Map.withoutKeys (progFunctions program) (ownedNames units))
            , progMain = lowerFunction renames program (progMain program)
            , progGenerics = Map.map (\(params, fields) -> (params, [(f, listType st t) | (f, t) <- fields])) (progGenerics program)
            }
    -- (a Box of an array is held as a list of its elements, so no value is of the Box's own instance, whose size may be
    -- one no use decided)
    boxedArrays = Map.keysSet (Map.filter (\ty -> case boxContent st ty of Just TArrayOf{} -> True; _ -> False) (namedTypesByName program))
    -- (once for the program: every function renames by it, and it is made of every local of every function)
    renames = renamesForTypes st (programTypes program)
    renameDecl d = case d of
        StructDecl fields -> StructDecl [(f, listType st t) | (f, t) <- fields]
        EnumDecl variants -> EnumDecl [(v, [(f, listType st t) | (f, t) <- fields]) | (v, fields) <- variants]

isArrayType :: Type -> Bool
isArrayType t = case t of
    TArrayOf{} -> True
    _ -> False

-- The name of a struct made with types that are lists, from the types the program has (a data name is a rendered name)
renameName :: Map Name Name -> Name -> Name
renameName renames name = Map.findWithDefault name name renames

-- The rendered names that list lowering renames, built structurally from the types of a program
renamesForTypes :: Storage -> [Type] -> Map Name Name
renamesForTypes st tys = Map.fromList [(instanceName base args, instanceName base (map (renameArg st) args)) | ty <- tys, (base, args) <- namedSubs ty]
  where
    namedSubs ty = case ty of
        TNamed base args -> (base, args) : concat [namedSubs u | ArgType u <- args]
        TArrayOf u _ -> namedSubs u
        TAddr u -> namedSubs u
        TUninit u -> namedSubs u
        TRef u -> namedSubs u
        TMutRef u -> namedSubs u
        TFn as r -> concatMap namedSubs (r : as)
        TForall _ _ u -> namedSubs u
        _ -> []

renameConstant :: Map Name Name -> Constant -> Constant
renameConstant renames c = case c of
    CData name fields -> CData (renameName renames name) [(f, renameConstant renames v) | (f, v) <- fields]
    CList cs -> CList (map (renameConstant renames) cs)
    CArray cs -> CArray (map (renameConstant renames) cs)
    _ -> c

-- The state of lowering a function: its locals (with the temporaries that were added), the blocks that are finished, and the one being built
data St = St
    { stLocals :: Map Local LocalDecl
    , stNextLocal :: Int
    , stNextBlock :: Int
    , stDone :: [(BlockId, BasicBlock)]
    , stCurrent :: BlockId
    , stStatements :: [Statement] -- (backwards)
    , stStorage :: Storage
    }

newtype M a = M {runM :: St -> (a, St)}

instance Functor M where
    fmap f (M g) = M (\s -> let (a, s') = g s in (f a, s'))

instance Applicative M where
    pure a = M (\s -> (a, s))
    M f <*> M g = M (\s -> let (h, s') = f s; (a, s'') = g s' in (h a, s''))

instance Monad M where
    M g >>= f = M (\s -> let (a, s') = g s in runM (f a) s')

getSt :: M St
getSt = M (\s -> (s, s))

modifySt :: (St -> St) -> M ()
modifySt f = M (\s -> ((), f s))

emit :: Statement -> M ()
emit stmt = modifySt (\s -> s{stStatements = stmt : stStatements s})

newTemp :: Type -> M Local
newTemp ty = do
    s <- getSt
    let l = Local (stNextLocal s)
    modifySt (\s' -> s'{stLocals = Map.insert l (LocalDecl ty Nothing) (stLocals s'), stNextLocal = stNextLocal s' + 1})
    return l

-- Ends the block being built with a call of a function of the native storage helpers, and goes on in a block that follows it
callTo :: Name -> [Operand] -> Local -> M ()
callTo name args dest = do
    s <- getSt
    let next = BlockId (stNextBlock s)
        block = BasicBlock (reverse (stStatements s)) (Call (Const (CFn (nativeHelperName name))) args dest next)
    modifySt (\s' -> s'{stDone = (stCurrent s', block) : stDone s', stNextBlock = stNextBlock s' + 1, stCurrent = next, stStatements = []})

localTypeOf :: Local -> M (Maybe Type)
localTypeOf l = (\s -> localType <$> Map.lookup l (stLocals s)) <$> getSt

operandType :: Operand -> M (Maybe Type)
operandType o = case o of
    Copy l -> localTypeOf l
    Move l -> localTypeOf l
    Const c -> (\s -> constantType (stStorage s) c) <$> getSt

lowerFunction :: Map Name Name -> Program -> Function -> Function
lowerFunction renames original fn =
    fn
        { fnLocals = Map.mapWithKey (\l d -> d{localType = if Map.member l boxedFromLists then TInt else listType st (localType d)}) (stLocals final)
        , fnReturns = fmap (listType st) (fnReturns fn)
        , fnBlocks = Map.fromList (stDone final)
        , fnSpec = emptySpec
        }
  where
    st = progStorage original
    -- (a Box of an array made from a list is the list itself, as a Box of an array is a List: the elements are
    -- already in their own memory, and making an inline array of them first would need a size the type does not give)
    boxedFromLists =
        Map.fromList
            [ (l, src)
            | Assign l (ListOp FromList [src]) <- allStatements
            , useCount l == 1
            , Assign dest (MakeBox o) <- allStatements
            , operandLocal o == Just l
            , Just ((boxContent st -> Just TArrayOf{})) <- [localType <$> Map.lookup dest (fnLocals fn)]
            ]
    allStatements = [s | BasicBlock ss _ <- Map.elems (fnBlocks fn), s <- ss]
    allOperands = concatMap statementOperands allStatements ++ concatMap terminatorOperands [t | BasicBlock _ t <- Map.elems (fnBlocks fn)]
    useCount l = length [() | o <- allOperands, operandLocal o == Just l]
    statementOperands s = case s of
        Assign _ rv -> operandsOf rv
        Peek _ rv -> operandsOf rv
        AssignRef _ steps rv -> operandsOf rv ++ [o | RefIndex o <- steps]
        _ -> []
    terminatorOperands t = case t of
        SwitchBool o _ _ -> [o]
        Call callee args _ _ -> callee : args
        _ -> []
    operandLocal o = case o of
        Copy l -> Just l
        Move l -> Just l
        Const _ -> Nothing
    ((), final) = runM (mapM_ lowerBlock (Map.toList (fnBlocks fn))) start
    start =
        St
            { stLocals = fnLocals fn
            , stNextLocal = 1 + maximum (0 : [n | Local n <- Map.keys (fnLocals fn)])
            , stNextBlock = 1 + maximum (0 : [n | BlockId n <- Map.keys (fnBlocks fn)])
            , stDone = []
            , stCurrent = BlockId 0
            , stStatements = []
            , stStorage = st
            }
    lowerBlock (b, BasicBlock stmts term) = do
        modifySt (\s -> s{stCurrent = b, stStatements = []})
        mapM_ lowerStatement stmts
        term' <- lowerTerminator term
        s <- getSt
        modifySt (\s' -> s'{stDone = (stCurrent s, BasicBlock (reverse (stStatements s)) term') : stDone s', stStatements = []})

    lowerStatement stmt = case stmt of
        Ghost{} -> return ()
        Assign dest rv | Map.member dest boxedFromLists -> return ()
        Assign dest rv -> lowerAssign dest rv
        AssignRef root steps rv -> do
            rootTy <- fromMaybe TInt <$> localTypeOf root
            let inner ty = case ty of TRef t -> t; TMutRef t -> t; t -> t
                stepType _ (RefField ctor field) = fromMaybe TInt (lookup field (fieldTypesOf ctor))
                stepType ty (RefIndex _) = case inner ty of
                    (listElement st -> Just t) -> t
                    TArrayOf t _ -> t
                    (boxContent st -> Just (TArrayOf t _)) -> t
                    _ -> TInt
                targetTy = foldl stepType (inner rootTy) steps
            value <- case rv of
                Use o -> operandFor targetTy o
                _ -> do
                    temp <- newTemp targetTy
                    lowerAssign temp rv
                    return (Copy temp)
            emit (AssignRef root (map renameBorrowStep steps) (Use value))
        -- (a value taken apart is cleared where it is, and what it held is not freed: see the ghost erasure)
        Peek _ (ListOp UninitEmpty []) -> emit stmt
        Peek dest rv -> lowerAssign dest rv
        Drop _ -> emit stmt

    lowerAssign dest rv = do
        destTy <- fromMaybe TInt <$> localTypeOf dest
        boxed <- case rv of
            Unbox o -> heldIn o
            _ -> return Nothing
        case (rv, boxed) of
            (ListOp NewBoxed [n, x], _) | (boxContent st -> Just (TArrayOf element _)) <- destTy -> operandFor element x >>= \x' -> callTo "listFilled" [n, x'] dest
            (ListOp NewEmptyBoxed [], _) | (boxContent st -> Just TArrayOf{}) <- destTy -> callTo "listNew" [] dest
            (Unsize o, _) -> emit (Assign dest (Use (renameOperand o)))
            (MakeBox o, _) | Just l <- operandLocal o, Just src <- Map.lookup l boxedFromLists -> emit (Assign dest (Use src))
            (MakeBox o, _) | (boxContent st -> Just held) <- destTy, not (isArrayType held) -> operandFor held o >>= \o' -> callTo "boxNew" [o'] dest
            (Unbox o, Just _) -> callTo "boxUnbox" [renameOperand o] dest
            _ -> lowerOther dest destTy rv

    -- (the type a Box that is not of an array holds, if the operand is one)
    heldIn o = do
        ty <- operandType o
        return $ case ty of
            Just ((boxContent st -> Just held)) | not (isArrayType held) -> Just held
            _ -> Nothing

    lowerOther dest destTy rv =
        case rv of
            ListOp op os@(first : _) -> do
                isList <- listOperand first
                if isList then listCall dest destTy op os else rewritten dest destTy rv
            MakeList os -> do
                let element = case destTy of
                        (listElement st -> Just t) -> t
                        _ -> TInt
                callTo "listNew" [] dest
                mapM_ (\o -> operandFor element o >>= \o' -> callTo "listPush" [Copy dest, o'] dest) os
            _ -> rewritten dest destTy rv

    rewritten dest destTy rv = do
        rv' <- lowerRvalue destTy rv
        emit (Assign dest rv')

    listOperand o = do
        ty <- operandType o
        return $ case (o, ty) of
            (Const (CList _), _) -> True
            (_, Just ((listElement st -> Just _))) -> True
            (_, Just (TRef ((listElement st -> Just _)))) -> True
            (_, Just (TMutRef ((listElement st -> Just _)))) -> True
            -- (a Box of an array is a list of native code)
            (_, Just ((boxContent st -> Just TArrayOf{}))) -> True
            _ -> False

    listCall dest destTy op os = do
        operandTy0 <- maybe (listOf st TInt) id <$> operandType (head os)
        let operandTy = case operandTy0 of
                TRef inner -> inner
                TMutRef inner -> inner
                other -> other
        -- (a list that is pushed to or set is the list that results, which says the type of a constant that is empty)
        let listTy = case (op, destTy, head os) of
                (Push, (listElement st -> Just _), _) -> destTy
                (Set, (listElement st -> Just _), _) -> destTy
                -- (the list that is popped has the type of the result)
                (Pop, (listElement st -> Just _), _) -> destTy
                -- (an Uninit of a list is the list natively, so the one it is made with has the type of the result)
                (UninitNew, (listElement st -> Just _), _) -> destTy
                -- (a constant list that is read from has elements of the type that is read, which an empty one among them does not say)
                (_, _, Const _) | op `elem` [First, Last, Get] -> listOf st destTy
                _ -> operandTy
            element = case listTy of
                (listElement st -> Just t) -> t
                (boxContent st -> Just (TArrayOf t _)) -> t
                _ -> case destTy of
                    (listElement st -> Just t) -> t
                    _ -> TInt
        l <- operandFor listTy (head os)
        let struct = case listType st listTy of
                TNamed base args -> instanceName base args
                other -> instanceName (storageList st) [ArgType other]
        case (op, drop 1 os) of
            -- (an element is read from the list where it is: a part that is only read is not copied)
            (Length, []) -> emit (Assign dest (ReadField l struct "len"))
            (First, []) -> emit (Assign dest (ListOp Get [l, Const (CInt 0)]))
            (Last, []) -> do
                n <- newTemp TInt
                emit (Assign n (ReadField l struct "len"))
                index <- newTemp TInt
                emit (Assign index (BinaryOp Sub (Copy n) (Const (CInt 1))))
                emit (Assign dest (ListOp Get [l, Copy index]))
            (Get, [i]) -> emit (Assign dest (ListOp Get [l, i]))
            (Push, [x]) -> operandFor element x >>= \x' -> callTo "listPush" [l, x'] dest
            (Pop, []) -> callTo "listPop" [l] dest
            (Set, [i, x]) -> operandFor element x >>= \x' -> callTo "listSet" [l, i, x'] dest
            (FromList, []) -> emit (Assign dest (ListOp FromList [l]))
            _ -> emit (Assign dest (ListOp op (l : drop 1 os)))

    lowerRvalue destTy rv = case rv of
        Use o -> Use <$> operandFor destTy o
        BinaryOp op a b -> do
            ta <- operandType a
            tb <- operandType b
            let ty = fromMaybe TInt (firstJust [nonConstant a ta, nonConstant b tb, ta, tb])
            BinaryOp op <$> operandFor ty a <*> operandFor ty b
        ListOp op os -> do
            -- (what is written to memory has the type of what the address is of)
            addressTy <- case (op, os) of
                (AddrWrite, p : _) -> operandType p
                _ -> return Nothing
            let element = case (destTy, addressTy) of
                    (_, Just (TAddr t)) -> t
                    (TArrayOf t _, _) -> t
                    ((boxContent st -> Just (TArrayOf t _)), _) -> t
                    _ -> TInt
            -- (the element that an array is made of, or that is put in it, has the type of the elements of the array)
            let isElement i = (i == (1 :: Int) && op `elem` [NewArray, NewBoxed]) || (i == 2 && op `elem` [Set, AddrWrite])
            os' <- mapM (\(i, o) -> operandFor (if isElement i then element else TInt) o) (zip [0 ..] os)
            return (ListOp op os')
        MakeBox o -> MakeBox <$> operandFor (case destTy of (boxContent st -> Just t) -> t; t -> t) o
        Unbox o -> return (Unbox (renameOperand o))
        Unsize o -> return (Unsize (renameOperand o))
        MakeData name fs -> do
            let fieldTypes = fieldTypesOf name
            fs' <- mapM (\(f, o) -> (,) f <$> operandFor (fromMaybe TInt (lookup f fieldTypes)) o) fs
            return (MakeData (renameName renames name) fs')
        ReadField o name f -> do
            o' <- operandFor (if "::" `isInfixOf` name then TVariant name else TNamed name []) o
            return (ReadField o' (renameName renames name) f)
        IsVariant o name -> return (IsVariant (renameOperand o) (renameName renames name))
        AsVariant o name -> return (AsVariant (renameOperand o) (renameName renames name))
        Borrow root steps upd -> do
            rootTy <- fromMaybe TInt <$> localTypeOf root
            return (Borrow root (nativeBorrowSteps rootTy steps (unref destTy)) upd)
        other -> return other

    -- Source Box places are transparent. Native places follow storage at slot zero,
    -- except when the field or final reference names the Box handle itself.
    nativeBorrowSteps ty steps wanted = case ty of
        TRef inner -> nativeBorrowSteps inner steps wanted
        TMutRef inner -> nativeBorrowSteps inner steps wanted
        (boxContent st -> Just inner) | RefField ctor _ : _ <- steps,
            ctor /= instanceName (storageBox st) [ArgType inner] ->
                RefIndex (Const (CInt 0)) : nativeBorrowSteps inner steps wanted
        _ -> case steps of
            [] -> [RefIndex (Const (CInt 0)) | Just inner <- [boxContent st ty], inner == wanted]
            RefField ctor field : rest -> renameBorrowStep (RefField ctor field) :
                nativeBorrowSteps (fromMaybe TInt (lookup field (fieldTypesOf ctor))) rest wanted
            RefIndex index : rest -> RefIndex (renameOperand index) : nativeBorrowSteps (case ty of
                (listElement st -> Just inner) -> inner
                TArrayOf inner _ -> inner
                (boxContent st -> Just (TArrayOf inner _)) -> inner
                _ -> TInt) rest wanted
    unref (TRef ty) = ty
    unref (TMutRef ty) = ty
    unref ty = ty

    nonConstant o ty = case o of
        Const _ -> Nothing
        _ -> ty

    fieldTypesOf name = case Map.lookup name (progTypes original) of
        Just (StructDecl fields) -> fields
        _ -> listToMaybeList [fields | EnumDecl variants <- Map.elems (progTypes original), (v, fields) <- variants, v == name]
    listToMaybeList xs = fromMaybe [] (listToMaybe xs)

    lowerTerminator term = case term of
        SwitchBool o yes no -> (\o' -> SwitchBool o' yes no) <$> operandFor TBool o
        Call callee args dest next -> do
            paramTypes <- calleeParameters callee
            -- (the types of the parameters of a function with types are its own: what a list passed to it is of, the call does not say)
            let wanted t = if mentionsParameter t && not (sameFunction callee) then TVar 0 else t
            args' <- mapM (\(i, a) -> operandFor (maybe (TVar 0) wanted (listToMaybe (drop i paramTypes))) a) (zip [0 ..] args)
            return (Call (renameOperand callee) args' dest next)
        _ -> return term

    sameFunction callee = callee == Const (CFn (fnName fn))
    unknown t = case t of
        TVar _ -> True
        (listElement st -> Just e) -> unknown e
        (boxContent st -> Just e) -> unknown e
        TAddr e -> unknown e
        TUninit e -> unknown e
        TArrayOf e _ -> unknown e
        _ -> False

    calleeParameters callee = case callee of
        Const (CFn name) -> return $ case Map.lookup name (progFunctions original) of
            Just f -> [localType d | p <- fnParams f, Just d <- [Map.lookup p (fnLocals f)]]
            Nothing -> []
        Copy l -> localTypeOf l >>= \t -> return (case t of Just (TFn ps _) -> ps; _ -> [])
        Move l -> localTypeOf l >>= \t -> return (case t of Just (TFn ps _) -> ps; _ -> [])
        _ -> return []

    renameBorrowStep step = case step of
        RefField name field -> RefField (renameName renames name) field
        RefIndex o -> RefIndex (renameOperand o)

    renameOperand o = case o of
        Const c -> Const (renameConstant renames c)
        _ -> o

    -- The operand for a place that wants a value of the type: a constant that has a list in it is made first
    operandFor ty o = case o of
        Const c | constantHasList c -> materialize ty c
        _ -> return (renameOperand o)

    constantHasList c = case c of
        CList _ -> True
        CData _ fs -> any (constantHasList . snd) fs
        CArray cs -> any constantHasList cs
        _ -> False

    materialize ty c = case c of
        CList cs -> do
            let listTy = case ty of
                    (listElement st -> Just e) | not (unknown e) -> ty
                    _ -> fromMaybe (listOf st TInt) (constantType st c)
                element = case listTy of
                    (listElement st -> Just t) -> t
                    _ -> TInt
            temp <- newTemp listTy
            if not (null cs) && element `elem` [TInt, TBool, TByte] && all scalar cs
                then emit (Assign temp (MakeBox (Const (CArray cs))))
                else do
                    callTo "listNew" [] temp
                    mapM_ (\x -> operandFor element (Const x) >>= \x' -> callTo "listPush" [Copy temp, x'] temp) cs
            return (Copy temp)
        CData name fs -> do
            let fieldTypes = fieldTypesOf name
            fs' <- mapM (\(f, v) -> (,) f <$> operandFor (fromMaybe TInt (lookup f fieldTypes)) (Const v)) fs
            temp <- newTemp (if "::" `isInfixOf` name then TVariant name else TNamed name [])
            emit (Assign temp (MakeData (renameName renames name) fs'))
            return (Copy temp)
        _ -> return (Const (renameConstant renames c))
    scalar c = case c of
        CInt _ -> True
        CBool _ -> True
        _ -> False

firstJust :: [Maybe a] -> Maybe a
firstJust xs = listToMaybe [x | Just x <- xs]
