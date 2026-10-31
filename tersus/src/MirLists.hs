module MirLists
    ( lowerLists
    , hasLists
    ) where

import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, listToMaybe)

import Mir
import Types (Arg (..), Name, Type (..), instanceName, mentionsParameter)

-- A list is checked, validated and run by the executor as a list. Native code has no list: a `List<T>` is the struct `StdList<T>` of
-- lib/lists.tersus (the elements in an array on the heap, and how many are in use), and this makes the program that is validated the
-- program with those. It runs after the validator, so the proofs about lists are the proofs of lists, and before ownership, which then
-- sees an ordinary struct that owns a Box of an array.
--
-- Each operation on a list becomes a call of the function of the library (a call ends a block, so a block with one is cut there), each
-- `List<T>` in a type becomes `StdList<T>`, and a list written as a constant (`[1, 2]`) is made by a call of `stdListNew` and one of
-- `stdListPush` for each element. A comparison of lists stays as it is: native code compares a `StdList` as a list (the elements in use,
-- not the room that is left), and prints it as one.

-- A Box is lowered the same way (step 29): a `Box<T>` whose T is not an array is the struct `StdBox<T>` of lib/box.tersus, one filled slot at
-- an address that its drop frees, and `Box::new(x)` and `Box::unbox(b)` are calls of `stdBoxNew` and `stdBoxUnbox`. A field read, a test of a
-- variant or a cast through a Box stays one through the `StdBox`, which native code reads at its address as it read a Box (the address is
-- the struct's only word), so a `match` still takes the fields out of a Box that is not used again.
--
-- A Box of an array, of a size or of any (`Box<Array<T, n>>`, `Box<Array<T>>`), is a `StdList<T>` with as many elements as it has room for:
-- `size`, `get`, `first`, `last` and `set` of one are those of a list, `Array::boxed(n, x)` is a call of `stdListFilled`, `Array::empty()` one
-- of `stdListNew`, and the unsizing of a Box of an array of a size is the list as it is. `Box::new` of an inline array and `Box::unbox` of a
-- Box of an array stay `MakeBox` and `Unbox`, which the emitters make of the list: the array's bytes are moved into memory of their own, or
-- out of it.

-- Whether the program has a list or a Box (of what is not an array) anywhere
hasLists :: Program -> Bool
hasLists program =
    any mentionsList (programTypes program)
        || or [hasListOperation fn | fn <- progMain program : Map.elems (progFunctions program)]
  where
    mentionsList ty = case ty of
        TList _ -> True
        TArrayOf t _ -> mentionsList t
        TBox _ -> True
        TAddr t -> mentionsList t
        TUninit t -> mentionsList t
        TRef t -> mentionsList t
        TFn args ret -> any mentionsList (ret : args)
        TNamed _ args -> or [mentionsList t | ArgType t <- args]
        _ -> False
    hasListOperation fn = or [constantList c | BasicBlock stmts term <- Map.elems (fnBlocks fn), c <- concatMap statementConstants stmts ++ terminatorConstants term]
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
    Clone o -> [o]
    TakeField{} -> []

-- The program with lists and Boxes made of the library's structs and functions. The first program is the library (lib/lists.tersus and
-- lib/box.tersus compiled).
lowerLists :: Program -> Program -> Program
lowerLists library program
    | not (hasLists program) = program
    | otherwise =
        completeErasedInstances
            lowered
                { progTypes = Map.union (progTypes lowered) (progTypes library)
                , progFunctions = Map.union (progFunctions lowered) (progFunctions library)
                , progGenerics = Map.union (progGenerics lowered) (progGenerics library)
                , progInvariants = Map.union (progInvariants lowered) (progInvariants library)
                }
  where
    lowered =
        program
            { progTypes = Map.fromList [(renameName (renamesForTypes (programTypes program)) n, renameDecl d) | (n, d) <- Map.toList (progTypes program)]
            , progFunctions = Map.map (lowerFunction program) (progFunctions program)
            , progMain = lowerFunction program (progMain program)
            , progGenerics = Map.map (\(params, fields) -> (params, [(f, listType t) | (f, t) <- fields])) (progGenerics program)
            }
    renameDecl d = case d of
        StructDecl fields -> StructDecl [(f, listType t) | (f, t) <- fields]
        EnumDecl variants -> EnumDecl [(v, [(f, listType t) | (f, t) <- fields]) | (v, fields) <- variants]

-- The type that a list or a Box is: the struct of the library, with the type of the elements
listType :: Type -> Type
listType ty = case ty of
    TList t -> TNamed "StdList" [ArgType (listType t)]
    TArrayOf t size -> TArrayOf (listType t) size
    TBox (TArrayOf t _) -> TNamed "StdList" [ArgType (listType t)]
    TBox t -> boxStruct t
    TAddr t -> TAddr (listType t)
    TUninit t -> TUninit (listType t)
    TRef t -> TRef (listType t)
    TFn args ret -> TFn (map listType args) (listType ret)
    TNamed base args -> TNamed base (map renameArg args)
    _ -> ty

-- The struct that a Box of the type is
boxStruct :: Type -> Type
boxStruct t = TNamed "StdBox" [ArgType (listType t)]

renameArg :: Arg -> Arg
renameArg (ArgType t) = ArgType (listType t)
renameArg other = other

isArrayType :: Type -> Bool
isArrayType t = case t of
    TArrayOf{} -> True
    _ -> False

-- The name of a struct made with types that are lists, from the types the program has (a data name is a rendered name)
renameName :: Map Name Name -> Name -> Name
renameName renames name = Map.findWithDefault name name renames

-- The rendered names that list lowering renames, built structurally from the types of a program
renamesForTypes :: [Type] -> Map Name Name
renamesForTypes tys = Map.fromList [(instanceName base args, instanceName base (map renameArg args)) | ty <- tys, (base, args) <- namedSubs ty]
  where
    namedSubs ty = case ty of
        TNamed base args -> (base, args) : concat [namedSubs u | ArgType u <- args]
        TList u -> namedSubs u
        TArrayOf u _ -> namedSubs u
        TBox u -> namedSubs u
        TAddr u -> namedSubs u
        TUninit u -> namedSubs u
        TRef u -> namedSubs u
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

-- Ends the block being built with a call of a function of the library, and goes on in a block that follows it
callTo :: Name -> [Operand] -> Local -> M ()
callTo name args dest = do
    s <- getSt
    let next = BlockId (stNextBlock s)
        block = BasicBlock (reverse (stStatements s)) (Call (Const (CFn name)) args dest next)
    modifySt (\s' -> s'{stDone = (stCurrent s', block) : stDone s', stNextBlock = stNextBlock s' + 1, stCurrent = next, stStatements = []})

localTypeOf :: Local -> M (Maybe Type)
localTypeOf l = (\s -> localType <$> Map.lookup l (stLocals s)) <$> getSt

operandType :: Operand -> M (Maybe Type)
operandType o = case o of
    Copy l -> localTypeOf l
    Move l -> localTypeOf l
    Const c -> return (constantType c)

-- The type of a constant, where it says it (a list that has an element has the type of the elements)
constantType :: Constant -> Maybe Type
constantType c = case c of
    CInt _ -> Just TInt
    CBool _ -> Just TBool
    CList cs -> Just (TList (fromMaybe TInt (listToMaybe [t | x <- cs, Just t <- [constantType x]])))
    CData name _ -> Just (if "::" `isInfixOf` name then TVariant name else TNamed name [])
    _ -> Nothing

lowerFunction :: Program -> Function -> Function
lowerFunction original fn =
    fn
        { fnLocals = Map.map (\d -> d{localType = listType (localType d)}) (stLocals final)
        , fnReturns = fmap listType (fnReturns fn)
        , fnBlocks = Map.fromList (stDone final)
        , fnSpec = emptySpec
        }
  where
    ((), final) = runM (mapM_ lowerBlock (Map.toList (fnBlocks fn))) start
    start =
        St
            { stLocals = fnLocals fn
            , stNextLocal = 1 + maximum (0 : [n | Local n <- Map.keys (fnLocals fn)])
            , stNextBlock = 1 + maximum (0 : [n | BlockId n <- Map.keys (fnBlocks fn)])
            , stDone = []
            , stCurrent = BlockId 0
            , stStatements = []
            }
    lowerBlock (b, BasicBlock stmts term) = do
        modifySt (\s -> s{stCurrent = b, stStatements = []})
        mapM_ lowerStatement stmts
        term' <- lowerTerminator term
        s <- getSt
        modifySt (\s' -> s'{stDone = (stCurrent s, BasicBlock (reverse (stStatements s)) term') : stDone s', stStatements = []})

    lowerStatement stmt = case stmt of
        Ghost{} -> return ()
        Assign dest rv -> lowerAssign dest rv
        -- (a value taken apart is cleared where it is, and what it held is not freed: see MirGhost)
        Peek _ (ListOp UninitEmpty []) -> emit stmt
        Peek dest rv -> lowerAssign dest rv
        Drop _ -> emit stmt

    lowerAssign dest rv = do
        destTy <- fromMaybe TInt <$> localTypeOf dest
        boxed <- case rv of
            Unbox o -> heldIn o
            _ -> return Nothing
        case (rv, boxed) of
            (ListOp NewBoxed [n, x], _) | TBox (TArrayOf element _) <- destTy -> operandFor element x >>= \x' -> callTo "stdListFilled" [n, x'] dest
            (ListOp NewEmptyBoxed [], _) | TBox TArrayOf{} <- destTy -> callTo "stdListNew" [] dest
            (Unsize o, _) -> emit (Assign dest (Use (renameOperand o)))
            (MakeBox o, _) | TBox held <- destTy, not (isArrayType held) -> operandFor held o >>= \o' -> callTo "stdBoxNew" [o'] dest
            (Unbox o, Just _) -> callTo "stdBoxUnbox" [renameOperand o] dest
            _ -> lowerOther dest destTy rv

    -- (the type a Box that is not of an array holds, if the operand is one)
    heldIn o = do
        ty <- operandType o
        return $ case ty of
            Just (TBox held) | not (isArrayType held) -> Just held
            _ -> Nothing

    lowerOther dest destTy rv =
        case rv of
            ListOp op os@(first : _) -> do
                isList <- listOperand first
                if isList then listCall dest destTy op os else rewritten dest destTy rv
            MakeList os -> do
                let element = case destTy of
                        TList t -> t
                        _ -> TInt
                callTo "stdListNew" [] dest
                mapM_ (\o -> operandFor element o >>= \o' -> callTo "stdListPush" [Copy dest, o'] dest) os
            _ -> rewritten dest destTy rv

    rewritten dest destTy rv = do
        rv' <- lowerRvalue destTy rv
        emit (Assign dest rv')

    listOperand o = do
        ty <- operandType o
        return $ case (o, ty) of
            (Const (CList _), _) -> True
            (_, Just (TList _)) -> True
            -- (a Box of an array is a list of native code)
            (_, Just (TBox TArrayOf{})) -> True
            _ -> False

    listCall dest destTy op os = do
        operandTy <- maybe (TList TInt) id <$> operandType (head os)
        -- (a list that is pushed to or set is the list that results, which says the type of a constant that is empty)
        let listTy = case (op, destTy, head os) of
                (Push, TList _, _) -> destTy
                (Set, TList _, _) -> destTy
                -- (the list that is popped has the type of the result)
                (Pop, TList _, _) -> destTy
                -- (a constant list that is read from has elements of the type that is read, which an empty one among them does not say)
                (_, _, Const _) | op `elem` [First, Last, Get] -> TList destTy
                _ -> operandTy
            element = case listTy of
                TList t -> t
                TBox (TArrayOf t _) -> t
                _ -> case destTy of
                    TList t -> t
                    _ -> TInt
        l <- operandFor listTy (head os)
        let struct = case listType listTy of
                TNamed base args -> instanceName base args
                _ -> "StdList"
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
            (Push, [x]) -> operandFor element x >>= \x' -> callTo "stdListPush" [l, x'] dest
            (Pop, []) -> callTo "stdListPop" [l] dest
            (Set, [i, x]) -> operandFor element x >>= \x' -> callTo "stdListSet" [l, i, x'] dest
            _ -> emit (Assign dest (ListOp op os))

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
                    (TBox (TArrayOf t _), _) -> t
                    _ -> TInt
            -- (the element that an array is made of, or that is put in it, has the type of the elements of the array)
            let isElement i = (i == (1 :: Int) && op `elem` [NewArray, NewBoxed]) || (i == 2 && op `elem` [Set, AddrWrite])
            os' <- mapM (\(i, o) -> operandFor (if isElement i then element else TInt) o) (zip [0 ..] os)
            return (ListOp op os')
        MakeBox o -> MakeBox <$> operandFor (case destTy of TBox t -> t; t -> t) o
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
        other -> return other

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
        TList e -> unknown e
        TBox e -> unknown e
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

    renames = renamesForTypes (programTypes original)
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
                    TList e | not (unknown e) -> ty
                    _ -> fromMaybe (TList TInt) (constantType c)
                element = case listTy of
                    TList t -> t
                    _ -> TInt
            temp <- newTemp listTy
            callTo "stdListNew" [] temp
            mapM_ (\x -> operandFor element (Const x) >>= \x' -> callTo "stdListPush" [Copy temp, x'] temp) cs
            return (Copy temp)
        CData name fs -> do
            let fieldTypes = fieldTypesOf name
            fs' <- mapM (\(f, v) -> (,) f <$> operandFor (fromMaybe TInt (lookup f fieldTypes)) (Const v)) fs
            temp <- newTemp (if "::" `isInfixOf` name then TVariant name else TNamed name [])
            emit (Assign temp (MakeData (renameName renames name) fs'))
            return (Copy temp)
        _ -> return (Const (renameConstant renames c))

firstJust :: [Maybe a] -> Maybe a
firstJust xs = listToMaybe [x | Just x <- xs]
