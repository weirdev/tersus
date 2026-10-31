module MirGhost
    ( eraseGhosts
    , ghostType
    , withoutUninit
    ) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Mir
import Pretty (renderType)
import TersusTypes (Arg (..), Size (..), Type (..), instanceName, instanceOf)
import Utils

-- Permissions (`Block<T>`, POINTERS.md) are ghost values: the validator has them, and the program that runs does not. This pass takes them
-- out of a validated program, before anything that runs it or makes native code of it (the executor of the MIR, the ownership pass, the
-- lists of native code and both emitters) sees it:
--
--   * a local, a parameter or a result that is a permission, or a struct or tuple made only of them (`Block::split` gives two), is gone, and
--     so is every statement that gives one a value: the ghost operations (`BlockNew`, `BlockTaken`, ...), a field read of one, a struct of them;
--   * a field of a struct (or a part of a tuple) that is a permission is gone from the struct, so a struct's layout is its runtime fields;
--   * a permission given to an operation or a call is not given;
--   * an operation that runs and gives a permission (`AddrWrite`, `AddrDropValue`, `AddrDropRange`) gives 0 to a local of its own, and a
--     function that returns a permission returns 0.
--
-- The validator has seen every permission used exactly once (MirMoves) and every contract hold, so nothing that runs depends on them.
-- It also checks what only the types say: `Block::cast` is between types of the same size.
eraseGhosts :: Program -> Result Program String
eraseGhosts program =
    checkCasts program `bindResult` \_ ->
        Ok
            program
                { progTypes = Map.map eraseDecl (progTypes program)
                , progGenerics = Map.map (\(params, fields) -> (params, [(f, t) | (f, t) <- fields, not (ghostType program t)])) (progGenerics program)
                , progFunctions = Map.map (eraseFunction program) (progFunctions program)
                , progMain = eraseFunction program (progMain program)
                }
  where
    eraseDecl decl = case decl of
        StructDecl fields -> StructDecl (runtimeFields fields)
        EnumDecl variants -> EnumDecl [(v, runtimeFields fields) | (v, fields) <- variants]
    runtimeFields fields = [(f, t) | (f, t) <- fields, not (ghostType program t)]

-- Whether a value of the type exists only for the validator: a permission, or a struct whose fields all are (and that has some)
ghostType :: Program -> Type -> Bool
ghostType program = go (0 :: Int)
  where
    go depth ty
        | depth > 16 = False
        | otherwise = case ty of
            TBlock _ -> True
            TNamed n -> case Map.lookup n (progTypes program) of
                Just (StructDecl fields@(_ : _)) -> all (go (depth + 1) . snd) fields
                _ -> False
            _ -> False

eraseFunction :: Program -> Function -> Function
eraseFunction program fn =
    fn
        { fnParams = filter (not . ghost) (fnParams fn)
        , fnBorrowed = filter (not . ghost) (fnBorrowed fn)
        , fnReturns = fmap returnType (fnReturns fn)
        , fnLocals = Map.union retargets (Map.mapWithKey keepLocal (Map.filterWithKey (\l _ -> not (ghost l) || l == Local 0) (fnLocals fn)))
        , fnBlocks = Map.map eraseBlock blocks
        , fnSpec = (fnSpec fn){specEnv = scrub (specEnv (fnSpec fn)), specLoops = Map.map (\ls -> ls{loopEnv = scrub (loopEnv ls)}) (specLoops (fnSpec fn))}
        }
  where
    ghostLocals = Set.fromList [l | (l, d) <- Map.toList (fnLocals fn), ghostType program (localType d)]
    ghost l = l `Set.member` ghostLocals
    returnType t = if ghostType program t then TInt else t
    -- (the return slot of a function that returns a permission holds 0)
    keepLocal l d = if l == Local 0 && ghost l then d{localType = TInt} else d
    -- an operation that runs and gives the permission after gives its 0 to a local of its own; a call that gives one, too
    firstFree = 1 + maximum (0 : [n | Local n <- Map.keys (fnLocals fn)])
    (blocks, retargets) = foldl' retargetBlock (fnBlocks fn, Map.empty) (Map.keys (fnBlocks fn))
    retargetBlock (bs, new) b = case Map.lookup b bs of
        Nothing -> (bs, new)
        Just (BasicBlock stmts term) ->
            let (stmts', new') = foldl' retargetStatement ([], new) stmts
                (term', new'') = retargetCall term new'
             in (Map.insert b (BasicBlock (reverse stmts') term') bs, new'')
    retargetStatement (acc, new) stmt = case stmt of
        Assign d rv@(ListOp op _) | ghost d, d /= Local 0, not (ghostOp op) ->
            let l = Local (firstFree + Map.size new)
             in (Assign l rv : acc, Map.insert l (LocalDecl TInt Nothing) new)
        _ -> (stmt : acc, new)
    retargetCall term new = case term of
        Call callee args d next | ghost d, d /= Local 0 ->
            let l = Local (firstFree + Map.size new)
             in (Call callee args l next, Map.insert l (LocalDecl TInt Nothing) new)
        _ -> (term, new)
    eraseBlock (BasicBlock stmts term) = BasicBlock (concatMap eraseStatement stmts) (eraseTerminator term)
    eraseStatement stmt = case stmt of
        Assign (Local 0) rv | ghost (Local 0) -> case rv of
            ListOp op os | not (ghostOp op) -> [Assign (Local 0) (ListOp op (runtime os))]
            _ -> [Assign (Local 0) (Use (Const (CInt 0)))]
        Assign d _ | ghost d -> []
        Assign d rv -> [Assign d (eraseRvalue rv)]
        -- (a value taken apart is used up: its bytes are cleared, which native code takes for a value that was moved out, so its drop does not run)
        Ghost _ (GhostDissolve l) | not (ghost l) -> [Peek l (ListOp UninitEmpty [])]
        Ghost env g -> [Ghost (scrub env) g]
        _ -> [stmt]
    eraseRvalue rv = case rv of
        ListOp op os -> ListOp op (runtime os)
        MakeData name fields -> MakeData name [(f, o) | (f, o) <- fields, not (ghostOperand o)]
        _ -> rv
    eraseTerminator term = case term of
        Call callee args d next -> Call callee (runtime args) d next
        _ -> term
    runtime = filter (not . ghostOperand)
    ghostOperand o = case o of
        Copy l -> ghost l
        Move l -> ghost l
        Const _ -> False
    scrub = Map.filter (not . ghostOperand)

-- `Block::cast(b)` gives the permission to the same memory as slots of another type, which have to take as many bytes as those of the
-- first, and be aligned no more strictly. The validator does not see types, so it is checked here, where every type is known.
checkCasts :: Program -> Result () String
checkCasts program = case concatMap castsOf (progMain program : Map.elems (progFunctions program)) of
    [] -> Ok ()
    problem : _ -> Error ("Validation failed: " ++ problem)
  where
    castsOf fn =
        [ "in " ++ fnName fn ++ ": Block::cast from " ++ renderType from ++ " to " ++ renderType to ++ ", whose slots are not the same size, or are aligned more strictly (" ++ show (layoutOf program from) ++ " and " ++ show (layoutOf program to) ++ ", as bytes and alignment)"
        | BasicBlock stmts _ <- Map.elems (fnBlocks fn)
        , Assign d (ListOp BlockCast [o]) <- stmts
        , Just (TBlock to) <- [localType <$> Map.lookup d (fnLocals fn)]
        , Just source <- [operandLocalOf o]
        , Just (TBlock from) <- [localType <$> Map.lookup source (fnLocals fn)]
        , sizeOf program from /= sizeOf program to || alignOf program to > alignOf program from
        ]
            ++ [ "in " ++ fnName fn ++ ": Block::cast from " ++ renderType from ++ " to " ++ renderType to ++ ", where the layout of a type parameter or a size parameter is not known"
               | BasicBlock stmts _ <- Map.elems (fnBlocks fn)
               , Assign d (ListOp BlockCast [o]) <- stmts
               , Just (TBlock to) <- [localType <$> Map.lookup d (fnLocals fn)]
               , Just source <- [operandLocalOf o]
               , Just (TBlock from) <- [localType <$> Map.lookup source (fnLocals fn)]
               , not (knownLayout from && knownLayout to)
               ]
    -- (the layout of a generic type is that of each instance, so a cast in a generic function is checked only where nothing in it is a parameter)
    knownLayout = go (0 :: Int)
      where
        go depth ty
            | depth > 16 = True
            | otherwise = case ty of
                TParam _ -> False
                TArrayOf t (SizeConst _) -> go (depth + 1) t
                TArrayOf _ _ -> False
                TList t -> go (depth + 1) t
                TBox t -> go (depth + 1) t
                TAddr t -> go (depth + 1) t
                TBlock t -> go (depth + 1) t
                TUninit t -> go (depth + 1) t
                TNamed n -> case instanceOf n of
                    Just (_, args) -> and [go (depth + 1) t | ArgType t <- args] && and [False | ArgSize s <- args, not (constSize s)]
                    Nothing -> fieldsKnown depth n
                _ -> True
        fieldsKnown depth n = case Map.lookup n (progTypes program) of
            Just (StructDecl fields) -> all (go (depth + 1) . snd) fields
            Just (EnumDecl variants) -> and [go (depth + 1) t | (_, fields) <- variants, (_, t) <- fields]
            Nothing -> True
        constSize s = case s of
            SizeConst _ -> True
            _ -> False
    operandLocalOf o = case o of
        Copy l -> Just l
        Move l -> Just l
        Const _ -> Nothing

-- An Uninit<T> is laid out as a T (POINTERS.md, Uninit): native code is made of the program with each Uninit<T> a T, in every type and in the
-- name of every struct made with one. Its operations are kept (an empty one is the words of a T cleared, which own nothing, and the others
-- are the value as it is), and the validator has proved that nothing reads an empty one.
withoutUninit :: Program -> Program
withoutUninit program =
    program
        { progTypes = Map.fromList [(name n, decl d) | (n, d) <- Map.toList (progTypes program)]
        , progGenerics = Map.map (\(params, fields) -> (params, [(f, plain t) | (f, t) <- fields])) (progGenerics program)
        , progFunctions = Map.map function (progFunctions program)
        , progMain = function (progMain program)
        }
  where
    decl d = case d of
        StructDecl fields -> StructDecl [(f, plain t) | (f, t) <- fields]
        EnumDecl variants -> EnumDecl [(v, [(f, plain t) | (f, t) <- fields]) | (v, fields) <- variants]
    function fn =
        fn
            { fnLocals = Map.map (\d -> d{localType = plain (localType d)}) (fnLocals fn)
            , fnReturns = fmap plain (fnReturns fn)
            , fnBlocks = Map.map (\(BasicBlock stmts term) -> BasicBlock (map statement stmts) (terminator term)) (fnBlocks fn)
            }
    statement st = case st of
        Assign d rv -> Assign d (rvalue rv)
        AssignRef root steps rv -> AssignRef root (map refStep steps) (rvalue rv)
        Peek d rv -> Peek d (rvalue rv)
        _ -> st
    terminator term = case term of
        SwitchBool o a b -> SwitchBool (operand o) a b
        Call f args d next -> Call (operand f) (map operand args) d next
        _ -> term
    rvalue rv = case rv of
        Use o -> Use (operand o)
        BinaryOp op a b -> BinaryOp op (operand a) (operand b)
        ListOp op os -> ListOp op (map operand os)
        MakeList os -> MakeList (map operand os)
        MakeBox o -> MakeBox (operand o)
        Unbox o -> Unbox (operand o)
        Unsize o -> Unsize (operand o)
        MakeData n fields -> MakeData (name n) [(f, operand o) | (f, o) <- fields]
        ReadField o n f -> ReadField (operand o) (name n) f
        IsVariant o n -> IsVariant (operand o) (name n)
        AsVariant o n -> AsVariant (operand o) (name n)
        Clone o -> Clone (operand o)
        TakeField l n f -> TakeField l (name n) f
        Borrow root steps mut -> Borrow root (map refStep steps) mut
        Deref o -> Deref (operand o)
    refStep s = case s of
        RefField n f -> RefField (name n) f
        RefIndex o -> RefIndex (operand o)
    operand o = case o of
        Const c -> Const (constant c)
        _ -> o
    constant c = case c of
        CList cs -> CList (map constant cs)
        CArray cs -> CArray (map constant cs)
        CData n fields -> CData (name n) [(f, constant v) | (f, v) <- fields]
        _ -> c
    name n = case instanceOf n of
        Just (base, args) -> instanceName base (map arg args)
        Nothing -> n
    arg a = case a of
        ArgType t -> ArgType (plain t)
        _ -> a

-- The type with each Uninit<T> a T
plain :: Type -> Type
plain ty = case ty of
    TUninit t -> plain t
    TList t -> TList (plain t)
    TArrayOf t size -> TArrayOf (plain t) size
    TBox t -> TBox (plain t)
    TAddr t -> TAddr (plain t)
    TBlock t -> TBlock (plain t)
    TRef t -> TRef (plain t)
    TMutRef t -> TMutRef (plain t)
    TFn args ret -> TFn (map plain args) (plain ret)
    TForall sizes types t -> TForall sizes types (plain t)
    TNamed n | Just (base, args) <- instanceOf n -> TNamed (instanceName base [case a of ArgType t -> ArgType (plain t); _ -> a | a <- args])
    _ -> ty

