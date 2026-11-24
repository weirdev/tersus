module MirThreads
    ( lowerThreads
    ) where

import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)
import qualified Data.Set as Set

import Mir
import MirMoves (isNativeSpawn, mayHoldReference, mayHoldUpdate)
import Types (Arg (..), Name, Type (..), Variable, instanceName, mentionsParameter)
import Utils (Result (..), bindResult)

-- The validator and `eval` run a thread of lib/thread.tersus where it is started (its closure called by spawn, its value kept
-- in the handle). Native code runs it on a thread of its own: this rewrites the library's spawn and join, as linking made
-- them, into calls of the runtime (LlvmRuntime), with nothing but erased Addr operations, extern functions and function
-- constants, so that ownership, the checker and the emitter see ordinary MIR.
--
-- A `Thread<T>` becomes `{ handle: Int, slot: Addr<T> }`. Each copy `<Thread>::spawn[F, T]` moves the closure into a job of
-- its own, allocates the slot and starts `thread$spawn[F, T](job, slot)`, which takes the closure out of the job, frees it,
-- calls it and writes its value into the slot; join waits for the thread, takes the value out of the slot and frees it.
-- A `ScopedThread<T, F>` is the same, but its closure is lent: the job holds the closure's address, and
-- `scopedThread$spawn[T, F]` calls it through that address. Its struct keeps the reference to the closure (`f`), so that
-- ownership, as the check of moves, keeps the closure and what it borrows until the handle is joined.
--
-- That is sound because of what MirMoves.checkSpawns refused: what a Thread's closure holds and what a thread gives hold no
-- reference, and a ScopedThread's closure holds no update reference, so a thread shares nothing that another one writes
-- (the copies are checked again here). Each kind is rewritten only when its struct, its spawn copies and its joins are
-- the library's, letter for letter, and nothing else reads or makes its fields.
lowerThreads :: Program -> Result Program String
lowerThreads program =
    lowerKind program threadKind `bindResult` \withThreads ->
        lowerKind withThreads scopedKind `bindResult` \withScoped ->
            Ok (completeErasedInstances withScoped)

data Kind = Kind
    { kindStruct :: Name
    , kindParams :: [Variable]
    , kindFields :: [(Variable, Type)]
    , kindTrampoline :: Name
    , kindLent :: Bool -- whether spawn is lent its closure (`g: &F`) rather than given it
    }

threadKind :: Kind
threadKind = Kind "Thread" ["T"] [("value", TParam "T")] "thread$spawn" False

scopedKind :: Kind
scopedKind = Kind "ScopedThread" ["T", "F"] [("value", TParam "T"), ("f", TRef (TParam "F"))] "scopedThread$spawn" True

-- What a spawn copy is: the closure's type, the result's, and the function that calls the closure
data Spawn = Spawn
    { spawnClosure :: Type
    , spawnResult :: Type
    , spawnCall :: Name
    }

spawnExtern, joinExtern :: Name
spawnExtern = "extern tersus_thread_spawn"
joinExtern = "extern tersus_thread_join"

lowerKind :: Program -> Kind -> Result Program String
lowerKind program kind
    | not (any (isNativeSpawn . fst) spawns) = Ok program
    | not (all (isNativeSpawn . fst) spawns) = unsupported
    | Map.lookup (kindStruct kind) (progGenerics program) /= Just (kindParams kind, kindFields kind) = unsupported
    | not (all (isJust . snd) spawns && all (isLibraryJoin kind) joins) = unsupported
    | any (not . shares) [s | (_, Just s) <- spawns] = unsupported
    | any touchesFields others = Error ("Native " ++ kindStruct kind ++ " handles can only be created by spawn and opened by join")
    | maybe False (containsHandle Set.empty) (fnReturns (progMain program)) =
        Error ("The program cannot return a " ++ kindStruct kind ++ " handle; join it before returning")
    | otherwise =
        Ok program
            { progGenerics = Map.insert (kindStruct kind) (kindParams kind, nativeFields) (progGenerics program)
            , progTypes = Map.filterWithKey (\name _ -> not (isInstance name)) (progTypes program)
            , progFunctions =
                Map.unions
                    [ Map.fromList [(fnName fn, spawnBody kind fn s) | (fn, Just s) <- spawns]
                    , Map.fromList [(fnName t, t) | (fn, Just s) <- spawns, let t = trampoline kind fn s]
                    , Map.fromList [(fnName fn, joinBody fn) | fn <- joins]
                    , Map.fromList [(fnName e, e) | e <- [spawnExternFn, joinExternFn]]
                    , progFunctions program
                    ]
            }
  where
    nativeFields = [("handle", TInt), ("slot", TAddr (TParam "T"))] ++ [("f", TRef (TParam "F")) | kindLent kind]
    spawnPrefix = "<" ++ kindStruct kind ++ ">::spawn"
    joinPrefix = "<" ++ kindStruct kind ++ ">::join"
    functions = Map.elems (progFunctions program)
    spawns = [(fn, librarySpawn kind fn) | fn <- functions, (spawnPrefix ++ "[") `isPrefixOf` fnName fn]
    joins = [fn | fn <- functions, fnName fn == joinPrefix || (joinPrefix ++ "[") `isPrefixOf` fnName fn]
    lowered = map fnName (map fst spawns ++ joins)
    others = progMain program : [fn | fn <- functions, fnName fn `notElem` lowered]
    shares s
        | kindLent kind = not (mayHoldReference program (spawnResult s)) && not (mayHoldUpdate program (spawnClosure s))
        | otherwise = not (mayHoldReference program (spawnResult s)) && not (mayHoldReference program (spawnClosure s))
    isInstance name = name == kindStruct kind || (kindStruct kind ++ "<") `isPrefixOf` name
    unsupported = Error ("Cannot lower the thread library's " ++ kindStruct kind ++ " operations to native code")
    containsHandle seen ty = case ty of
        TNamed base args -> named (instanceName base args)
        TVariant variant -> maybe False named (ownerOf program variant)
        TArrayOf element _ -> containsHandle seen element
        TUninit inner -> containsHandle seen inner
        _ -> False
      where
        named name
            | isInstance name = True
            | Set.member name seen = False
            | otherwise = case Map.lookup name (progTypes program) of
                Just (StructDecl fields) -> any inside fields
                Just (EnumDecl variants) -> any (any inside . snd) variants
                Nothing -> False
          where
            inside = containsHandle (Set.insert name seen) . snd
    touchesFields fn = any (blockTouches isInstance) (Map.elems (fnBlocks fn))

-- The spawn copy, when its body is the library's: it calls the closure it is given (or lent), and gives the struct of the value
-- (with, for a ScopedThread, the loan of the closure). Only a copy for concrete types is run on a thread.
librarySpawn :: Kind -> Function -> Maybe Spawn
librarySpawn kind fn = case (fnParams fn, fnReturns fn, map plainBlock (Map.toList (fnBlocks fn))) of
    ([p1], Just (TNamed base args), [(BlockId 0, BasicBlock [] (Call (Const (CFn callee)) [arg] r (BlockId 1))), (BlockId 1, BasicBlock built Return)])
        | p1 == Local 1
        , r == Local 2
        , base == kindStruct kind
        , operandLocal arg == Just p1
        , null (fnTypeParams fn)
        , not (any mentionsParameter (Map.elems types))
        , Map.keys types == map Local [0 .. if kindLent kind then 3 else 2]
        , Just closure <- Map.lookup p1 types
        , Just result <- Map.lookup r types
        , args == [ArgType result | not (kindLent kind)] ++ [ArgType a | kindLent kind, a <- [result, closure]]
        , (kindLent kind && fnBorrowed fn == [p1]) || (not (kindLent kind) && null (fnBorrowed fn))
        , built == libraryMake (instanceName base args) ->
            Just (Spawn closure result callee)
    _ -> Nothing
  where
    types = Map.map localType (fnLocals fn)
    libraryMake name
        | kindLent kind = [Assign (Local 3) (Borrow (Local 1) [] False), Assign (Local 0) (MakeData name [("value", Copy (Local 2)), ("f", Copy (Local 3))])]
        | otherwise = [Assign (Local 0) (MakeData name [("value", Copy (Local 2))])]

-- join takes the value out of the struct it is given, and gives it
isLibraryJoin :: Kind -> Function -> Bool
isLibraryJoin kind fn = case (fnParams fn, Map.lookup (Local 1) types, map plainBlock (Map.toList (fnBlocks fn))) of
    ([Local 1], Just (TNamed base args), [(BlockId 0, BasicBlock [Assign (Local 0) (ReadField arg name "value")] Return)]) ->
        base == kindStruct kind && name == instanceName base args && operandLocal arg == Just (Local 1) && Map.size types == 2
    _ -> False
  where
    types = Map.map localType (fnLocals fn)

spawnBody :: Kind -> Function -> Spawn -> Function
spawnBody kind fn s =
    fn
        { fnLocals = Map.fromList (zip (map Local [0 ..]) (map plain (spawnTypes ++ [TInt, TInt, TInt])))
        , fnBlocks =
            Map.fromList
                [ (BlockId 0, BasicBlock (startJob ++ [Assign slot (alloc1), Assign jobInt (ListOp AddrToInt [Copy job]), Assign slotInt (ListOp AddrToInt [Copy slot])]) (Call (Const (CFn spawnExtern)) [Const (CFn (trampolineName kind fn)), Copy jobInt, Copy slotInt] handle (BlockId 1)))
                , (BlockId 1, BasicBlock [Assign (Local 0) (MakeData (instanceName (kindStruct kind) structArgs) ([("handle", Copy handle), ("slot", Copy slot)] ++ [("f", Copy (Local 3)) | kindLent kind]))] Return)
                ]
        , fnSpec = quiet (fnSpec fn)
        }
  where
    structArgs = [ArgType (spawnResult s)] ++ [ArgType (spawnClosure s) | kindLent kind]
    held = jobType kind s
    -- _0 the struct, _1 the closure, _2 the job, _3 what is held in it (when that is the closure's address), then the write's
    -- value, the slot, the two addresses as numbers and the handle
    spawnTypes = [TNamed (kindStruct kind) structArgs, spawnClosure s, TAddr held] ++ [held | kindLent kind] ++ [TInt, TAddr (spawnResult s)]
    alloc1 = ListOp AddrAlloc [Const (CInt 1)]
    offset = if kindLent kind then 1 else 0
    job = Local 2
    written = Local (3 + offset)
    slot = Local (4 + offset)
    jobInt = Local (5 + offset)
    slotInt = Local (6 + offset)
    handle = Local (7 + offset)
    startJob
        | kindLent kind = [Assign job alloc1, Assign (Local 3) (Borrow (Local 1) [] False), Assign written (ListOp AddrWrite [Copy job, Const (CInt 0), Copy (Local 3)])]
        | otherwise = [Assign job alloc1, Assign written (ListOp AddrWrite [Copy job, Const (CInt 0), Copy (Local 1)])]

-- What the job holds: the closure, or the address of the closure that is lent
jobType :: Kind -> Spawn -> Type
jobType kind s = if kindLent kind then TRef (spawnClosure s) else spawnClosure s

trampolineName :: Kind -> Function -> Name
trampolineName kind fn = kindTrampoline kind ++ drop (length ("<" ++ kindStruct kind ++ ">::spawn")) (fnName fn)

-- The function the thread runs: (job, slot) -> 0
trampoline :: Kind -> Function -> Spawn -> Function
trampoline kind fn s =
    (plainFunction (trampolineName kind fn) [Local 1, Local 2] TInt [TInt, TInt, TInt, TAddr held, held, TInt, spawnResult s, TAddr (spawnResult s), TInt])
        { fnBlocks =
            Map.fromList
                [ (BlockId 0, BasicBlock [Assign (Local 3) (ListOp AddrFromInt [Copy (Local 1)]), Assign (Local 4) (ListOp AddrTake [Copy (Local 3), Const (CInt 0)]), Assign (Local 5) (ListOp AddrFree [Copy (Local 3)])] (Call (Const (CFn (spawnCall s))) [Copy (Local 4)] (Local 6) (BlockId 1)))
                , (BlockId 1, BasicBlock [Assign (Local 7) (ListOp AddrFromInt [Copy (Local 2)]), Assign (Local 8) (ListOp AddrWrite [Copy (Local 7), Const (CInt 0), Copy (Local 6)]), Assign (Local 0) (Use (Const (CInt 0)))] Return)
                ]
        }
  where
    held = jobType kind s

-- join: the thread waited for, its value taken out of the slot, the slot freed
joinBody :: Function -> Function
joinBody fn =
    fn
        { fnLocals = Map.fromList (zip (map Local [0 ..]) (map plain [result, struct, TInt, TAddr result, TInt, TInt]))
        , fnBlocks =
            Map.fromList
                [ (BlockId 0, BasicBlock [Assign (Local 2) (ReadField (Copy (Local 1)) name "handle"), Assign (Local 3) (ReadField (Copy (Local 1)) name "slot")] (Call (Const (CFn joinExtern)) [Copy (Local 2)] (Local 4) (BlockId 1)))
                , (BlockId 1, BasicBlock [Assign (Local 0) (ListOp AddrTake [Copy (Local 3), Const (CInt 0)]), Assign (Local 5) (ListOp AddrFree [Copy (Local 3)])] Return)
                ]
        , fnSpec = quiet (fnSpec fn)
        }
  where
    result = maybe TInt id (fnReturns fn)
    struct = maybe TInt localType (Map.lookup (Local 1) (fnLocals fn))
    name = case struct of
        TNamed base args -> instanceName base args
        _ -> ""

spawnExternFn, joinExternFn :: Function
spawnExternFn = externFunction spawnExtern [TFn [TInt, TInt] TInt, TInt, TInt]
joinExternFn = externFunction joinExtern [TInt]

externFunction :: Name -> [Type] -> Function
externFunction name params =
    (plainFunction name (map Local [1 .. length params]) TInt (TInt : params)){fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] Unreachable)}

plainFunction :: Name -> [Local] -> Type -> [Type] -> Function
plainFunction name params ret types = Function name params (Just ret) (Map.fromList (zip (map Local [0 ..]) (map plain types))) Map.empty [] [] [] [] [] emptySpec

plain :: Type -> LocalDecl
plain ty = LocalDecl ty Nothing

-- (what the library's contracts say of the value is the validator's, which has used them)
quiet :: FunctionSpec -> FunctionSpec
quiet spec = spec{specRequires = [], specEnsures = []}

plainBlock :: (BlockId, BasicBlock) -> (BlockId, BasicBlock)
plainBlock (b, BasicBlock stmts term) = (b, BasicBlock [s | s <- stmts, not (ghost s)] term)
  where
    ghost Ghost{} = True
    ghost _ = False

operandLocal :: Operand -> Maybe Local
operandLocal o = case o of
    Copy l -> Just l
    Move l -> Just l
    Const _ -> Nothing

-- Whether a block makes or reads a struct of the names, or a constant of one
blockTouches :: (Name -> Bool) -> BasicBlock -> Bool
blockTouches named (BasicBlock stmts term) = any statement stmts || any operand (terminatorOperands term)
  where
    statement s = case s of
        Assign _ rv -> rvalue rv
        Peek _ rv -> rvalue rv
        AssignRef _ steps rv -> any step steps || rvalue rv
        _ -> False
    rvalue rv = case rv of
        MakeData name fields -> named name || any (operand . snd) fields
        ReadField o name _ -> named name || operand o
        TakeField _ name _ -> named name
        IsVariant o name -> named name || operand o
        AsVariant o name -> named name || operand o
        Borrow _ steps _ -> any step steps
        Use o -> operand o
        BinaryOp _ a b -> operand a || operand b
        ListOp _ os -> any operand os
        MakeList os -> any operand os
        MakeBox o -> operand o
        Unbox o -> operand o
        Unsize o -> operand o
        CopyOf o -> operand o
        Deref o -> operand o
    step st = case st of
        RefField name _ -> named name
        RefIndex o -> operand o
    operand o = case o of
        Const c -> constant c
        _ -> False
    constant c = case c of
        CData name fields -> named name || any (constant . snd) fields
        CList cs -> any constant cs
        CArray cs -> any constant cs
        _ -> False
    terminatorOperands t = case t of
        SwitchBool o _ _ -> [o]
        Call callee args _ _ -> callee : args
        _ -> []
