module MirOwnership
    ( insertOwnership
    , needsDrop
    , Role (..)
    , roles
    , isProjection
    , operandLocal
    ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, listToMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Mir
import MirMono (monomorphize)
import TersusTypes (Name, Type (..), Variable)

-- Native code frees what a program makes, and updates a list in place, so it needs to know who owns each list and each
-- struct or enum value. This pass makes that explicit in the MIR, after the program is validated, and without changing what
-- the program means (the executor of the MIR runs the result and gives the same answers).
--
-- Every value on the heap (a list, a struct or an enum value) has exactly one owner: a local, a slot of another value, or a
-- temporary on its way somewhere. So the heap is a forest, a value can be freed with what is in it, and `push` and `set` can
-- change the list they are given when it is theirs and nothing else uses it. Where a value is wanted by two, one gets a
-- copy.
--
-- What an operand does with a value of the heap decides what happens to the local:
--
--   * It reads it (`size`, `==`, `is`, the list of a `get`): nothing happens.
--   * It takes it (`y = x`, `push(x, v)` and `set` for the list and the element, a call, a list or a struct that is made,
--     the return value): the local gives it up. If the local is not used again that is a `Move`, and otherwise the operand
--     is a `Clone` of the local, which nothing else shares.
--
-- Every parameter is owned by the function, and a function returns what it owns, so a call is the same wherever the
-- function came from.
--
-- A value read out of a list, a struct or an enum (`get`, `first`, `last`, a field) is part of what contains it:
--
--   * A field of a value that is not used again is `TakeField`n out of it: a `match` takes the value apart. What is left in
--     the value is freed with it.
--   * A temporary that is only read, by statements that follow it in the same block and before anything takes or changes
--     what it was read from, `Peek`s at the value. It owns nothing, so it is not freed and costs nothing.
--   * Otherwise it is a `Clone`.
--
-- A local is freed (`Drop`) when it is assigned, and all that a function owns when it returns. A local that has been moved
-- from holds nothing, and dropping that does nothing.

insertOwnership :: Program -> Program
insertOwnership validated =
    program
        { progFunctions = Map.map (ownFunction program) (progFunctions program)
        , progMain = ownFunction program (progMain program)
        }
  where
    -- (a function with size parameters is made into a copy for each list of sizes it is called with, since native code needs them)
    program = monomorphize validated

-- What is used of a local: all of it, the tag that says which variant it is, or one field
data Key = Whole | Tag | Field Name Variable
    deriving (Eq, Ord)

type Live = Set (Local, Key)

data Role = Read | Consume
    deriving (Eq)

-- Whether a value of the type owns something to free: a list or a Box, or a struct, an enum or an array that holds one. A value that
-- owns nothing (a number, a Bool, a function, and a struct, an enum or an array of them) is plain: it is copied where it is wanted
-- and needs no care. A type that contains itself does so through a Box, which owns.
needsDrop :: Program -> Type -> Bool
needsDrop program = owning
  where
    owning ty = case ty of
        TBox{} -> True
        TArrayOf t _ -> owning t
        TNamed n -> declared n
        TVariant v -> maybe False declared (ownerOf v)
        _ -> False
    -- (the struct that a list is made of owns the memory at its address, which the runtime frees and copies with the elements in use)
    declared n | takeWhile (/= '<') n == "StdList" = True
    -- (a struct or an enum with a drop has something to do when it is freed, whatever its fields are)
    declared n | Just _ <- dropFunction program n = True
    declared n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> any (owning . snd) fields
        Just (EnumDecl variants) -> any (owning . snd) (concatMap snd variants)
        Nothing -> False
    -- (a struct is its own constructor, and a cast to it has the type of a variant of it)
    ownerOf v = case Map.lookup v (progTypes program) of
        Just StructDecl{} -> Just v
        _ -> listToMaybe [n | (n, EnumDecl variants) <- Map.toList (progTypes program), v `elem` map fst variants]

heap :: Ctx -> Type -> Bool
heap cx = needsDrop (cxProgram cx)

-- The operands of an rvalue, and what is done with the value of each
roles :: Rvalue -> [(Operand, Role)]
roles rv =
    case rv of
        Use o -> [(o, Consume)]
        BinaryOp _ a b -> [(a, Read), (b, Read)]
        ListOp Push [l, x] -> [(l, Consume), (x, Consume)]
        ListOp Pop [l] -> [(l, Consume)]
        ListOp Set [l, i, x] -> [(l, Consume), (i, Read), (x, Consume)]
        -- (a value written to memory is moved there; a permission that an operation changes is taken by it, and one it only looks at is lent)
        ListOp AddrWrite (p : i : x : rest) -> [(p, Read), (i, Read), (x, Consume)] ++ [(b, Consume) | b <- rest]
        ListOp AddrDropValue [p, i, b] -> [(p, Read), (i, Read), (b, Consume)]
        ListOp AddrDropRange [p, i, n, b] -> [(p, Read), (i, Read), (n, Read), (b, Consume)]
        ListOp AddrFree [p, b] -> [(p, Read), (b, Consume)]
        ListOp op (b : rest) | op `elem` [BlockTaken, BlockResized, BlockSplitHi, BlockCast] -> (b, Consume) : [(o, Read) | o <- rest]
        ListOp BlockJoin os -> [(o, Consume) | o <- os]
        ListOp op [u] | op `elem` [UninitNew, UninitTake, UninitDiscard] -> [(u, Consume)]
        ListOp _ os -> [(o, Read) | o <- os]
        MakeList os -> [(o, Consume) | o <- os]
        MakeBox o -> [(o, Consume)]
        Unbox o -> [(o, Consume)]
        Unsize o -> [(o, Consume)]
        MakeData _ fields -> [(o, Consume) | (_, o) <- fields]
        ReadField o _ _ -> [(o, Read)]
        IsVariant o _ -> [(o, Read)]
        AsVariant o _ -> [(o, Consume)]
        Clone o -> [(o, Read)]
        TakeField l _ _ -> [(Copy l, Read)]

-- The rvalues that read a part of a value
isProjection :: Rvalue -> Bool
isProjection (ListOp op _) = op `elem` [First, Last, Get, AddrGet, UninitGet]
isProjection ReadField{} = True
isProjection _ = False

-- The value a projection reads from
projectionSource :: Rvalue -> Maybe Operand
projectionSource (ListOp _ (l : _)) = Just l
projectionSource (ReadField o _ _) = Just o
projectionSource _ = Nothing

mentions :: Local -> Operand -> Bool
mentions l (Copy m) = l == m
mentions l (Move m) = l == m
mentions _ _ = False

operandLocal :: Operand -> Maybe Local
operandLocal (Copy l) = Just l
operandLocal (Move l) = Just l
operandLocal _ = Nothing

-- Liveness: which locals, and which parts of them, a program still uses after a point

stmtUses :: Statement -> Live
stmtUses (Assign _ rv) = rvalueUses rv
stmtUses _ = Set.empty

rvalueUses :: Rvalue -> Live
rvalueUses rv =
    case rv of
        ReadField (Copy l) name field -> Set.singleton (l, Field name field)
        IsVariant (Copy l) _ -> Set.singleton (l, Tag)
        _ -> Set.fromList [(l, Whole) | (o, _) <- roles rv, Just l <- [operandLocal o]]

stmtDef :: Statement -> Maybe Local
stmtDef (Assign d _) = Just d
stmtDef (Peek d _) = Just d
stmtDef _ = Nothing

termUses :: Terminator -> Live
termUses term =
    case term of
        SwitchBool o _ _ -> opUses o
        Call callee args _ _ -> Set.unions (map opUses (callee : args))
        Return -> Set.singleton (Local 0, Whole)
        _ -> Set.empty
  where
    opUses o = Set.fromList [(l, Whole) | Just l <- [operandLocal o]]

termDef :: Terminator -> Maybe Local
termDef (Call _ _ d _) = Just d
termDef _ = Nothing

forgetLocal :: Local -> Live -> Live
forgetLocal d = Set.filter ((/= d) . fst)

stepStmt :: Statement -> Live -> Live
stepStmt st after = Set.union (stmtUses st) (maybe id forgetLocal (stmtDef st) after)

stepTerm :: Terminator -> Live -> Live
stepTerm term after = Set.union (termUses term) (maybe id forgetLocal (termDef term) after)

-- What is live when each block ends
liveOuts :: Function -> Map BlockId Live
liveOuts fn = go (Map.map (const Set.empty) (fnBlocks fn))
  where
    go outs =
        let ins = Map.mapWithKey (\b (BasicBlock stmts term) -> foldr stepStmt (stepTerm term (outs Map.! b)) stmts) (fnBlocks fn)
            outs' = Map.map (\(BasicBlock _ term) -> Set.unions [Map.findWithDefault Set.empty s ins | s <- successors term]) (fnBlocks fn)
         in if outs' == outs then outs else go outs'

localsOf :: Live -> Set Local
localsOf = Set.map fst

-- What is known about a function while its blocks are rewritten
data Ctx = Ctx
    { cxProgram :: Program
    , cxTypes :: Map Local Type
    , cxProjected :: Set Local -- the locals that a projection gives a value to
    , cxDefs :: Map Local Int -- how many statements and calls assign it
    , cxStatements :: Map BlockId [Statement]
    , cxUses :: Map Local [(BlockId, Int, Role)] -- the uses of a local by statements
    , cxUsedByTerminator :: Set Local
    , cxTakes :: Set (BlockId, Int) -- the statements that take a field out of a value
    , cxBorrowed :: Set Local -- the parameters that are lent: the function does not own them, so it never frees or moves them
    }

typeOf :: Ctx -> Local -> Type
typeOf cx l = Map.findWithDefault TInt l (cxTypes cx)

ownFunction :: Program -> Function -> Function
ownFunction program fn0 =
    let fn = fuseCasts fn0
        outs = liveOuts fn
        statements = Map.map blockStatements (fnBlocks fn)
        -- (a parameter has a value from the start, so what is assigned to it is a second one)
        defsOf = Map.fromListWith (+) ([(d, 1 :: Int) | BasicBlock stmts _ <- Map.elems (fnBlocks fn), Just d <- map stmtDef stmts] ++ [(d, 1) | BasicBlock _ (Call _ _ d _) <- Map.elems (fnBlocks fn)] ++ [(p, 1) | p <- fnParams fn])
        types = Map.map localType (fnLocals fn)
        projected =
            Set.fromList
                [ d
                | BasicBlock stmts _ <- Map.elems (fnBlocks fn)
                , Assign d rv <- stmts
                , isProjection rv
                , maybe False (needsDrop program) (Map.lookup d types)
                ]
        usesOf =
            Map.fromListWith
                (flip (++))
                [ (l, [(b, k, role)])
                | (b, BasicBlock stmts _) <- Map.toList (fnBlocks fn)
                , (k, Assign _ rv) <- zip [0 ..] stmts
                , (o, role) <- roles rv
                , Just l <- [operandLocal o]
                ]
        byTerminator =
            Set.fromList [l | BasicBlock _ term <- Map.elems (fnBlocks fn), (l, _) <- Set.toList (termUses term)]
        cx0 =
            Ctx
                { cxProgram = program
                , cxTypes = types
                , cxProjected = projected
                , cxDefs = defsOf
                , cxStatements = statements
                , cxUses = usesOf
                , cxUsedByTerminator = byTerminator
                , cxTakes = Set.empty
                , cxBorrowed = Set.fromList (fnBorrowed fn)
                }
        takes =
            Set.fromList
                [ (b, k)
                | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn)
                , let afters = tail (scanr stepStmt (stepTerm term (outs Map.! b)) stmts)
                , (k, st, after) <- zip3 [0 ..] stmts afters
                , takesField cx0 st after
                ]
        cx = cx0{cxTakes = takes}
        start = 1 + maximum (0 : [n | Local n <- Map.keys (fnLocals fn)])
        (blocks, finalState) =
            runR (mapM (rewriteBlock cx outs) (Map.toList (fnBlocks fn))) (RS start Map.empty Set.empty)
        allLocals = Map.union (fnLocals fn) (rsNew finalState)
        owned = [l | (l, d) <- Map.toList allLocals, needsDrop program (localType d), l /= Local 0, l `Set.notMember` rsAlias finalState, l `Set.notMember` cxBorrowed cx, not (dropped l)]
        -- (the drop of a type is given the value to free: native code frees what its fields own after it, so the drop does not free it)
        dropped l = isDropFunction (fnName fn) && take 1 (fnParams fn) == [l]
        nextBlock = 1 + maximum (0 : [n | BlockId n <- map fst blocks])
        (allLocals', blocks') = elaborateDrops program fn (Set.fromList owned) allLocals (Map.fromList blocks) (rsNext finalState) nextBlock
     in fn{fnLocals = allLocals', fnBlocks = blocks'}

-- Whether a local that owns something still holds it at a point, and whether each field of it that owns something
-- is still in it: a part holds nothing (it was never given a value, or what it held was moved out, taken out or
-- dropped), it holds a value on every path to the point, or it may hold one (the paths differ). The pass works this
-- out over the blocks of a function and only says to drop a part where it may hold a value, so a drop never has to
-- look at the bytes of the value to tell whether it is there. Where the paths differ a flag local keeps the answer
-- instead: it is given the value of the state whenever the part is given a value, is moved or taken from, or is
-- dropped, and the drop at a return is made under a test of it. A local whose fields were taken out in part is
-- dropped field by field at the return (each one that is still in it is taken out and dropped on its own), so what
-- is left of it is freed without its drop, as a value that is taken apart is.
data OwnState = Empty | Owned | MaybeOwned
    deriving (Eq, Show)

joinOwn :: OwnState -> OwnState -> OwnState
joinOwn a b
    | a == b = a
    | otherwise = MaybeOwned

-- A whole local, or one field of one (the name of its constructor and the field)
type OwnKey = (Local, Maybe (Name, Variable))

type OwnStates = Map OwnKey OwnState

-- (a field that was taken out is in the state holding nothing, which says more than a field that is not in the
-- state at all: that one is as the whole of it is)
ownStates :: OwnStates -> OwnStates
ownStates = Map.filterWithKey (\k state -> state /= Empty || isJust (snd k))

-- (a part that is not in a state holds nothing in it, and a field that is not in it is as the whole of it is, so a
-- join looks at every part that either side names, and asks for a field of the whole of the other side)
joinOwnStates :: OwnStates -> OwnStates -> OwnStates
joinOwnStates a b =
    ownStates
        ( Map.fromList
            [ (k, joinOwn (look a k) (look b k))
            | k <- Set.toList (Map.keysSet a `Set.union` Map.keysSet b)
            ]
        )
  where
    look states (l, Nothing) = Map.findWithDefault Empty (l, Nothing) states
    look states (l, Just field) =
        case Map.lookup (l, Just field) states of
            Just state -> state
            Nothing -> Map.findWithDefault Empty (l, Nothing) states

stateOf :: Set Local -> OwnStates -> OwnKey -> OwnState
stateOf tracked states k@(l, _)
    | l `Set.member` tracked = Map.findWithDefault Empty k states
    | otherwise = Empty

-- The state of a field that no take has named: what the state of the whole says
fieldStateOf :: Set Local -> OwnStates -> Local -> (Name, Variable) -> OwnState
fieldStateOf tracked states l key =
    case Map.lookup (l, Just key) states of
        Just state -> state
        Nothing -> stateOf tracked states (l, Nothing)

setState :: Set Local -> OwnKey -> OwnState -> OwnStates -> OwnStates
setState tracked k@(l, _) state states
    | l `Set.member` tracked = ownStates (Map.insert k state states)
    | otherwise = states

-- What a whole value being given, moved or dropped does to the states of its fields
clearFields :: Local -> OwnStates -> OwnStates
clearFields l = Map.filterWithKey (\(m, field) _ -> m /= l || field == Nothing)

movedLocals :: [Operand] -> [Local]
movedLocals operands = [l | Move l <- operands]

statementMoved :: Statement -> [Local]
statementMoved st =
    case st of
        Assign _ rv -> movedLocals [o | (o, _) <- roles rv]
        Peek _ rv -> movedLocals [o | (o, _) <- roles rv]
        _ -> []

terminatorMoved :: Terminator -> [Local]
terminatorMoved term =
    case term of
        Call callee args _ _ -> movedLocals (callee : args)
        SwitchBool o _ _ -> movedLocals [o]
        _ -> []

transferStatement :: Set Local -> OwnStates -> Statement -> OwnStates
transferStatement tracked states st =
    case st of
        Assign d (TakeField s name field) ->
            setState tracked (d, Nothing) Owned (clearFields d (setState tracked (s, Just (name, field)) Empty consumed))
        Assign d _ -> setState tracked (d, Nothing) Owned (clearFields d consumed)
        Drop l -> setState tracked (l, Nothing) Empty (clearFields l states)
        _ -> consumed
  where
    consumed = foldl (\s l -> setState tracked (l, Nothing) Empty (clearFields l s)) states (statementMoved st)

transferTerminator :: Set Local -> OwnStates -> Terminator -> OwnStates
transferTerminator tracked states term =
    case term of
        Call _ _ d _ -> setState tracked (d, Nothing) Owned (clearFields d consumed)
        _ -> consumed
  where
    consumed = foldl (\s l -> setState tracked (l, Nothing) Empty (clearFields l s)) states (terminatorMoved term)

transferBlock :: Set Local -> OwnStates -> BasicBlock -> OwnStates
transferBlock tracked states (BasicBlock stmts term) =
    transferTerminator tracked (foldl (transferStatement tracked) states stmts) term

-- The state of every part at the start of each block, and at the end of it
blockStates :: Function -> Set Local -> Map BlockId BasicBlock -> (Map BlockId OwnStates, Map BlockId OwnStates)
blockStates fn tracked blocks = (ins, outs)
  where
    entry = ownStates (Map.fromList [((p, Nothing), Owned) | p <- fnParams fn, p `Set.member` tracked])
    ins = fixpoint (Map.singleton (BlockId 0) entry)
    outs = Map.mapWithKey (\b block -> transferBlock tracked (Map.findWithDefault Map.empty b ins) block) blocks
    fixpoint known =
        let reached =
                Map.fromListWith
                    joinOwnStates
                    [(s, transferBlock tracked (Map.findWithDefault Map.empty b known) block) | (b, block) <- Map.toList blocks, b `Map.member` known, s <- successors (blockTerminator block)]
            known' = Map.unionWith joinOwnStates known reached
         in if known' == known then known else fixpoint known'

-- The constructors of the type of a local, each with the fields of it that own something, and whether the type has
-- a drop of its own (which a value that is taken apart does not run, so such a value is dropped whole, as before)
type DropShape = [(Name, [(Name, Variable, Type)])]

dropShape :: Program -> Map Local LocalDecl -> Local -> (DropShape, Bool)
dropShape program locals l =
    case localType <$> Map.lookup l locals of
        Just (TNamed n) -> (variantsOf [(n, decl) | decl <- maybe [] (: []) (Map.lookup n (progTypes program))], hasDrop n)
        Just (TVariant v) -> (variantsOf [(n, decl) | (n, decl@(EnumDecl variants)) <- Map.toList (progTypes program), v `elem` map fst variants], maybe False hasDrop (ownerName v))
        _ -> ([], False)
  where
    variantsOf decls = [(ctor, [(ctor, f, t) | (f, t) <- fields, needsDrop program t]) | (ctor, fields) <- concatMap declVariants decls]
    declVariants (n, StructDecl fields) = [(n, fields)]
    declVariants (_, EnumDecl variants) = variants
    hasDrop n = dropFunction program n /= Nothing
    ownerName v = listToMaybe [n | (n, EnumDecl variants) <- Map.toList (progTypes program), v `elem` map fst variants]

-- What drops a local at a return, before the flags and the new locals are known: the whole of it, or the fields of
-- it that are still in it, constructor by constructor
data DropPlan
    = NoDrop
    | WholeDrop
    | FieldsDrop DropShape

dropPlan :: Program -> Map Local LocalDecl -> Set Local -> OwnStates -> Local -> DropPlan
dropPlan program locals tracked state l
    | whole == Empty = NoDrop
    | hasDrop || null shape || allHeld = WholeDrop
    | otherwise = FieldsDrop [(ctor, [(ctor', f, t) | (ctor', f, t) <- fields, fieldStateOf tracked state l (ctor', f) /= Empty]) | (ctor, fields) <- shape]
  where
    whole = stateOf tracked state (l, Nothing)
    (shape, hasDrop) = dropShape program locals l
    allHeld = all (\(_, fields) -> all (\(ctor, f, _) -> fieldStateOf tracked state l (ctor, f) == Owned) fields) shape

-- A drop to make at a return: the statements of it, under a test of a flag, or the drops of one constructor of a
-- value (under a test that the value is that constructor)
data DropAct
    = Act (Maybe OwnKey) [Statement]
    | SpliceAct [DropAct]
    | GroupAct OwnKey [DropAct]
    | VariantAct Local Name [DropAct]

-- Inserts the drops of a function at its returns, under what the states say: a drop of a part that holds nothing on
-- any path to the return is not inserted, and one that may hold a value is made under a test of its flag. The flags
-- are new locals, kept up to date where a part they stand for is given a value, is moved or taken from, or is dropped.
elaborateDrops :: Program -> Function -> Set Local -> Map Local LocalDecl -> Map BlockId BasicBlock -> Int -> Int -> (Map Local LocalDecl, Map BlockId BasicBlock)
elaborateDrops program fn tracked locals blocks nextLocal nextBlock = (locals', blocks')
  where
    (_, endStates) = blockStates fn tracked blocks
    endState b = Map.findWithDefault Map.empty b endStates
    plans b = [(l, dropPlan program locals tracked (endState b) l) | l <- Set.toList tracked]
    flagged =
        Set.fromList
            ( [ (l, Nothing)
              | (b, BasicBlock _ term) <- Map.toList blocks
              , term == Return
              , l <- Set.toList tracked
              , stateOf tracked (endState b) (l, Nothing) == MaybeOwned
              ]
                ++ [ (l, Just (ctor, f))
                   | (b, BasicBlock _ term) <- Map.toList blocks
                   , term == Return
                   , (l, FieldsDrop shape) <- plans b
                   , (_, fields) <- shape
                   , (ctor, f, _) <- fields
                   , fieldStateOf tracked (endState b) l (ctor, f) == MaybeOwned
                   ]
            )
    flagOf = Map.fromList (zip (Set.toList flagged) (map Local [nextLocal ..]))
    nextLocal' = nextLocal + Map.size flagOf
    setFlag key value = Assign (flagOf Map.! key) (Use (Const (CBool value)))
    flagsOf l value = [setFlag key value | (key, _) <- Map.toList flagOf, fst key == l]
    flagClears ls = concatMap (\l -> flagsOf l False) ls
    withStatementFlags st =
        [st]
            ++ flagClears (statementMoved st)
            ++ (case st of
                    Assign d (TakeField s name field) ->
                        [setFlag (s, Just (name, field)) False | (s, Just (name, field)) `Map.member` flagOf]
                            ++ flagsOf d True
                    Assign d _ -> flagsOf d True
                    Drop l -> flagsOf l False
                    _ -> [])
    withEntryFlags b stmts
        | b == BlockId 0 = [Assign f (Use (Const (CBool (fst key `elem` fnParams fn)))) | (key, f) <- Map.toList flagOf] ++ stmts
        | otherwise = stmts
    (blocks', _, _, newDecls) = foldl step (Map.empty, nextBlock, nextLocal', []) (Map.toList blocks)
    locals' = Map.union (Map.union locals (Map.fromList [(f, LocalDecl TBool Nothing) | f <- Map.elems flagOf])) (Map.fromList newDecls)
    step (done, freshB, freshL, decls) (b, BasicBlock stmts term) =
        let stmts' = withEntryFlags b (concatMap withStatementFlags stmts)
         in case term of
                Return ->
                    let (acts, freshL', decls') = dropActs (endState b) freshL decls
                        finalBlock = BlockId freshB
                        (entry, (freshB', freshL'', blocks'', decls'')) = buildActs acts finalBlock (freshB + 1, freshL', done, decls')
                     in ( Map.insert finalBlock (BasicBlock [] Return) (Map.insert b (BasicBlock stmts' (Goto entry)) blocks'')
                        , freshB'
                        , freshL''
                        , decls''
                        )
                Call callee args dest next ->
                    let updates = flagClears (terminatorMoved term) ++ flagsOf dest True
                     in if null updates
                            then (Map.insert b (BasicBlock stmts' term) done, freshB, freshL, decls)
                            else
                                let trampoline = BlockId freshB
                                 in ( Map.insert trampoline (BasicBlock updates (Goto next)) (Map.insert b (BasicBlock stmts' (Call callee args dest trampoline)) done)
                                    , freshB + 1
                                    , freshL
                                    , decls
                                    )
                _ -> (Map.insert b (BasicBlock stmts' term) done, freshB, freshL, decls)
    -- The drops of every local at a return, as actions, with the new locals that the fields are taken into
    dropActs state freshL decls = foldl one ([], freshL, decls) (plansHere)
      where
        plansHere = [(l, dropPlan program locals tracked state l) | l <- Set.toList tracked]
        one (acts, fresh, ds) (l, plan) =
            case plan of
                NoDrop -> (acts, fresh, ds)
                WholeDrop
                    | stateOf tracked state (l, Nothing) == MaybeOwned -> (acts ++ [Act (Just (l, Nothing)) [Drop l]], fresh, ds)
                    | otherwise -> (acts ++ [Act Nothing [Drop l]], fresh, ds)
                FieldsDrop shape ->
                    let (sub, fresh', ds') = foldl variant ([], fresh, ds) shape
                        variant (vacts, vf, vds) (ctor, fields) =
                            let (facts, vf', vds') = foldl field ([], vf, vds) fields
                                field (facts, ff, fds) (ctor', f, t)
                                    | fieldStateOf tracked state l (ctor', f) == MaybeOwned =
                                        let temp = Local ff
                                         in (facts ++ [Act (Just (l, Just (ctor', f))) [Assign temp (TakeField l ctor' f), Drop temp]], ff + 1, (temp, LocalDecl t Nothing) : fds)
                                    | otherwise =
                                        let temp = Local ff
                                         in (facts ++ [Act Nothing [Assign temp (TakeField l ctor' f), Drop temp]], ff + 1, (temp, LocalDecl t Nothing) : fds)
                             in if null facts then (vacts, vf', vds') else (vacts ++ [if length shape == 1 then SpliceAct facts else VariantAct l ctor facts], vf', vds')
                     in case stateOf tracked state (l, Nothing) of
                            MaybeOwned -> (acts ++ [GroupAct (l, Nothing) (sub ++ [Act Nothing [Drop l]])], fresh', ds')
                            _ -> (acts ++ sub ++ [Act Nothing [Drop l]], fresh', ds')
    -- Runs the actions in order, each block going to the next, and then to the block it all ends at
    buildActs [] cont acc = (cont, acc)
    buildActs (SpliceAct sub : rest) cont acc = buildActs (sub ++ rest) cont acc
    buildActs (GroupAct key sub : rest) cont acc =
        let (restEntry, acc1) = buildActs rest cont acc
            (subEntry, (freshB', freshL', done', decls')) = buildActs sub restEntry acc1
            testB = BlockId freshB'
         in ( testB
            , ( freshB' + 1
              , freshL'
              , Map.insert testB (BasicBlock [] (SwitchBool (Copy (flagOf Map.! key)) subEntry restEntry)) done'
              , decls'
              )
            )
    buildActs (Act Nothing stmts : rest) cont (freshB, freshL, done, decls) =
        let (restEntry, (freshB', freshL', done', decls')) = buildActs rest cont (freshB, freshL, done, decls)
            bid = BlockId freshB'
         in (bid, (freshB' + 1, freshL', Map.insert bid (BasicBlock stmts (Goto restEntry)) done', decls'))
    buildActs (Act (Just key) stmts : rest) cont (freshB, freshL, done, decls) =
        let (restEntry, (freshB', freshL', done', decls')) = buildActs rest cont (freshB, freshL, done, decls)
            dropB = BlockId freshB'
            testB = BlockId (freshB' + 1)
         in ( testB
            , ( freshB' + 2
              , freshL'
              , Map.insert testB (BasicBlock [] (SwitchBool (Copy (flagOf Map.! key)) dropB restEntry)) (Map.insert dropB (BasicBlock stmts (Goto restEntry)) done')
              , decls'
              )
            )
    buildActs (VariantAct l ctor sub : rest) cont (freshB, freshL, done, decls) =
        let (restEntry, acc1) = buildActs rest cont (freshB, freshL, done, decls)
            (subEntry, (freshB', freshL', done', decls')) = buildActs sub restEntry acc1
            temp = Local freshL'
            testB = BlockId freshB'
         in ( testB
            , ( freshB' + 1
              , freshL' + 1
              , Map.insert testB (BasicBlock [Assign temp (IsVariant (Copy l) ctor)] (SwitchBool (Copy temp) subEntry restEntry)) done'
              , (temp, LocalDecl TBool Nothing) : decls'
              )
            )

-- Forwards a cast to the reads that follow it in its block, so that `(x as V).f` reads the field of x itself, which is what
-- lets a field be taken out of x. A cast that nothing else uses is dropped.
fuseCasts :: Function -> Function
fuseCasts fn = fn{fnBlocks = Map.map dropDeadCasts fused}
  where
    fused = Map.map fuseBlock (fnBlocks fn)
    definitions = Map.fromListWith (+) ([(d, 1 :: Int) | BasicBlock stmts _ <- Map.elems (fnBlocks fn), Assign d _ <- stmts] ++ [(d, 1) | BasicBlock _ (Call _ _ d _) <- Map.elems (fnBlocks fn)] ++ [(p, 1) | p <- fnParams fn])
    fuseBlock (BasicBlock stmts term) = BasicBlock (go Map.empty stmts) term
      where
        -- the cast locals met so far in the block, and what each is a cast of, for as long as neither changes
        go _ [] = []
        go subst (Assign d rv : rest) =
            let rv' = substitute subst rv
                kept = Map.filterWithKey (\t s -> t /= d && s /= d) subst
                subst' = case rv' of
                    AsVariant (Copy s) _ | Map.findWithDefault 0 d definitions == 1, d /= s -> Map.insert d s kept
                    _ -> kept
             in Assign d rv' : go subst' rest
        go subst (st : rest) = st : go subst rest
    substitute subst rv =
        case rv of
            ReadField (Copy t) name field | Just s <- Map.lookup t subst -> ReadField (Copy s) name field
            IsVariant (Copy t) name | Just s <- Map.lookup t subst -> IsVariant (Copy s) name
            _ -> rv
    used = Set.fromList [l | BasicBlock stmts term <- Map.elems fused, l <- concatMap stmtOperandLocals stmts ++ termOperandLocals term]
    dropDeadCasts (BasicBlock stmts term) = BasicBlock [st | st <- stmts, not (dead st)] term
    dead (Assign d (AsVariant (Copy _) _)) = d `Set.notMember` used && Map.findWithDefault 0 d definitions == 1
    dead _ = False

stmtOperandLocals :: Statement -> [Local]
stmtOperandLocals (Assign _ rv) = [l | (o, _) <- roles rv, Just l <- [operandLocal o]]
stmtOperandLocals _ = []

termOperandLocals :: Terminator -> [Local]
termOperandLocals term = map fst (Set.toList (termUses term))

-- Which parameters of the function that a call calls are lent: those that the function declares so, or for a function value the
-- parameters that its type marks with &
-- and the type of each parameter
borrowedArguments :: Ctx -> Operand -> Int -> [(Bool, Maybe Type)]
borrowedArguments cx callee count =
    case callee of
        Const (CFn name) | Just f <- Map.lookup name (progFunctions (cxProgram cx)) -> [(p `elem` fnBorrowed f, localType <$> Map.lookup p (fnLocals f)) | p <- fnParams f]
        Copy l | Just (TFn args _) <- Map.lookup l (cxTypes cx) -> map ref args
        Move l | Just (TFn args _) <- Map.lookup l (cxTypes cx) -> map ref args
        _ -> replicate count (False, Nothing)
  where
    ref (TRef t) = (True, Just t)
    ref t = (False, Just t)

-- Whether the statement takes a field out of a value that is not used again, rather than copying it
takesField :: Ctx -> Statement -> Live -> Bool
takesField cx (Assign d (ReadField (Copy s) name field)) after =
    maybe False (heap cx) (Map.lookup d (cxTypes cx))
        && s `Set.notMember` cxProjected cx
        && s `Set.notMember` cxBorrowed cx
        && (s, Whole) `Set.notMember` after'
        && (s, Field name field) `Set.notMember` after'
  where
    after' = forgetLocal d after
takesField _ _ _ = False

-- The state of the rewriting: the next local to make, the locals that were made, and the ones that own nothing
data RS = RS {rsNext :: Int, rsNew :: Map Local LocalDecl, rsAlias :: Set Local}

newtype R a = R {runR :: RS -> (a, RS)}

instance Functor R where
    fmap f (R g) = R (\s -> let (a, s') = g s in (f a, s'))

instance Applicative R where
    pure a = R (\s -> (a, s))
    R f <*> R g = R (\s -> let (h, s') = f s; (a, s'') = g s' in (h a, s''))

instance Monad R where
    R g >>= f = R (\s -> let (a, s') = g s in runR (f a) s')

freshLocal :: Type -> R Local
freshLocal ty = R (\s -> let l = Local (rsNext s) in (l, s{rsNext = rsNext s + 1, rsNew = Map.insert l (LocalDecl ty Nothing) (rsNew s)}))

markAlias :: Local -> R ()
markAlias l = R (\s -> ((), s{rsAlias = Set.insert l (rsAlias s)}))

rewriteBlock :: Ctx -> Map BlockId Live -> (BlockId, BasicBlock) -> R (BlockId, BasicBlock)
rewriteBlock cx outs (b, BasicBlock stmts term) = do
    let out = outs Map.! b
        afters = tail (scanr stepStmt (stepTerm term out) stmts)
    rewritten <- mapM (\(k, st, after) -> rewriteStatement cx b k after st) (zip3 [0 ..] stmts afters)
    (pre, term') <- rewriteTerminator cx out term
    return (b, BasicBlock (concat rewritten ++ pre) term')

rewriteStatement :: Ctx -> BlockId -> Int -> Live -> Statement -> R [Statement]
rewriteStatement _ _ _ _ st@Ghost{} = pure [st]
rewriteStatement _ _ _ _ st@Drop{} = pure [st]
rewriteStatement _ _ _ _ st@Peek{} = pure [st]
rewriteStatement cx b k after (Assign d rv)
    | isProjection rv && heap cx (typeOf cx d) = projection
    | otherwise = do
        (pre, post, operands) <- rewriteOperands cx after' (roles rv)
        pure $ case (pre, withOperands rv operands) of
            -- `y = x` of a value that is used again is the copy itself
            ([Assign t copy@(Clone _)], Use (Move t')) | t == t' -> [Assign d copy] ++ post
            (_, rv') -> pre ++ [Assign d rv'] ++ post
  where
    after' = forgetLocal d after
    projection =
        case (rv, projectionSource rv) of
            (ReadField (Copy s) name field, _)
                | (b, k) `Set.member` cxTakes cx -> pure [Assign d (TakeField s name field)]
            (_, Just (Copy s))
                | peekable cx b k d s -> markAlias d >> pure [Peek d rv]
            _ -> do
                -- a copy of the part: the part is read into a local that owns nothing, and that is cloned
                (pre, post, operands) <- rewriteOperands cx after' (roles rv)
                alias <- freshLocal (typeOf cx d)
                markAlias alias
                pure (pre ++ [Peek alias (withOperands rv operands), Assign d (Clone (Copy alias))] ++ post)

-- Whether a temporary can look at a part of a value instead of owning a copy: it is given a value once, only read, by
-- statements after it in its block, and none of them takes or changes what it was read from or uses it in a way that
-- gives it away
peekable :: Ctx -> BlockId -> Int -> Local -> Local -> Bool
peekable cx b k t s =
    t /= s
        && Map.findWithDefault 0 t (cxDefs cx) == 1
        && s `Set.notMember` cxProjected cx
        && t `Set.notMember` cxUsedByTerminator cx
        && all inBlockAfter uses
        && not (any disturbed [k + 1 .. lastUse])
  where
    uses = Map.findWithDefault [] t (cxUses cx)
    inBlockAfter (b', k', role) = b' == b && k' > k && role == Read
    lastUse = maximum (k : [k' | (_, k', _) <- uses])
    statements = Map.findWithDefault [] b (cxStatements cx)
    disturbed j =
        (b, j) `Set.member` cxTakes cx && takesFrom (statements !! j)
            || disturbs (statements !! j)
    takesFrom (Assign _ (ReadField (Copy s') _ _)) = s' == s
    takesFrom _ = False
    -- gives the local another value, or gives the value away
    disturbs (Assign d rv) = d == s || or [mentions s o | (o, Consume) <- roles rv]
    disturbs _ = False

-- The operands of an rvalue made ready: a value that is given away and used again is cloned, and one that is not is moved.
-- A constant that is only read is made into a local first and freed after.
rewriteOperands :: Ctx -> Live -> [(Operand, Role)] -> R ([Statement], [Statement], [Operand])
rewriteOperands cx after' operands = go consumed operands
  where
    -- (a parameter that is lent is always still wanted: whoever lent it gets it back)
    stillLive = localsOf after' `Set.union` cxBorrowed cx
    -- (a local that the same operation reads, as a lent argument is, cannot be handed over: the one that takes it may change it)
    readHere = Set.fromList [l | (o, Read) <- operands, Just l <- [operandLocal o]]
    -- how many operands give up each local, so that all but the last get a copy
    consumed = Map.fromListWith (+) [(l, 1 :: Int) | (o, Consume) <- operands, Just l <- [operandLocal o], heap cx (typeOf cx l)]
    siblingType = listToMaybe [typeOf cx l | (o, _) <- operands, Just l <- [operandLocal o], heap cx (typeOf cx l)]
    go _ [] = pure ([], [], [])
    go remaining ((o, role) : rest) = do
        (pre, post, o', remaining') <- one remaining o role
        (pres, posts, os) <- go remaining' rest
        pure (pre ++ pres, post ++ posts, o' : os)
    one remaining o Consume
        | Just l <- operandLocal o
        , heap cx (typeOf cx l) = do
            let left = Map.findWithDefault 1 l remaining - 1
                remaining' = Map.insert l left remaining
            if left > 0 || l `Set.member` stillLive || l `Set.member` readHere
                then do
                    copy <- freshLocal (typeOf cx l)
                    pure ([Assign copy (Clone (Copy l))], [], Move copy, remaining')
                else pure ([], [], Move l, remaining')
    one remaining o@(Const c) Read
        | isHeapConstant c = do
            temp <- freshLocal (constantType (cxProgram cx) siblingType c)
            pure ([Assign temp (Use o)], [Drop temp], Copy temp, remaining)
    one remaining o _ = pure ([], [], o, remaining)

-- A constant that owns something, which is made again each time it is wanted: a list, or a struct or an enum that has one. A
-- constant that owns nothing needs no care.
isHeapConstant :: Constant -> Bool
isHeapConstant (CData _ fields) = any (isHeapConstant . snd) fields
isHeapConstant _ = False

-- The type of a constant that is only read, from what it holds
constantType :: Program -> Maybe Type -> Constant -> Type
constantType program _ c =
    case c of
        CBool _ -> TBool
        CData name _ -> case Map.lookup name (progTypes program) of
            Just StructDecl{} -> TNamed name
            _ -> TVariant name
        _ -> TInt

-- The operands put back into the rvalue they came from, in the order `roles` gave them
withOperands :: Rvalue -> [Operand] -> Rvalue
withOperands rv operands =
    case (rv, operands) of
        (Use _, [o]) -> Use o
        (BinaryOp op _ _, [a, b]) -> BinaryOp op a b
        (ListOp op _, os) -> ListOp op os
        (MakeList _, os) -> MakeList os
        (MakeBox _, [o]) -> MakeBox o
        (Unbox _, [o]) -> Unbox o
        (Unsize _, [o]) -> Unsize o
        (MakeData name fields, os) -> MakeData name (zip (map fst fields) os)
        (ReadField _ name field, [o]) -> ReadField o name field
        (IsVariant _ name, [o]) -> IsVariant o name
        (AsVariant _ name, [o]) -> AsVariant o name
        (Clone _, [o]) -> Clone o
        _ -> rv

rewriteTerminator :: Ctx -> Live -> Terminator -> R ([Statement], Terminator)
rewriteTerminator cx out term =
    case term of
        Call callee args dest next -> do
            -- (an argument for a parameter that is lent is only read: the callee neither frees nor changes it)
            let lent = borrowedArguments cx callee (length args)
                -- (a constant that owns something and is lent is made into a local of the type of the parameter that it is lent to)
                prepare (a, (True, Just ty)) | Const c <- a, isHeapConstant c = do
                    temp <- freshLocal ty
                    pure (Copy temp, [Assign temp (Use a)])
                prepare (a, _) = pure (a, [])
            prepared <- mapM prepare (zip args lent)
            (pre, _, args') <- rewriteOperands cx (forgetLocal dest out) [(a, if b then Read else Consume) | ((a, _), (b, _)) <- zip prepared lent]
            return (concatMap snd prepared ++ pre, Call callee args' dest next)
        _ -> return ([], term)
