module MirOwnership
    ( insertOwnership
    , needsDrop
    ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)
import Data.Set (Set)
import qualified Data.Set as Set

import Mir
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
insertOwnership program =
    program
        { progFunctions = Map.map (ownFunction program) (progFunctions program)
        , progMain = ownFunction program (progMain program)
        }

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
        TList{} -> True
        TBox{} -> True
        TArrayOf t _ -> owning t
        TNamed n -> declared n
        TVariant v -> maybe False declared (ownerOf v)
        _ -> False
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
        ListOp Set [l, i, x] -> [(l, Consume), (i, Read), (x, Consume)]
        ListOp _ os -> [(o, Read) | o <- os]
        MakeList os -> [(o, Consume) | o <- os]
        MakeBox o -> [(o, Consume)]
        Unbox o -> [(o, Consume)]
        MakeData _ fields -> [(o, Consume) | (_, o) <- fields]
        ReadField o _ _ -> [(o, Read)]
        IsVariant o _ -> [(o, Read)]
        AsVariant o _ -> [(o, Consume)]
        Clone o -> [(o, Read)]
        TakeField l _ _ -> [(Copy l, Read)]

-- The rvalues that read a part of a value
isProjection :: Rvalue -> Bool
isProjection (ListOp op _) = op `elem` [First, Last, Get]
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
        owned = [l | (l, d) <- Map.toList allLocals, needsDrop program (localType d), l /= Local 0, l `Set.notMember` rsAlias finalState]
        withDrops (b, BasicBlock stmts term) =
            (b, BasicBlock (if term == Return then stmts ++ map Drop owned else stmts) term)
     in fn{fnLocals = allLocals, fnBlocks = Map.fromList (map withDrops blocks)}

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

-- Whether the statement takes a field out of a value that is not used again, rather than copying it
takesField :: Ctx -> Statement -> Live -> Bool
takesField cx (Assign d (ReadField (Copy s) name field)) after =
    maybe False (heap cx) (Map.lookup d (cxTypes cx))
        && s `Set.notMember` cxProjected cx
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
    stillLive = localsOf after'
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
            if left > 0 || l `Set.member` stillLive
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
isHeapConstant CList{} = True
isHeapConstant (CData _ fields) = any (isHeapConstant . snd) fields
isHeapConstant _ = False

-- The type of a constant that is only read, from what it is read with when that says, and from what it holds otherwise
constantType :: Program -> Maybe Type -> Constant -> Type
constantType _ (Just ty) CList{} = ty
constantType program _ c =
    case c of
        CBool _ -> TBool
        CList cs -> TList (elementType cs)
        CData name _ -> case Map.lookup name (progTypes program) of
            Just StructDecl{} -> TNamed name
            _ -> TVariant name
        _ -> TInt
  where
    elementType cs = case [c' | c' <- cs, known c'] ++ cs of
        c' : _ -> constantType program Nothing c'
        [] -> TInt
    known (CList cs) = any known cs
    known _ = True

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
            (pre, _, args') <- rewriteOperands cx (forgetLocal dest out) [(a, Consume) | a <- args]
            return (pre, Call callee args' dest next)
        _ -> return ([], term)
