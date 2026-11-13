module MirPacks
    ( Expanded (..)
    , expandPack
    , isPackName
    ) where

import Data.Char (isDigit)
import Data.List (isPrefixOf, stripPrefix)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as Set

import Mir
import StdLib (builtinFunct)
import Syntax (Expression (..), FunctBody (..), Proof (..), RwRule (..), Termination (..), ValidationStatement (..), Value (..), VariableProof, exprToProof)
import qualified Types as T
import Types (Rel (..), Type (..), Variable)

-- The expansion of a variadic function for a copy (MIR.md, "Copies of variadic functions"). The copy step runs it before it
-- puts the copy's types in: the pack parameter becomes one parameter for each argument (`args 0`, ...), size(args) the number
-- of them, each loop over the pack a copy of its body for each index, a branch whose test each copy knows only the side it
-- takes, and get(args, k) the parameter at k. What each part of the copy binds the element types of its loops and gets to is
-- given with it, for the copy step to put the types of the arguments in.

-- A pack of types (`..T`) and its elements' types (`..T#0`, `..T@1`) keep the dots, which no other name has
isPackName :: Variable -> Bool
isPackName name = ".." `isPrefixOf` name

data Expanded = Expanded
    { exFunction :: Function
    , exBlockIndexes :: Map BlockId (Map Variable Integer) -- the element types each block binds, to the index of their argument
    , exLocalIndexes :: Map Local (Map Variable Integer) -- and each local
    }

-- What the expansion knows of the copy: the pack's local and name, the number of arguments and their parameters
-- (xNames: the names a validation statement sees as numbers in the copy, such as the index of an unrolled loop)
data X = X {xPack :: Local, xName :: Variable, xType :: Variable, xCount :: Integer, xElements :: [Local], xNames :: Map Variable Integer, xWhere :: String, xDefines :: Map Variable Integer}

data XS = XS
    { xsFn :: Function
    , xsNextLocal :: Int
    , xsNextBlock :: Int
    , xsBlocks :: Map BlockId (Map Variable Integer)
    , xsLocals :: Map Local (Map Variable Integer)
    , xsLoops :: [PackLoop]
    }

expandPack :: BoundedFn -> Variable -> Integer -> Function -> Either String Expanded
expandPack bounded pack n fn0 = do
    packLocal <- case [l | l <- fnParams fn0, Just d <- [Map.lookup l (fnLocals fn0)], localType d == TParam pack] of
        [l] -> Right l
        _ -> Left ("internal compiler error: " ++ fnName fn0 ++ " has no pack parameter of " ++ pack)
    let name = fromMaybe "args" (Map.lookup packLocal (fnLocals fn0) >>= localName)
        next0 = 1 + maximum (0 : [i | Local i <- Map.keys (fnLocals fn0)])
        elements = [Local (next0 + k) | k <- [0 .. fromInteger n - 1]]
        x = X packLocal name pack n elements Map.empty "" Map.empty
        decls = Map.fromList [(l, LocalDecl (TParam (pack ++ "#" ++ show k)) (Just (elementName x k))) | (l, k) <- zip elements [0 ..]]
        spread ls = concatMap (\l -> if l == packLocal then elements else [l]) ls
        fn1 =
            fn0
                { fnParams = spread (fnParams fn0)
                , fnBorrowed = spread (fnBorrowed fn0)
                , fnLocals = Map.union decls (fnLocals fn0)
                , fnTypeParams = filter (/= pack) (fnTypeParams fn0)
                }
        nextBlock = 1 + maximum (0 : [i | BlockId i <- Map.keys (fnBlocks fn1)])
    st <- unrollAll x (XS fn1 (next0 + fromInteger n) nextBlock Map.empty Map.empty (boundedPackLoops bounded))
    (fn2a, bindings) <- resolveElements x (xsFn st)
    let fn2 = pruneUnreachable fn2a
    fn3 <- packProofs x fn2
    let fn4 = dropUnused (spreadEnvs x fn3)
    case [() | usesLocal packLocal fn4] of
        _ : _ -> Left ("internal compiler error: the pack " ++ name ++ " of " ++ fnName fn0 ++ " is used as a value in a copy")
        [] -> Right ()
    let context m key = Map.findWithDefault Map.empty key m
        within inner outer = Map.isSubmapOf outer inner
        blockBindings =
            Map.fromList
                [ (b, Map.union (context (xsBlocks st) b) (Map.fromList [(p, k) | (at, p, k) <- bindings, within (context (xsBlocks st) b) (context (xsBlocks st) at)]))
                | b <- Map.keys (fnBlocks fn4)
                ]
        localBindings =
            Map.fromList
                [ (l, Map.filter (\k -> k >= 0 && k < n) (Map.union (context (xsLocals st) l) (Map.fromList [(p, k) | (at, p, k) <- bindings, mentionsName p (localType d), within (context (xsLocals st) l) (context (xsBlocks st) at)])))
                | (l, d) <- Map.toList (fnLocals fn4)
                ]
        -- (a local whose type is that of an element no argument gives, such as the element of an iteration past the pack
        -- or of a loop in a branch the copy drops, is only named by an environment, which no longer needs it)
        unbound = Set.fromList [l | (l, d) <- Map.toList (fnLocals fn4), any (\p -> Map.notMember p (context localBindings l)) (elementTypes x (localType d))]
        fn5 = dropUnused (forgetLocals unbound fn4)
        kept = Map.keysSet (fnLocals fn5)
    case [l | l <- Set.toList kept, Set.member l unbound] of
        l : _ -> Left ("internal compiler error: a copy of " ++ fnName fn0 ++ " uses " ++ show l ++ ", of the type of an element no argument gives")
        [] -> Right ()
    Right
        ( Expanded
            fn5{fnLocals = Map.delete packLocal (fnLocals fn5)}
            (Map.filter (not . Map.null) blockBindings)
            (Map.filterWithKey (\l m -> Set.member l kept && not (Map.null m)) localBindings)
        )

-- The element types of the pack read at an index that is not a number a type names
elementTypes :: X -> Type -> [Variable]
elementTypes x ty = case ty of
    TParam q | (xType x ++ "@") `isPrefixOf` q -> [q]
    TAddr t -> elementTypes x t
    TBlock t -> elementTypes x t
    TUninit t -> elementTypes x t
    TRef t -> elementTypes x t
    TMutRef t -> elementTypes x t
    TArrayOf t _ -> elementTypes x t
    TFn args ret -> concatMap (elementTypes x) (ret : args)
    TNamed _ args -> concat [elementTypes x t | T.ArgType t <- args]
    _ -> []

-- The function with the locals taken out of every environment
forgetLocals :: Set.Set Local -> Function -> Function
forgetLocals gone fn =
    fn
        { fnBlocks = Map.map (\(BasicBlock ss t) -> BasicBlock (map statement ss) t) (fnBlocks fn)
        , fnSpec = spec{specEnv = keep (specEnv spec), specLoops = Map.map (\l -> l{loopEnv = keep (loopEnv l)}) (specLoops spec)}
        }
  where
    spec = fnSpec fn
    keep = Map.filter (\o -> case o of
        Copy l -> Set.notMember l gone
        Move l -> Set.notMember l gone
        _ -> True)
    statement s = case s of
        Ghost env g -> Ghost (keep env) g
        _ -> s

mentionsName :: Variable -> Type -> Bool
mentionsName p ty = case ty of
    TParam q -> p == q
    TAddr t -> mentionsName p t
    TBlock t -> mentionsName p t
    TUninit t -> mentionsName p t
    TRef t -> mentionsName p t
    TMutRef t -> mentionsName p t
    TArrayOf t _ -> mentionsName p t
    TFn args ret -> any (mentionsName p) (ret : args)
    TNamed _ args -> or [mentionsName p t | T.ArgType t <- args]
    _ -> False

-- The function without the blocks nothing reaches (an element read out of range ends its block, and what came after it
-- goes), and the loops that start in them
pruneUnreachable :: Function -> Function
pruneUnreachable fn = fn{fnBlocks = keepDefinitions reach (fnBlocks fn), fnSpec = (fnSpec fn){specLoops = Map.filterWithKey (\h _ -> Set.member h reach) (specLoops (fnSpec fn))}}
  where
    reach = walk Set.empty [BlockId 0]
    walk seen [] = seen
    walk seen (b : rest)
        | Set.member b seen = walk seen rest
        | otherwise = case Map.lookup b (fnBlocks fn) of
            Nothing -> walk seen rest
            Just (BasicBlock _ t) -> walk (Set.insert b seen) (successors t ++ rest)

-- The blocks reached, with the definitions of the functions defined in the blocks that go put at the start (a function a
-- copy never calls is still lifted, and the validator checks each lifted function where it is defined)
keepDefinitions :: Set.Set BlockId -> Map BlockId BasicBlock -> Map BlockId BasicBlock
keepDefinitions reach blocks = Map.adjust (\(BasicBlock ss t) -> BasicBlock (orphans ++ ss) t) (BlockId 0) (Map.filterWithKey (\b _ -> Set.member b reach) blocks)
  where
    orphans = [s | (b, BasicBlock ss _) <- Map.toList blocks, Set.notMember b reach, s@(Ghost _ GhostFunction{}) <- ss]

elementName :: X -> Integer -> Variable
elementName x k = xName x ++ " " ++ show k

-- Unrolling: the loops whose test a copy decides go first (a branch the copy does not take may hold a loop), then the
-- outermost loop, again until none is left
unrollAll :: X -> XS -> Either String XS
unrollAll x st0 = do
    let st = foldPrune x st0
        loops = xsLoops st
    case [l | l <- loops, not (any (\o -> packHeader o /= packHeader l && packHeader l `elem` packBlocks o) loops)] of
        [] | null loops -> Right st
        [] -> Left ("internal compiler error: the loops over the pack of " ++ fnName (xsFn st) ++ " are not nested")
        l : _ -> unrollOne x l st >>= unrollAll x

-- The value each local has wherever it is read, when it is assigned once from a constant, arithmetic or a comparison of
-- such, or the size of the pack, and is never borrowed (a write through a borrow would give it another value)
constantsOf :: X -> Function -> Map Local Constant
constantsOf x fn = go Map.empty
  where
    stmts = concat [ss | BasicBlock ss _ <- Map.elems (fnBlocks fn)]
    assigned = Map.fromListWith (++) ([(d, [rv]) | Assign d rv <- stmts] ++ [(d, [Use (Const (CFn ""))]) | BasicBlock _ (Call _ _ d _) <- Map.elems (fnBlocks fn)])
    borrowed = borrowedLocals fn
    single = Map.mapMaybe (\rvs -> case rvs of [rv] -> Just rv; _ -> Nothing) (Map.filterWithKey (\l _ -> l `notElem` fnParams fn && Set.notMember l borrowed) assigned)
    go known =
        let known' = Map.union known (Map.mapMaybe (evaluate known) single)
         in if Map.size known' == Map.size known then known else go known'
    evaluate known rv = case rv of
        Use o -> operandConstant known o
        BinaryOp op a b -> do
            ca <- operandConstant known a
            cb <- operandConstant known b
            binary op ca cb
        ListOp Length [o] | isPack o -> Just (CInt (xCount x))
        _ -> Nothing
    isPack o = case o of
        Copy l -> l == xPack x
        Move l -> l == xPack x
        _ -> False

-- The locals a borrow or a write through one starts from
borrowedLocals :: Function -> Set.Set Local
borrowedLocals fn = Set.fromList (concat [roots s | BasicBlock ss _ <- Map.elems (fnBlocks fn), s <- ss])
  where
    roots s = case s of
        Assign _ (Borrow r _ _) -> [r]
        Peek _ (Borrow r _ _) -> [r]
        AssignRef r _ _ -> [r]
        _ -> []

operandConstant :: Map Local Constant -> Operand -> Maybe Constant
operandConstant known o = case o of
    Const c@(CInt _) -> Just c
    Const c@(CBool _) -> Just c
    Copy l -> Map.lookup l known
    Move l -> Map.lookup l known
    _ -> Nothing

binary :: BinOp -> Constant -> Constant -> Maybe Constant
binary op a b = case (op, a, b) of
    (Add, CInt p, CInt q) -> Just (CInt (p + q))
    (Sub, CInt p, CInt q) -> Just (CInt (p - q))
    (Mul, CInt p, CInt q) -> Just (CInt (p * q))
    (Compare rel, CInt p, CInt q) -> Just (CBool (compareWith rel p q))
    (Compare Eq, CBool p, CBool q) -> Just (CBool (p == q))
    (Compare NotEq, CBool p, CBool q) -> Just (CBool (p /= q))
    _ -> Nothing

compareWith :: Rel -> Integer -> Integer -> Bool
compareWith rel p q = case rel of
    Eq -> p == q
    NotEq -> p /= q
    Lt -> p < q
    Gt -> p > q
    LtEq -> p <= q
    GtEq -> p >= q

-- A test the copy decides is a jump to the side it takes; what no path reaches goes, with the loops that start there
foldPrune :: X -> XS -> XS
foldPrune x st =
    st
        { xsFn = fn{fnBlocks = kept, fnSpec = (fnSpec fn){specLoops = Map.filterWithKey (\h l -> Set.member h reach && Set.member (loopBody l) reach) (specLoops (fnSpec fn))}}
        , xsLoops = [l | l <- xsLoops st, Set.member (packHeader l) reach]
        }
  where
    fn = xsFn st
    known = constantsOf x fn
    decided = Map.map decide (fnBlocks fn)
    decide (BasicBlock ss t) = BasicBlock ss $ case t of
        SwitchBool o yes no | Just (CBool v) <- operandConstant known o -> Goto (if v then yes else no)
        _ -> t
    reach = walk Set.empty [BlockId 0]
    walk seen [] = seen
    walk seen (b : rest)
        | Set.member b seen = walk seen rest
        | otherwise = case Map.lookup b decided of
            Nothing -> walk seen rest
            Just (BasicBlock _ t) -> walk (Set.insert b seen) (successors t ++ rest)
    kept = keepDefinitions reach decided

-- A copy of the loop's body for each index from lo to hi - 1: each with blocks and locals of its own, the index read as the
-- number, the element as the parameter at it, and the element type bound to that argument's
unrollOne :: X -> PackLoop -> XS -> Either String XS
unrollOne x loop st = do
    let fn = xsFn st
        known = constantsOf x fn
        intAt l = case Map.lookup l known of
            Just (CInt v) -> Right v
            _ -> Left ("internal compiler error: a bound of a loop over the pack of " ++ fnName fn ++ " is not fixed in a copy")
    lo <- intAt (packLo loop)
    hi <- intAt (packHi loop)
    let values = [lo .. hi - 1]
        count = length values
        body = Set.fromList (packBlocks loop)
        nb = xsNextBlock st
        bodyBlocks = packBlocks loop
        bodyLocals = packElement loop : packLocals loop
        blockMaps = [Map.fromList (zip bodyBlocks [BlockId (nb + j * length bodyBlocks + i) | i <- [0 ..]]) | j <- [0 .. count - 1]]
        nl = xsNextLocal st
        localMaps = [Map.fromList (zip bodyLocals [Local (nl + j * length bodyLocals + i) | i <- [0 ..]]) | j <- [0 .. count - 1]]
        entries = [m Map.! packBody loop | m <- blockMaps]
        nextOf j = if j + 1 < count then entries !! (j + 1) else packExit loop
        inRange v = v >= 0 && v < xCount x
        elementType = packElementType loop
        iteration (j, v) = (j, v, blockMaps !! j, localMaps' j v)
        localMaps' j v = if inRange v then Map.insert (packElement loop) (xElements x !! fromInteger v) (localMaps !! j) else localMaps !! j
        iterations = map iteration (zip [0 ..] values)
        copies =
            [ (bm Map.! b, BasicBlock [renameDefines (definesOf v) (Map.restrictKeys (definesOf v) (definedBefore b p)) (renameStatement loop lm v s) | (p, s) <- zip [0 :: Int ..] ss, not (inRange v && definesElement s), not (definesFunction s)] (renameTerminator loop bm lm v (nextOf j) t))
            | (j, v, bm, lm) <- iterations
            , b <- bodyBlocks
            , Just (BasicBlock ss t) <- [Map.lookup b (fnBlocks fn)]
            ]
        definesElement s = case s of
            Assign d _ -> d == packElement loop
            _ -> False
        -- (a function defined in the body is lifted once, and defined where the loop starts: whether or not any iteration runs)
        definesFunction s = case s of
            Ghost _ GhostFunction{} -> True
            _ -> False
        -- (a name the body defines is one name in each iteration: the validator keeps one definition of a name, the last
        -- it reads, and the iterations come one after another)
        bodyDefines = Map.fromList [(b, [(p, n) | (p, Ghost _ (GhostValidation (AssignProofVar n _))) <- zip [0 :: Int ..] ss, not (placePrefix `isPrefixOf` n)]) | b <- bodyBlocks, Just (BasicBlock ss _) <- [Map.lookup b (fnBlocks fn)]]
        definedInBody = Set.fromList [n | ds <- Map.elems bodyDefines, (_, n) <- ds]
        definesOf v = Map.fromSet (\n -> n ++ " in iteration " ++ show v) definedInBody
        -- (a use is of the iteration's own name only where the body's define of it comes first: earlier in its block, or in a
        -- block every path from the start of the body to it goes through)
        dominators = bodyDominators (packBody loop) [(b, [c | Just (BasicBlock _ t) <- [Map.lookup b (fnBlocks fn)], c <- successors t, Set.member c body]) | b <- bodyBlocks]
        definedBefore b p =
            Set.fromList
                ( [n | d <- Set.toList (Map.findWithDefault Set.empty b dominators), d /= b, (_, n) <- Map.findWithDefault [] d bodyDefines]
                    ++ [n | (q, n) <- Map.findWithDefault [] b bodyDefines, q < p]
                )
        markers = [s | b <- bodyBlocks, Just (BasicBlock ss _) <- [Map.lookup b (fnBlocks fn)], s <- ss, definesFunction s]
        blockIndexes = Map.fromList [(bm Map.! b, Map.insert elementType v (Map.findWithDefault Map.empty b (xsBlocks st))) | (_, v, bm, _) <- iterations, b <- bodyBlocks]
        localDecls = Map.fromList [(l', d) | (_, v, _, lm) <- iterations, l <- bodyLocals, Just l' <- [Map.lookup l lm], not (l == packElement loop && inRange v), Just d <- [Map.lookup l (fnLocals fn)]]
        localIndexes = Map.fromList [(l', Map.insert elementType v (Map.findWithDefault Map.empty l (xsLocals st))) | (_, v, _, lm) <- iterations, l <- bodyLocals, Just l' <- [Map.lookup l lm], not (l == packElement loop && inRange v)]
        loopSpecs =
            Map.fromList
                [ ( bm Map.! h
                  , let names = Map.restrictKeys (definesOf v) (definedBefore h 0)
                     in ls
                            { loopBody = Map.findWithDefault (loopBody ls) (loopBody ls) bm
                            , loopEnv = Map.map (renameOperand loop lm v) (loopEnv ls)
                            , loopInvariant = map (renameValidation names names) (loopInvariant ls)
                            , loopTermination = fmap (renameTermination names) (loopTermination ls)
                            }
                  )
                | (_, v, bm, lm) <- iterations
                , (h, ls) <- Map.toList (specLoops (fnSpec fn))
                , Set.member h body
                ]
        inner =
            [ o
                { packHeader = rb (packHeader o)
                , packBody = rb (packBody o)
                , packExit = rb (packExit o)
                , packBlocks = map rb (packBlocks o)
                , packLocals = map rl (packLocals o)
                , packIndex = rl (packIndex o)
                , packElement = rl (packElement o)
                , packLo = rl (packLo o)
                , packHi = rl (packHi o)
                , packTaken = fmap rl (packTaken o)
                }
            | (_, _, bm, lm) <- iterations
            , let rb b = Map.findWithDefault b b bm
            , let rl l = Map.findWithDefault l l lm
            , o <- xsLoops st
            , packHeader o /= packHeader loop
            , Set.member (packHeader o) body
            ]
        entry = if count > 0 then head entries else packExit loop
        headerLocals = case Map.lookup (packHeader loop) (fnBlocks fn) of
            Just (BasicBlock ss _) -> [d | Assign d _ <- ss]
            Nothing -> []
        retarget (BasicBlock ss t) = BasicBlock ([s | s <- ss, not (takes s)] ++ (if packHeader loop `elem` successors t then markers else [])) (retargetTerminator t)
        takes s = case (s, packTaken loop) of
            (Assign d _, Just t) -> d == t
            _ -> False
        retargetTerminator t = case t of
            Goto b | b == packHeader loop -> Goto entry
            SwitchBool o a b -> SwitchBool o (if a == packHeader loop then entry else a) (if b == packHeader loop then entry else b)
            Call f as d next | next == packHeader loop -> Call f as d entry
            _ -> t
        outside = Map.map retarget (Map.filterWithKey (\b _ -> b /= packHeader loop && Set.notMember b body) (fnBlocks fn))
        dropped = Set.fromList (bodyLocals ++ headerLocals ++ maybe [] pure (packTaken loop))
        spec = fnSpec fn
        fn' =
            fn
                { fnBlocks = Map.union outside (Map.fromList copies)
                , fnLocals = Map.union (Map.filterWithKey (\l _ -> Set.notMember l dropped) (fnLocals fn)) localDecls
                , fnSpec = spec{specLoops = Map.union (Map.filterWithKey (\h _ -> Set.notMember h body) (specLoops spec)) loopSpecs}
                }
    Right
        st
            { xsFn = fn'
            , xsNextBlock = nb + count * length bodyBlocks
            , xsNextLocal = nl + count * length bodyLocals
            , xsBlocks = Map.union (Map.filterWithKey (\b _ -> Set.notMember b body) (xsBlocks st)) blockIndexes
            , xsLocals = Map.union (Map.filterWithKey (\l _ -> Set.notMember l dropped) (xsLocals st)) localIndexes
            , xsLoops = [o | o <- xsLoops st, packHeader o /= packHeader loop, Set.notMember (packHeader o) body] ++ inner
            }

renameOperand :: PackLoop -> Map Local Local -> Integer -> Operand -> Operand
renameOperand loop lm v o = case o of
    Copy l | l == packIndex loop -> Const (CInt v)
    Move l | l == packIndex loop -> Const (CInt v)
    Copy l -> Copy (Map.findWithDefault l l lm)
    Move l -> Move (Map.findWithDefault l l lm)
    _ -> o

renameStatement :: PackLoop -> Map Local Local -> Integer -> Statement -> Statement
renameStatement loop lm v = mapStatement (\l -> Map.findWithDefault l l lm) (renameOperand loop lm v)

-- A statement with its locals renamed: the ones it assigns and roots by the first function, the ones it reads by the second
mapStatement :: (Local -> Local) -> (Operand -> Operand) -> Statement -> Statement
mapStatement local operand s = case s of
    Assign d rv -> Assign (local d) (mapRvalue local operand rv)
    Ghost env g -> Ghost (Map.map operand env) (case g of GhostDissolve l -> GhostDissolve (local l); _ -> g)
    Drop l -> Drop (local l)
    Peek d rv -> Peek (local d) (mapRvalue local operand rv)
    AssignRef root steps rv -> AssignRef (local root) (map step steps) (mapRvalue local operand rv)
  where
    step st = case st of
        RefIndex o -> RefIndex (operand o)
        _ -> st

mapRvalue :: (Local -> Local) -> (Operand -> Operand) -> Rvalue -> Rvalue
mapRvalue local operand rv = case rv of
    Use o -> Use (operand o)
    BinaryOp b p q -> BinaryOp b (operand p) (operand q)
    ListOp l os -> ListOp l (map operand os)
    MakeList os -> MakeList (map operand os)
    MakeBox o -> MakeBox (operand o)
    Unbox o -> Unbox (operand o)
    Unsize o -> Unsize (operand o)
    MakeData n fields -> MakeData n [(f, operand o) | (f, o) <- fields]
    ReadField o n f -> ReadField (operand o) n f
    IsVariant o n -> IsVariant (operand o) n
    AsVariant o n -> AsVariant (operand o) n
    CopyOf o -> CopyOf (operand o)
    TakeField l n f -> TakeField (local l) n f
    Borrow root steps m -> Borrow (local root) [case st of RefIndex o -> RefIndex (operand o); _ -> st | st <- steps] m
    Deref o -> Deref (operand o)

mapTerminator :: (Local -> Local) -> (Operand -> Operand) -> (BlockId -> BlockId) -> Terminator -> Terminator
mapTerminator local operand block t = case t of
    Goto b -> Goto (block b)
    SwitchBool o a b -> SwitchBool (operand o) (block a) (block b)
    Call f as d next -> Call (operand f) (map operand as) (local d) (block next)
    Return -> Return
    Unreachable -> Unreachable

renameTerminator :: PackLoop -> Map BlockId BlockId -> Map Local Local -> Integer -> BlockId -> Terminator -> Terminator
renameTerminator loop bm lm v next = mapTerminator (\l -> Map.findWithDefault l l lm) (renameOperand loop lm v) block
  where
    block b
        | b == packHeader loop = next
        | otherwise = Map.findWithDefault b b bm

-- get(args, k), size(args) and borrows of an element: the parameter at k (a local that only it assigns is that parameter),
-- the number, a borrow of the parameter; a k out of range in a block a copy runs is the proof obligation k < N, which the
-- validator refuses unless the path is ruled out
resolveElements :: X -> Function -> Either String (Function, [(BlockId, Variable, Integer)])
resolveElements x fn = do
    blocks <- Map.traverseWithKey (\b blk -> block b blk) (fnBlocks fn)
    let renames = Map.fromList (concat [rs | (_, rs, _) <- Map.elems blocks])
        bindings = concat [bs | (_, _, bs) <- Map.elems blocks]
        rename l = Map.findWithDefault l l renames
        operand o = case o of
            Copy l -> Copy (rename l)
            Move l -> Move (rename l)
            _ -> o
        renamed = Map.map (\(BasicBlock ss t) -> BasicBlock (map (mapStatement rename operand) ss) (mapTerminator rename operand id t)) (Map.map (\(blk, _, _) -> blk) blocks)
        spec = fnSpec fn
    Right
        ( fn
            { fnBlocks = renamed
            , fnLocals = Map.filterWithKey (\l _ -> Map.notMember l renames) (fnLocals fn)
            , fnSpec = spec{specEnv = Map.map operand (specEnv spec), specLoops = Map.map (\l -> l{loopEnv = Map.map operand (loopEnv l)}) (specLoops spec)}
            }
        , bindings
        )
  where
    known = constantsOf x fn
    borrowed = borrowedLocals fn
    assignments = Map.fromListWith (+) ([(d, 1 :: Int) | BasicBlock ss _ <- Map.elems (fnBlocks fn), Assign d _ <- ss] ++ [(d, 1) | BasicBlock _ (Call _ _ d _) <- Map.elems (fnBlocks fn)])
    isPack o = case o of
        Copy l -> l == xPack x
        Move l -> l == xPack x
        _ -> False
    indexOf o = case operandConstant known o of
        Just (CInt k) -> Right k
        _ -> Left ("internal compiler error: an index of the pack of " ++ fnName fn ++ " is not fixed in a copy")
    -- (an element read at an index that is not a number has a type of its own, `..T@n`, which is the type of the argument
    -- the index comes to: in the blocks of this iteration, and of the iterations inside it)
    elementType d = case unrefType . localType <$> Map.lookup d (fnLocals fn) of
        Just (TParam p) | (xType x ++ "@") `isPrefixOf` p -> Just p
        _ -> Nothing
    unrefType ty = case ty of
        TRef t -> t
        TMutRef t -> t
        _ -> ty
    block here (BasicBlock ss t) = go [] [] [] ss
      where
        go acc renames bs [] = Right (BasicBlock (reverse acc) t, renames, bs)
        go acc renames bs (s : rest) = case s of
            Assign d (ReadField o "$pack" field) | isPack o, all isDigit field, not (null field) -> element acc renames bs rest d (read field)
            Assign d (ListOp Get [o, i]) | isPack o -> indexOf i >>= element acc renames bs rest d
            Assign d (ListOp Length [o]) | isPack o -> go (Assign d (Use (Const (CInt (xCount x)))) : acc) renames bs rest
            Assign d (Borrow root (RefField "$pack" field : steps) m) | root == xPack x, all isDigit field, not (null field) -> borrow acc renames bs rest d (read field) steps m
            Assign d (Borrow root (RefIndex i : steps) m) | root == xPack x -> indexOf i >>= \k -> borrow acc renames bs rest d k steps m
            _ -> go (s : acc) renames bs rest
        bound bs d k = [(here, p, k) | Just p <- [elementType d]] ++ bs
        element acc renames bs rest d k
            | not (inRange k) = Right (outOfRange acc k, renames, bs)
            | d == Local 0 = go (Assign d (Use (Copy (parameter k))) : acc) renames (bound bs d k) rest
            | d `notElem` fnParams fn && Set.notMember d borrowed && Map.findWithDefault 0 d assignments == 1 = go acc ((d, parameter k) : renames) (bound bs d k) rest
            | otherwise = go (Assign d (CopyOf (Copy (parameter k))) : acc) renames (bound bs d k) rest
        borrow acc renames bs rest d k steps m
            | not (inRange k) = Right (outOfRange acc k, renames, bs)
            | otherwise = go (Assign d (Borrow (parameter k) steps m) : acc) renames (bound bs d k) rest
        -- (the validator refuses the fact on a path it cannot rule out; the contradiction assumed after it keeps the validator
        -- from checking the end of the block, which returns no value)
        outOfRange acc k =
            let (fact, names) = rangeFact x (maybe "" (" at line " ++) (lastPlace acc)) k
             in BasicBlock (reverse (filter (not . placeMark) acc) ++ [Ghost names (GhostValidation fact), Ghost Map.empty (GhostValidation (Assume (FApp (CTerm (builtinFunct (T.Rel Eq))) [CTerm (VInt 0), CTerm (VInt 1)])))]) Return
        lastPlace acc = case [p | Ghost _ (GhostValidation (AssignProofVar n _)) <- acc, Just p <- [stripPrefix placePrefix n]] of
            p : _ -> Just p
            [] -> Nothing
    inRange k = k >= 0 && k < xCount x
    parameter k = xElements x !! fromInteger k

-- The fact an index k of the pack needs, which fails: 0 <= k, or k < N, with the names its message reads (the get and where
-- the program wrote it), which the environment gives their numbers
rangeFact :: X -> String -> Integer -> (ValidationStatement, Env)
rangeFact x place k =
    ( if k < 0 then ProofAssert (FApp (CTerm (builtinFunct (T.Rel LtEq))) [CTerm (VInt 0), ATerm index]) else ProofAssert (FApp (CTerm (builtinFunct (T.Rel Lt))) [ATerm index, ATerm count])
    , Map.fromList [(index, Const (CInt k)), (count, Const (CInt (xCount x)))]
    )
  where
    index = "the index " ++ show k ++ " of get(" ++ xName x ++ ", ...)" ++ place
    count = show (xCount x) ++ (if xCount x == 1 then " argument" else " arguments")

-- Contracts and the validator's statements: size(args) is the number, get(args, k) the parameter at k (and a statement with
-- one out of range is the fact that k is in range, which fails), and a forall over the indices of the pack is a fact for
-- each, its element's type that argument's (the name of a call through its bound is the one at k)
packProofs :: X -> Function -> Either String Function
packProofs x fn = do
    let spec = fnSpec fn
    requires <- concat <$> mapM (validations x{xWhere = " in a contract"}) (specRequires spec)
    ensures <- concat <$> mapM (validations x{xWhere = " in a contract"}) (specEnsures spec)
    loops <- mapM (\l -> (\inv -> l{loopInvariant = map fst inv, loopEnv = Map.unions (loopEnv l : map snd inv)}) . concat <$> mapM (validations x{xNames = namesIn (loopEnv l), xDefines = defined}) (loopInvariant l)) (specLoops spec)
    blocks <- mapM (\(BasicBlock ss t) -> (\ss' -> BasicBlock ss' t) <$> walk Nothing defined ss) (fnBlocks fn)
    Right fn{fnBlocks = blocks, fnSpec = spec{specRequires = map fst requires, specEnsures = map fst ensures, specLoops = loops, specEnv = Map.unions (specEnv spec : map snd (requires ++ ensures))}}
  where
    known = constantsOf x fn
    -- (a name an environment gives a number the copy knows: the index of an iteration, or a local that is a constant)
    namesIn env = Map.mapMaybe (\o -> case o of
        Const (CInt k) -> Just k
        Copy l | Just (CInt k) <- Map.lookup l known -> Just k
        _ -> Nothing) env
    -- (the statements of a block in order: the place lowering marked last is where a statement is in the source, and a
    -- name a define gave an element of the pack at an index the copy fixes is that element, for the calls through its bound)
    walk _ _ [] = Right []
    walk place defs (s : rest)
        | placeMark s = walk (placeOf s) defs rest
    walk place defs (s : rest) = case s of
        Ghost env (GhostValidation v) -> do
            let x' = x{xNames = namesIn env, xWhere = maybe "" (" at line " ++) place, xDefines = defs}
            ws <- validations x' v
            let defs' = case v of
                    AssignProofVar n e -> maybe (Map.delete n defs) (\k -> Map.insert n k defs) (defineIndex x' e)
                    _ -> defs
            (map (\(w, names) -> Ghost (Map.union names env) (GhostValidation w)) ws ++) <$> walk place defs' rest
        _ -> (s :) <$> walk place defs rest
    placeOf s = case s of
        Ghost _ (GhostValidation (AssignProofVar n _)) -> stripPrefix placePrefix n
        _ -> Nothing
    -- (a name defined once in the function, from an element at a fixed index, is that element in every block)
    defined =
        Map.mapMaybe id $
            Map.fromListWith (\_ _ -> Nothing)
                [ (n, defineIndex x{xNames = namesIn env} e)
                | BasicBlock ss _ <- Map.elems (fnBlocks fn)
                , Ghost env (GhostValidation (AssignProofVar n e)) <- ss
                , not (placePrefix `isPrefixOf` n)
                ]

validations :: X -> ValidationStatement -> Either String [(ValidationStatement, Env)]
validations x v = case v of
    ProofAssert (Forall i guards body) | mentionsIndex i body -> unrolled ProofAssert i guards body
    Assume (Forall i guards body) | mentionsIndex i body -> unrolled Assume i guards body
    _ -> one v
  where
    -- (a forall whose body reads the pack at an index made of its own is one fact for each index of its range, which each
    -- copy knows)
    unrolled make i guards body = case (lowerBound i guards >>= foldProof x, upperBound i guards >>= foldProof x) of
        (Just lo, Just hi) -> concat <$> mapM (\k -> one (make (substitute i k body))) [lo .. hi - 1]
        _ -> Left ("Type error: a forall over the elements of " ++ xName x ++ " is written forall i in lo..hi with bounds fixed in each copy (numbers, size(" ++ xName x ++ "), and + - * of those)")
    one w = case w of
        ProofAssert p -> wrap ProofAssert p
        Assume p -> wrap Assume p
        Rewrite (Refl p) -> wrap (Rewrite . Refl) p
        Rewrite (CheckGtZero p) -> wrap (Rewrite . CheckGtZero) p
        Rewrite (CheckRel p) -> wrap (Rewrite . CheckRel) p
        Rewrite (UserRewrite _ ps) | (k : _) <- mapMaybe (definedOutOfRange x) ps -> Right [rangeFact x (xWhere x) k]
        Rewrite (UserRewrite n ps) -> do
            terms <- mapM (proofTerm x . boundCalls x) ps
            case sequence terms of
                Right ps' -> Right [(Rewrite (UserRewrite n ps'), Map.empty)]
                Left k -> Right [rangeFact x (xWhere x) k]
        AssignProofVar _ e | Just k <- definedOutOfRange x (exprToProof e) -> Right [rangeFact x (xWhere x) k]
        AssignProofVar n e -> do
            term <- expressionTerm x e
            case term of
                Right e' -> Right [(AssignProofVar n e', Map.empty)]
                Left k -> Right [rangeFact x (xWhere x) k]
        _ -> Right [(w, Map.empty)]
    wrap make p | Just k <- definedOutOfRange x p = Right [rangeFact x (xWhere x) k]
    wrap make p = case proofTerm x (boundCalls x p) of
        Right (Right p') -> Right [(make p', Map.empty)]
        Right (Left k) -> Right [rangeFact x (xWhere x) k]
        Left e -> Left e
    mentionsIndex i p = case p of
        FApp f [ATerm a, e] | a == xName x, isGet f -> mentions i e || mentionsIndex i e
        FApp f args -> mentionsIndex i f || any (mentionsIndex i) args
        Forall _ gs b -> any (mentionsIndex i) gs || mentionsIndex i b
        _ -> False
    mentions i e = case e of
        BVar j -> j == i
        ATerm j -> j == i
        FApp f args -> mentions i f || any (mentions i) args
        _ -> False
    isIndex i e = case e of
        BVar j -> j == i
        ATerm j -> j == i
        _ -> False
    lowerBound i guards = case [lo | FApp f [lo, e] <- guards, isRel LtEq f, isIndex i e] ++ [lo | FApp f [e, lo] <- guards, isRel GtEq f, isIndex i e] of
        lo : _ -> Just lo
        [] -> Nothing
    upperBound i guards = case [hi | FApp f [e, hi] <- guards, isRel Lt f, isIndex i e] ++ [hi | FApp f [hi, e] <- guards, isRel Gt f, isIndex i e] of
        hi : _ -> Just hi
        [] -> Nothing
    substitute i k p = case p of
        BVar j | j == i -> CTerm (VInt k)
        ATerm j | j == i -> CTerm (VInt k)
        FApp f args -> FApp (substitute i k f) (map (substitute i k) args)
        Forall j gs b | j /= i -> Forall j (map (substitute i k) gs) (substitute i k b)
        _ -> p

-- A call through a bound of an element of the pack read at an index that is not a number (`<$param ..T@n as Tr>::f`), given
-- that element at an index that comes to k in the copy, is the call of the argument at k (`..T#k`)
boundCalls :: X -> VariableProof -> VariableProof
boundCalls x p = case p of
    FApp (ATerm name) (arg@(ATerm n) : rest)
        | Just k <- Map.lookup n (xDefines x), k >= 0, k < xCount x, Just name' <- atElement k name -> FApp (ATerm name') (arg : map (boundCalls x) rest)
    FApp (ATerm name) (arg@(FApp g [ATerm a, e]) : rest)
        | a == xName x, isGet g, Just k <- foldProof x e, Just name' <- atElement k name -> FApp (ATerm name') (arg : map (boundCalls x) rest)
    FApp f args -> FApp (boundCalls x f) (map (boundCalls x) args)
    Forall j gs b -> Forall j (map (boundCalls x) gs) (boundCalls x b)
    _ -> p
  where
    prefix = "<$param " ++ xType x ++ "@"
    atElement k name = case splitAt (length prefix) name of
        (start, rest) | start == prefix, (_ : _, after) <- span isDigit rest, " as " `isPrefixOf` after -> Just ("<$param " ++ xType x ++ "#" ++ show k ++ after)
        _ -> Nothing

-- A statement with the names of defines renamed: the name a define gives by the first map, the names it reads by the second
renameDefines :: Map Variable Variable -> Map Variable Variable -> Statement -> Statement
renameDefines targets uses s = case s of
    Ghost env (GhostValidation v) -> Ghost env (GhostValidation (renameValidation targets uses v))
    _ -> s

renameValidation :: Map Variable Variable -> Map Variable Variable -> ValidationStatement -> ValidationStatement
renameValidation targets uses v = case v of
    ProofAssert p -> ProofAssert (renameProof uses p)
    Assume p -> Assume (renameProof uses p)
    AssignProofVar n e -> AssignProofVar (Map.findWithDefault n n targets) (renameExpression uses e)
    Rewrite (Refl p) -> Rewrite (Refl (renameProof uses p))
    Rewrite (CheckGtZero p) -> Rewrite (CheckGtZero (renameProof uses p))
    Rewrite (CheckRel p) -> Rewrite (CheckRel (renameProof uses p))
    Rewrite (UserRewrite n ps) -> Rewrite (UserRewrite n (map (renameProof uses) ps))
    _ -> v

renameTermination :: Map Variable Variable -> Termination -> Termination
renameTermination names t = case t of
    Shrinks e -> Shrinks (renameExpression names e)
    Counting e -> Counting (renameExpression names e)
    Parts e -> Parts (renameExpression names e)

renameProof :: Map Variable Variable -> VariableProof -> VariableProof
renameProof names p = case p of
    ATerm a -> ATerm (Map.findWithDefault a a names)
    FApp f args -> FApp (renameProof names f) (map (renameProof names) args)
    Forall j gs b -> Forall j (map (renameProof names) gs) (renameProof names b)
    _ -> p

renameExpression :: Map Variable Variable -> Expression -> Expression
renameExpression names e = case e of
    Var a -> Var (Map.findWithDefault a a names)
    F f args -> F (renameExpression names f) (map (renameExpression names) args)
    _ -> e

-- The blocks each block of a loop body is reached through from its start (itself included)
bodyDominators :: BlockId -> [(BlockId, [BlockId])] -> Map BlockId (Set.Set BlockId)
bodyDominators entry graph = go initial
  where
    blocks = map fst graph
    everything = Set.fromList blocks
    preds b = [a | (a, cs) <- graph, b `elem` cs]
    initial = Map.fromList [(b, if b == entry then Set.singleton b else everything) | b <- blocks]
    go doms =
        let step b
                | b == entry = Set.singleton b
                | otherwise = case [Map.findWithDefault everything p doms | p <- preds b] of
                    [] -> Set.singleton b
                    ds -> Set.insert b (foldr1 Set.intersection ds)
            next = Map.fromList [(b, step b) | b <- blocks]
         in if next == doms then doms else go next

-- The index of the element of the pack a define's expression is, when the copy fixes it (in range or not)
definedElement :: X -> Expression -> Maybe Integer
definedElement x e = case e of
    F (Val (VFunct _ _ _ (BuiltinFunct (T.Field (Just "$pack") field)) _)) [Var a] | a == xName x, all isDigit field, not (null field) -> Just (read field)
    F (Val (VFunct _ _ _ (BuiltinFunct T.Get) _)) [Var a, i] | a == xName x -> foldProof x (exprToProof i)
    F (Var "get") [Var a, i] | a == xName x -> foldProof x (exprToProof i)
    _ -> Nothing

-- What a name a define gives stands for: the element at an index the copy fixes, or a read out of range (whose index makes
-- every proof that reads the name the fact that it is in range)
defineIndex :: X -> Expression -> Maybe Integer
defineIndex x e = case definedElement x e of
    Just k -> Just k
    Nothing -> case definedOutOfRange x (exprToProof e) of
        Just k -> Just k
        Nothing -> case expressionTerm x e of
            Right (Left k) -> Just k
            _ -> Nothing

-- The index of an element out of range that a name a proof reads was defined as: the copy has no such element, so the proof
-- is the fact that the index is in range, as it is for get(args, k) written in it
definedOutOfRange :: X -> VariableProof -> Maybe Integer
definedOutOfRange x p = case p of
    ATerm a | Just k <- Map.lookup a (xDefines x), k < 0 || k >= xCount x -> Just k
    FApp f args -> case mapMaybe (definedOutOfRange x) (f : args) of
        k : _ -> Just k
        [] -> Nothing
    Forall _ gs b -> case mapMaybe (definedOutOfRange x) (b : gs) of
        k : _ -> Just k
        [] -> Nothing
    _ -> Nothing

-- An expression of a define with size(args) and get(args, k) put in, or the k of a get out of range
expressionTerm :: X -> Expression -> Either String (Either Integer Expression)
expressionTerm x e = case e of
    F f [Var a] | a == xName x, isSizeE f -> Right (Right (Val (VInt (xCount x))))
    F (Val (VFunct _ _ _ (BuiltinFunct (T.Field (Just "$pack") field)) _)) [Var a] | a == xName x, all isDigit field, not (null field) ->
        let k = read field
         in if k >= 0 && k < xCount x then Right (Right (Var (elementName x k))) else Right (Left k)
    F (Var name) (arg@(F (Val (VFunct _ _ _ (BuiltinFunct (T.Field (Just "$pack") field)) _)) [Var a]) : rest)
        | a == xName x, all isDigit field, not (null field), Just name' <- atElementE (read field :: Integer) name -> expressionTerm x (F (Var name') (arg : rest))
    F f [Var a, i] | a == xName x, isGetE f -> case foldProof x (exprToProof i) of
        Just k | k >= 0 && k < xCount x -> Right (Right (Var (elementName x k)))
        Just k -> Right (Left k)
        Nothing -> Left (notFixed x)
    F (Var name) (arg@(F g [Var a, i]) : rest)
        | a == xName x, isGetE g, Just k <- foldProof x (exprToProof i), Just name' <- atElementE k name -> expressionTerm x (F (Var name') (arg : rest))
    F f args -> do
        f' <- expressionTerm x f
        args' <- mapM (expressionTerm x) args
        Right (F <$> f' <*> sequence args')
    _ -> Right (Right e)
  where
    isSizeE f = case f of
        Val (VFunct _ _ _ (BuiltinFunct T.Size) _) -> True
        Var "size" -> True
        _ -> False
    isGetE f = case f of
        Val (VFunct _ _ _ (BuiltinFunct T.Get) _) -> True
        Var "get" -> True
        _ -> False
    prefix = "<$param " ++ xType x ++ "@"
    atElementE k name = case splitAt (length prefix) name of
        (start, rest) | start == prefix, (_ : _, after) <- span isDigit rest, " as " `isPrefixOf` after -> Just ("<$param " ++ xType x ++ "#" ++ show k ++ after)
        _ -> Nothing

-- The ghost lowering writes before a read of the pack, with the place in the source it is at (MirLower.markPackReads)
placePrefix :: String
placePrefix = "$pack read at "

placeMark :: Statement -> Bool
placeMark s = case s of
    Ghost _ (GhostValidation (AssignProofVar n _)) -> placePrefix `isPrefixOf` n
    _ -> False

notFixed :: X -> String
notFixed x = "Type error: get(" ++ xName x ++ ", i) in a contract or a validation statement needs an index fixed in each copy (numbers, size(" ++ xName x ++ "), the index of a forall over " ++ xName x ++ ", and + - * of those)"

isGet :: VariableProof -> Bool
isGet f = case f of
    CTerm (VFunct _ _ _ (BuiltinFunct T.Get) _) -> True
    ATerm "get" -> True
    _ -> False

isSize :: VariableProof -> Bool
isSize f = case f of
    CTerm (VFunct _ _ _ (BuiltinFunct T.Size) _) -> True
    ATerm "size" -> True
    _ -> False

isRel :: Rel -> VariableProof -> Bool
isRel rel f = case f of
    CTerm (VFunct _ _ _ (BuiltinFunct (T.Rel r)) _) -> r == rel
    _ -> False

-- A proof with size(args) and get(args, k) put in, or the k of a get out of range
proofTerm :: X -> VariableProof -> Either String (Either Integer VariableProof)
proofTerm x p = case p of
    FApp f [ATerm a] | a == xName x, isSize f -> Right (Right (CTerm (VInt (xCount x))))
    FApp f [ATerm a, e] | a == xName x, isGet f -> case foldProof x e of
        Just k | k >= 0 && k < xCount x -> Right (Right (ATerm (elementName x k)))
        Just k -> Right (Left k)
        Nothing -> Left (notFixed x)
    FApp f args -> do
        f' <- proofTerm x f
        args' <- mapM (proofTerm x) args
        Right (FApp <$> f' <*> sequence args')
    Forall i gs b -> do
        gs' <- mapM (proofTerm x) gs
        b' <- proofTerm x b
        Right (Forall i <$> sequence gs' <*> b')
    _ -> Right (Right p)

foldProof :: X -> VariableProof -> Maybe Integer
foldProof x p = case p of
    CTerm (VInt k) -> Just k
    ATerm a | Just k <- Map.lookup a (xNames x) -> Just k
    BVar a | Just k <- Map.lookup a (xNames x) -> Just k
    FApp f [ATerm a] | a == xName x, isSize f -> Just (xCount x)
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct b) _)) [l, r] -> do
        a <- foldProof x l
        c <- foldProof x r
        case b of
            T.Plus -> Just (a + c)
            T.Minus -> Just (a - c)
            T.Times -> Just (a * c)
            _ -> Nothing
    _ -> Nothing

-- The locals no statement, terminator or environment of the copy mentions any more (those of a block an index out of range
-- cut short, or of a branch the copy does not take), which would keep element types no argument has
dropUnused :: Function -> Function
dropUnused fn = fn{fnLocals = Map.filterWithKey (\l _ -> l == Local 0 || l `elem` fnParams fn || Set.member l used) (fnLocals fn)}
  where
    used = Set.fromList (concatMap blockLocals (Map.elems (fnBlocks fn)) ++ concatMap envLocals (specEnv (fnSpec fn) : map loopEnv (Map.elems (specLoops (fnSpec fn)))))
    blockLocals (BasicBlock ss t) = concatMap statementLocals ss ++ terminatorLocals t
    envLocals env = concatMap operandLocals (Map.elems env)
    operandLocals o = case o of
        Copy l -> [l]
        Move l -> [l]
        _ -> []
    statementLocals s = case s of
        Assign d rv -> d : rvalueLocals rv
        Peek d rv -> d : rvalueLocals rv
        AssignRef r steps rv -> r : concat [operandLocals o | RefIndex o <- steps] ++ rvalueLocals rv
        Drop l -> [l]
        Ghost env g -> envLocals env ++ (case g of GhostDissolve l -> [l]; _ -> [])
    rvalueLocals rv = case rv of
        Borrow r steps _ -> r : concat [operandLocals o | RefIndex o <- steps]
        TakeField l _ _ -> [l]
        _ -> concatMap operandLocals (rvalueOperandsOf rv)
    terminatorLocals t = case t of
        SwitchBool o _ _ -> operandLocals o
        Call f as d _ -> d : concatMap operandLocals (f : as)
        _ -> []
    rvalueOperandsOf rv = case rv of
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
        Deref o -> [o]
        _ -> []

-- The environments name each parameter of the pack (`args 0`, ...) instead of the pack
spreadEnvs :: X -> Function -> Function
spreadEnvs x fn =
    fn
        { fnBlocks = Map.map (\(BasicBlock ss t) -> BasicBlock (map statement ss) t) (fnBlocks fn)
        , fnSpec = spec{specEnv = spread (specEnv spec), specLoops = Map.map (\l -> l{loopEnv = spread (loopEnv l)}) (specLoops spec)}
        }
  where
    spec = fnSpec fn
    statement s = case s of
        Ghost env g -> Ghost (spread env) g
        _ -> s
    spread env
        | any isPack (Map.elems env) =
            Map.union (Map.filter (not . isPack) env) (Map.fromList [(elementName x k, Copy l) | (k, l) <- zip [0 ..] (xElements x)])
        | otherwise = env
    isPack o = case o of
        Copy l -> l == xPack x
        Move l -> l == xPack x
        _ -> False

usesLocal :: Local -> Function -> Bool
usesLocal l fn = any blockUses (Map.elems (fnBlocks fn))
  where
    blockUses (BasicBlock ss t) = any statementUses ss || terminatorUses t
    op o = case o of
        Copy m -> m == l
        Move m -> m == l
        _ -> False
    statementUses s = case s of
        Assign d rv -> d == l || rvalueUses rv
        Peek d rv -> d == l || rvalueUses rv
        AssignRef r _ rv -> r == l || rvalueUses rv
        Drop m -> m == l
        Ghost _ _ -> False
    rvalueUses rv = case rv of
        Borrow r steps _ -> r == l || or [op o | RefIndex o <- steps]
        TakeField m _ _ -> m == l
        _ -> any op (operandsOf rv)
    terminatorUses t = case t of
        SwitchBool o _ _ -> op o
        Call f as d _ -> op f || any op as || d == l
        _ -> False
    operandsOf rv = case rv of
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
        Deref o -> [o]
        _ -> []
