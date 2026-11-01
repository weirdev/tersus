module MirValidate
    ( Validated (..)
    , validateProgram
    , validateProgramWithCache
    , validateProgramUncached
    , ValidationCache
    , emptyValidationCache
    , validationCacheHits
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Monad (filterM, foldM, forM_, unless, when)
import Data.Containers.ListUtils (nubOrd)
import Data.List (isInfixOf, isPrefixOf, sort)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe, isNothing, listToMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import Ghost
import qualified Mir as M
import qualified ProofEngine as Engine
import ProofHelpers (proofIotas, proofVars, substituteProofTerm)
import ProofState
import Pretty (renderVarProof)
import StdLib
import Types
import Syntax
import Utils

-- Validation on the MIR: the validator walks the control-flow graph of each function with a state per path (what is known
-- about the values of the locals), checks every operation's contract and the statements the program wrote for the
-- validator (affirm, define, rewrite), and joins the paths where they meet. A loop is checked by its invariant, not
-- by running it. See MIR.md.

-- What validating a program leaves: the names of the program's locals at its end with the facts that hold there
data Validated = Validated
    { vdVars :: Map Variable Iota
    , vdFacts :: [IotaProof]
    , vdReturn :: Maybe Iota
    }
    deriving (Show)

-- The source name of each function defined at the top of the program, from where main defines it
topLevelSources :: M.Program -> Map Name Variable
topLevelSources program = Map.fromList [(name, source) | block <- Map.elems (M.fnBlocks (M.progMain program)), M.Ghost _ (M.GhostFunction name source True) <- M.blockStatements block]

-- What a call of a function is taken to give before its body has been checked: only what its output contract says of its parameters and result
assumedInfo :: M.Program -> Name -> FnInfo
assumedInfo program name =
    case Map.lookup name (M.progFunctions program) of
        Nothing -> FnInfo [] [] [] Nothing (ATerm (fnIota name)) True (KUser name) False []
        Just fn ->
            let spec = M.fnSpec fn
                names = [n | p <- M.fnParams fn, Just d <- [Map.lookup p (M.fnLocals fn)], Just n <- [M.localName d]]
                assumed = [p | ProofAssert p <- M.specEnsures spec, all (`elem` ("return" : names ++ ["$old " ++ n | n <- M.specMutParams spec])) (proofVars p)]
             in FnInfo names (M.specRequires spec) assumed (M.specTermination spec) (ATerm (fnIota name)) True (KUser name) (Set.member name (M.readersOfInput program)) (M.specMutParams spec)

-- What a function depends on: the functions it calls or names, and the ones its contracts and proofs call,
-- since a proof that calls a function uses its contract as a call in the code does. Nested functions are
-- dependencies like any other: a cycle can pass through one.
dependencies :: M.Program -> M.Function -> Set Name
dependencies program fn = Set.intersection (Map.keysSet (M.progFunctions program)) (Set.union (M.functionsNamed fn) (Set.fromList (concatMap statementNames statements)))
  where
    spec = M.fnSpec fn
    statements = M.specRequires spec ++ M.specEnsures spec ++ [vs | block <- Map.elems (M.fnBlocks fn), M.Ghost _ ghost <- M.blockStatements block, vs <- ghostStatements ghost]
    ghostStatements (M.GhostValidation vs) = [vs]
    ghostStatements (M.GhostAxiom _ _ ins outs) = ins ++ outs
    ghostStatements (M.GhostProof _ _ ins outs body) = ins ++ outs ++ body
    ghostStatements _ = []
    statementNames (ProofAssert proof) = proofNames proof
    statementNames (Assume proof) = proofNames proof
    statementNames (AssignProofVar _ expr) = exprNames expr
    statementNames (Rewrite rule) = ruleNames rule
    proofNames (BVar var) = [var]
    proofNames (ATerm var) = [var]
    proofNames (FApp funct args) = proofNames funct ++ concatMap proofNames args
    proofNames (Forall _ guards body) = concatMap proofNames guards ++ proofNames body
    proofNames (CTerm (VFnRef n)) = [n]
    proofNames _ = []
    exprNames (Var var) = [var]
    exprNames (F expr args) = exprNames expr ++ concatMap exprNames args
    exprNames (Val (VFnRef n)) = [n]
    exprNames _ = []
    ruleNames (UserRewrite _ args) = concatMap proofNames args
    ruleNames (Refl proof) = proofNames proof
    ruleNames (CheckGtZero proof) = proofNames proof
    ruleNames (CheckRel proof) = proofNames proof
    ruleNames _ = []

-- The group of a function defined at the top: the top-level functions that depend on it and that it
-- depends on, in a cycle, or just itself. Only they are members (a cycle can still pass through a nested
-- function, which is a dependency on the way). A function defined inside another is in no group of its
-- own: it can call the one around it only under the rule for that (both declared ~), which the recursive
-- call itself checks.
callGroup :: M.Program -> Name -> Set Name
callGroup program name = Set.filter (\other -> Set.member other tops && Set.member name (reach other)) (reach name)
  where
    fns = M.progFunctions program
    tops = Map.keysSet (topLevelSources program)
    callees n = maybe Set.empty (dependencies program) (Map.lookup n fns)
    reach n = go Set.empty [n]
      where
        go seen [] = seen
        go seen (x : xs)
            | Set.member x seen = go seen xs
            | otherwise = go (Set.insert x seen) (Set.toList (callees x) ++ xs)

{-# NOINLINE processValidationCache #-}
processValidationCache :: MVar ValidationCache
processValidationCache = unsafePerformIO (newMVar emptyValidationCache)

{-# NOINLINE validateProgram #-}
validateProgram :: M.Program -> Result Validated String
validateProgram program = unsafePerformIO $ modifyMVar processValidationCache $ \cache ->
    case validateProgramWithCache cache program of
        Error e -> pure (cache, Error e)
        Ok (validated, cache') -> pure (cache', Ok validated)

validateProgramWithCache :: ValidationCache -> M.Program -> Result (Validated, ValidationCache) String
validateProgramWithCache cache = runVWithCache cache . validateProgramV

validateProgramUncached :: M.Program -> Result Validated String
validateProgramUncached = runV . validateProgramV

validateProgramV :: M.Program -> V Validated
validateProgramV program = do
    let main' = M.progMain program
        seeded = (initialPState program){psFns = Map.fromList [(name, assumedInfo program name) | name <- Map.keys (topLevelSources program)]}
        st0 = withFunctions main' seeded
    returned <- walkFunction st0 main'
    -- (a function whose definition main never reaches, past a return, has still to be checked)
    let validated = Set.unions (map psValidated returned)
    mapM_ (\name -> inImplCheck name (validateFunction st0 name True)) [name | name <- Map.keys (topLevelSources program), not (Set.member name validated)]
    case returned of
        [] -> return (Validated Map.empty (allFacts st0) Nothing)
        _ -> do
            st <- joinAll returned
            let names = Map.fromList [(n, iota) | (l, iota) <- Map.toList (psLocals st), Just d <- [Map.lookup l (M.fnLocals main')], Just n <- [M.localName d]]
            return (Validated (Map.union names (psVars st)) (allFacts st) (Map.lookup (M.Local 0) (psLocals st)))

-- A function's graph and what is known of its loops
data Ctx = Ctx
    { cxFn :: M.Function
    , cxOrder :: [M.BlockId] -- the blocks a walk from the entry reaches, each after the blocks that jump to it (apart from a loop's back edge)
    , cxLoops :: Map M.BlockId LoopInfo
    }

data LoopInfo = LoopInfo
    { liSpec :: M.LoopSpec
    , liRegion :: Set M.BlockId -- the header and every block that can get back to it
    }

mkCtx :: M.Function -> Ctx
mkCtx fn = Ctx fn order loops
  where
    blocks = M.fnBlocks fn
    succs b = maybe [] (M.successors . M.blockTerminator) (Map.lookup b blocks)
    -- reverse postorder, and the edges that go back to a block still being walked (a loop's back edges)
    (order, backEdges) = let (_, acc, _, es) = dfs (Set.empty, [], Set.empty, []) (M.BlockId 0) in (acc, es)
    dfs (seen, acc, active, es) b
        | Set.member b seen = (seen, acc, active, es)
        | otherwise =
            let step (sn, ac, ct, e) t
                    | Set.member t ct = (sn, ac, ct, (b, t) : e)
                    | otherwise = dfs (sn, ac, ct, e) t
                (seen', acc', _, es') = foldl step (Set.insert b seen, acc, Set.insert b active, es) (succs b)
             in (seen', b : acc', active, es')
    preds = Map.fromListWith (++) [(t, [b]) | b <- Map.keys blocks, t <- succs b]
    loops =
        Map.mapWithKey
            ( \h spec ->
                let backs = [u | (u, t) <- backEdges, t == h]
                 in LoopInfo spec (region h backs)
            )
            (M.specLoops (M.fnSpec fn))
    -- the blocks that reach a block that jumps back, without passing the header
    region h backs = go (Set.singleton h) backs
      where
        go seen [] = seen
        go seen (x : xs)
            | Set.member x seen = go seen xs
            | otherwise = go (Set.insert x seen) (Map.findWithDefault [] x preds ++ xs)

-- The paths of a walk that left the blocks it was given, the ones that went back to the start of a loop, and the ones that
-- returned
data Walked = Walked
    { wdExits :: [(M.BlockId, PState)]
    , wdBacks :: [PState]
    , wdReturns :: [PState]
    }

noWalk :: Walked
noWalk = Walked [] [] []

-- What a loop being walked needs besides its blocks: its header, its invariant, its environment, and what shrinks
data LoopRun = LoopRun
    { lrHeader :: M.BlockId
    , lrBody :: M.BlockId -- the first block of the body, which an iteration starts on entering (a condition of several tests has an edge to it from each that can decide it)
    , lrEnv :: M.Env
    , lrVariant :: Maybe (Variable, Termination, Expression)
    }

-- The states at the returns of a function body, from the entry
walkFunction :: PState -> M.Function -> V [PState]
walkFunction st fn = do
    let cx = mkCtx fn
        region = Set.fromList (cxOrder cx)
        named = st{psLocalNames = Map.fromList [(l, n) | (l, d) <- Map.toList (M.fnLocals fn), Just n <- [M.localName d]]}
    walked <- walk cx Nothing region (M.BlockId 0) named
    return (wdReturns walked)

-- Walks the blocks of a region from the entry, each when the paths that jump to it have been walked
walk :: Ctx -> Maybe LoopRun -> Set M.BlockId -> M.BlockId -> PState -> V Walked
walk cx run region entry start = go order (Map.singleton entry [start]) noWalk
  where
    order = filter (`Set.member` region) (cxOrder cx)
    isLoopWalk = case run of
        Just _ -> True
        Nothing -> False
    go [] _ acc = return acc{wdExits = reverse (wdExits acc), wdBacks = reverse (wdBacks acc), wdReturns = reverse (wdReturns acc)}
    go (b : rest) pending acc =
        case Map.lookup b pending of
            Nothing -> go rest pending acc
            Just incoming -> do
                walked <-
                    if b == entry
                        then processBlock cx run b (head incoming)
                        else case Map.lookup b (cxLoops cx) of
                            Just info -> enterLoop cx b info (reverse incoming)
                            Nothing -> joinStates cx b (reverse incoming) >>= processBlock cx run b
                let (pending', acc') = foldl route (Map.delete b pending, acc{wdReturns = reverse (wdReturns walked) ++ wdReturns acc}) (wdExits walked)
                    acc'' = acc'{wdBacks = reverse (wdBacks walked) ++ wdBacks acc'}
                go rest pending' acc''
    route (pending, acc) (target, st)
        | target == entry && isLoopWalk = (pending, acc{wdBacks = st : wdBacks acc})
        | Set.member target region = (Map.insertWith (++) target [st] pending, acc)
        | otherwise = (pending, acc{wdExits = (target, st) : wdExits acc})

-- The paths out of a block: where each goes, and which return
processBlock :: Ctx -> Maybe LoopRun -> M.BlockId -> PState -> V Walked
processBlock cx run b st0 = do
    let M.BasicBlock stmts term = M.fnBlocks (cxFn cx) Map.! b
    -- (an iteration of a loop starts when its body is entered, once the ways in have met: a condition of several tests has several)
    started <- case run of
        Just r | lrBody r == b -> startIteration r st0
        _ -> return st0
    st <- foldM (execStatement cx) started stmts
    case term of
        M.Goto target -> return noWalk{wdExits = [(target, st)]}
        M.SwitchBool test yes no -> do
            cond <- operandTerm st test
            case cond of
                CTerm (VBool True) -> return noWalk{wdExits = [(yes, st)]}
                CTerm (VBool False) -> return noWalk{wdExits = [(no, st)]}
                _ -> do
                    let stYes = addFacts st (branchFacts st cond True)
                        stNo = addFacts st (branchFacts st cond False)
                    return noWalk{wdExits = [(yes, stYes), (no, stNo)]}
        M.Call callee args dest next -> do
            calleeTerm <- operandTerm st callee
            argTerms <- mapM (operandTerm st) args
            info <- liftR (resolveFunction st calleeTerm)
            result <- fresh
            let mutNames = fnMutParams info
            posts <- freshN (length mutNames)
            st' <- applyCall st info argTerms result (zip mutNames posts)
            st'' <- versionMutArgs cx st' info args (zip mutNames posts)
            return noWalk{wdExits = [(next, forgetProofVar dest (withTypeFacts (cxFn cx) dest st''{psLocals = Map.insert dest result (psLocals st'')}))]}
        M.Return -> return noWalk{wdReturns = [st]}
        M.Unreachable
            | unreachable st -> return noWalk
            | otherwise -> throwV "Return value not found: the function can end without returning"

-- What a branch of an if or a loop knows: the truth of its condition, and the relation when the condition compares
branchFacts :: PState -> IotaProof -> Bool -> [IotaProof]
branchFacts st cond branch = FApp eqProof [cond, CTerm (VBool branch)] : relation ++ variant
  where
    -- (a value that is a variant is that variant built from its own fields, so two values of one variant with equal fields are equal)
    -- (and a value that is not any of the other variants of its enum is the one that is left)
    variant = case cond of
        ATerm iota ->
            concat
                [ if branch then constructedFacts st name [] value else lastVariant name value
                | FApp eq [ATerm lhs, FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is name)) _)) [value]] <- psFacts st
                , eq == eqProof
                , lhs == iota
                ]
        _ -> []
    lastVariant name value =
        let ruledOut = name : [w | FApp eq [ATerm c, FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is w)) _)) [v]] <- psFacts st, eq == eqProof, v == value, FApp eqProof [ATerm c, CTerm (VBool False)] `elem` psFacts st]
         in case [v | v <- enumVariants st name, v `notElem` ruledOut] of
                [left] -> FApp eqProof [FApp (CTerm (builtinFunct (Is left))) [value], CTerm (VBool True)] : constructedFacts st left [] value
                _ -> []
    relation = case cond of
        ATerm iota ->
            [ FApp (CTerm (builtinFunct (Rel rel'))) args
            | FApp eq [ATerm lhs, FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel rel)) _)) args] <- psFacts st
            , eq == eqProof
            , lhs == iota
            , Just rel' <- [if branch then Just rel else negateRel rel]
            ]
        _ -> []

negateRel :: Rel -> Maybe Rel
negateRel Lt = Just GtEq
negateRel Gt = Just LtEq
negateRel LtEq = Just Gt
negateRel GtEq = Just Lt
negateRel Eq = Just NotEq
negateRel NotEq = Just Eq

-- Statements

-- A variable of a proof that has the name of a program variable (`define x = ...` where the program has an `x`) stands for the
-- variable's value from then on, so assigning the program variable is assigning it again
forgetProofVar :: M.Local -> PState -> PState
forgetProofVar dest st = case Map.lookup dest (psLocalNames st) of
    Just name -> st{psVars = Map.delete name (psVars st)}
    Nothing -> st

execStatement :: Ctx -> PState -> M.Statement -> V PState
execStatement cx st (M.Assign dest rv) = do
    st0 <- case rv of
        M.ListOp M.FromList [src] -> checkFromListSize cx st dest src
        _ -> return st
    st1 <- assign st0 dest rv
    let st2 = case rv of
            M.Borrow root steps _ -> st1{psBorrows = Map.insert dest (root, steps) (psBorrows st1)}
            _ -> st1{psBorrows = Map.delete dest (psBorrows st1)}
    st3 <- reversionBorrows st2 dest
    return (forgetProofVar dest (typed st3))
  where
    -- (a local that is another local has its facts already)
    typed = case rv of
        M.Use (M.Copy _) -> id
        _ -> withTypeFacts (cxFn cx) dest
execStatement cx st (M.AssignRef root steps rv) = do
    valueTerm <- case rv of
        M.Use o -> operandTerm st o
        _ -> throwV "An assignment through a reference of a value the validator does not know"
    valueIota <- case valueTerm of
        ATerm iota -> return iota
        _ -> do
            iota <- fresh
            return iota
    st1 <- case valueTerm of
        ATerm _ -> setPlaceVersion st root steps valueIota
        _ -> do
            s1 <- setPlaceVersion st root steps valueIota
            return (addFacts s1 [FApp eqProof [ATerm valueIota, valueTerm]])
    -- (a struct whose field is written is a struct that is made: it has to meet its invariant, as at a construction)
    checkPlaceBounds st1 root steps
    checkWriteInvariants st1 root steps
    st2 <- reversionBorrows st1 root
    return (forgetProofVar root (withTypeFacts (cxFn cx) root st2))
execStatement cx st (M.Ghost env g) = ghostStatement cx st env g

assign :: PState -> M.Local -> M.Rvalue -> V PState
assign st dest rv =
    case rv of
        M.Use o -> do
            term <- operandTerm st o
            case term of
                ATerm iota -> return (bind st iota)
                _ -> do
                    iota <- fresh
                    return (addFacts (bind st iota) [FApp eqProof [ATerm iota, term]])
        M.Borrow root steps _ -> do
            checkPlaceBounds st root steps
            term <- placeTerm st root steps
            case term of
                ATerm iota -> return (bind st iota)
                _ -> do
                    iota <- fresh
                    return (addFacts (bind st iota) [FApp eqProof [ATerm iota, term]])
        -- (what a reference is to is the reference's own version: Borrow bound it to the place's term)
        M.Deref o -> assign st dest (M.Use o)
        M.MakeList _ -> throwV "A list written from variables is not supported by the validator"
        -- (a Box has the value of what it holds)
        M.MakeBox o -> assign st dest (M.Use o)
        M.Unbox o -> assign st dest (M.Use o)
        M.Unsize o -> assign st dest (M.Use o)
        M.CopyOf o -> assign st dest (M.Use o)
        -- (an array made from a list has the value of the list: only its type says how many elements it has)
        M.ListOp M.FromList [o] -> assign st dest (M.Use o)
        _ -> case rvalueCall rv of
            Nothing -> throwV "An operation the validator does not know"
            Just (builtin, operands) -> do
                terms <- mapM (operandTerm st) operands
                -- (a struct that is made has to meet its invariant)
                case builtin of
                    Ctor name _ fields -> checkInvariant st name (zip fields terms)
                    _ -> return ()
                result <- fresh
                st' <- applyCall st (builtinInfo builtin) terms result []
                return (bind st' result)
  where
    bind s iota = s{psLocals = Map.insert dest iota (psLocals s)}

-- The invariant of the struct that a type is, or that a Box of the type holds, as facts about a value of the type
typeInvariants :: PState -> Type -> IotaProof -> [IotaProof]
typeInvariants st ty value = case ty of
    TNamed base args -> invariantFacts st (instanceName base args) value
    TBox inner -> typeInvariants st inner value
    _ -> []

-- What the type of a local says of its value: an array has the size of its type, wherever it came from, so a contract or a
-- loop invariant need not say it
withTypeFacts :: M.Function -> M.Local -> PState -> PState
withTypeFacts fn l st =
    case (M.localType <$> Map.lookup l (M.fnLocals fn), Map.lookup l (psLocals st)) of
        -- (a Byte is from 0 to 255, wherever it came from: it is only ever made from an Int that was proved to be, or read from a list of them)
        (Just TByte, Just iota) -> addFacts st [FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm iota, CTerm (VInt 0)], FApp (CTerm (builtinFunct (Rel Lt))) [ATerm iota, CTerm (VInt 256)]]
        -- (a fixed-width integer is in its range, as a Byte is)
        (Just (TWord signed bits), Just iota) ->
            let (low, high) = wordRange signed bits
             in addFacts st [FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm iota, CTerm (VInt low)], FApp (CTerm (builtinFunct (Rel Lt))) [ATerm iota, CTerm (VInt high)]]
        -- (a permission is to a number of slots that is not negative, and as many of them are filled as count says, which are at most all of them)
        (Just (TBlock _), Just iota) ->
            let app f = FApp (CTerm (VFunct [] [] [] (BuiltinFunct f) [])) [ATerm iota]
             in addFacts st [FApp (CTerm (builtinFunct (Rel GtEq))) [app BlockCap, CTerm (VInt 0)], FApp (CTerm (builtinFunct (Rel GtEq))) [app BlockCount, CTerm (VInt 0)], FApp (CTerm (builtinFunct (Rel LtEq))) [app BlockCount, app BlockCap]]
        (Just (TArray _ n), Just iota) -> sized n iota
        (Just (TBox (TArray _ n)), Just iota) -> sized n iota
        (Just (TArrayOf _ (SizeParam p)), Just iota) -> sizedByParam p iota
        (Just (TBox (TArrayOf _ (SizeParam p))), Just iota) -> sizedByParam p iota
        -- (a struct meets its invariant, wherever it came from, and is built from its fields)
        (Just ty, Just iota) | facts@(_ : _) <- typeInvariants st ty (ATerm iota) ++ structFacts ty (ATerm iota) -> addFacts st facts
        _ -> st
  where
    structFacts ty value = case ty of
        TNamed base args | Just (M.StructDecl _) <- Map.lookup (instanceName base args) (M.progTypes (psProgram st)) -> constructedFacts st (instanceName base args) args value
        TRef t -> structFacts t value
        _ -> []
    sized n iota = addFacts st [FApp eqProof [FApp (CTerm (builtinFunct Size)) [ATerm iota], CTerm (VInt n)]]
    -- (a size parameter is the parameter of the function that is named like it)
    sizedByParam p iota =
        case [value | (param, M.LocalDecl _ (Just name)) <- Map.toList (M.fnLocals fn), name == p, param `elem` M.fnParams fn, Just value <- [Map.lookup param (psLocals st)]] of
            value : _ -> addFacts st [FApp eqProof [FApp (CTerm (builtinFunct Size)) [ATerm iota], ATerm value]]
            [] -> st

-- (an array made from a list has as many elements as the list: where the type of the result gives the number, the list
-- must be proved to have that many, since the size the type says is otherwise taken on trust from here on)
checkFromListSize :: Ctx -> PState -> M.Local -> M.Operand -> V PState
checkFromListSize cx st dest src = do
    let fn = cxFn cx
        destTy = M.localType <$> Map.lookup dest (M.fnLocals fn)
    case destTy of
        Just (TArray _ n) -> check (CTerm (VInt n)) (show n)
        Just (TArrayOf _ (SizeParam p)) ->
            case [value | (param, M.LocalDecl _ (Just name)) <- Map.toList (M.fnLocals fn), name == p, param `elem` M.fnParams fn, Just value <- [Map.lookup param (psLocals st)]] of
                value : _ -> check (ATerm value) p
                [] -> return st
        _ -> return st
  where
    check wanted shown = do
        term <- operandTerm st src
        let proof = FApp eqProof [FApp (CTerm (builtinFunct Size)) [term], wanted]
        st' <- evaluateCalls st [proof]
        if Engine.entails proof (proofContext st')
            then return st
            else throwV ("Could not prove: the list given to Array::fromList has " ++ shown ++ " elements, as the array it is made into does")

-- A value of a struct or a variant is that constructor applied to the fields of the value (which, with congruence, makes two
-- values whose fields are equal equal)
constructedFacts :: PState -> Name -> [Arg] -> IotaProof -> [IotaProof]
constructedFacts st ctor ctorArgs value = case fieldsOf of
    Just fields -> [FApp eqProof [value, FApp (CTerm (builtinFunct (Ctor ctor ctorArgs fields))) [FApp (CTerm (builtinFunct (Field Nothing f))) [value] | f <- fields]]]
    Nothing -> []
  where
    types = M.progTypes (psProgram st)
    fieldsOf = case Map.lookup ctor types of
        Just (M.StructDecl fs) -> Just (map fst fs)
        _ -> listToMaybe [map fst fs | (enum, M.EnumDecl variants) <- Map.toList types, (v, fs) <- variants, v == ctor || enum ++ "::" ++ v == ctor]

-- The variants of the enum that a variant is of, named as the variant is
enumVariants :: PState -> Name -> [Name]
enumVariants st variant =
    head ([[if "::" `isInfixOf` v then v else enum ++ "::" ++ v | (v, _) <- variants] | (enum, M.EnumDecl variants) <- Map.toList (M.progTypes (psProgram st)), any (\(v, _) -> v == variant || enum ++ "::" ++ v == variant) variants] ++ [[]])

-- The term for the value at a place of a local
placeTerm :: PState -> M.Local -> [M.RefStep] -> V IotaProof
placeTerm st root steps = operandTerm st (M.Copy root) >>= \term -> placeTermSteps st term steps

placeTermSteps :: PState -> IotaProof -> [M.RefStep] -> V IotaProof
placeTermSteps _ term [] = return term
placeTermSteps st term (step : rest) = do
    next <- case step of
        M.RefField _ field -> return (FApp (CTerm (builtinFunct (Field Nothing field))) [term])
        M.RefIndex index -> do
            indexTerm <- operandTerm st index
            return (FApp (CTerm (builtinFunct Get)) [term, indexTerm])
    placeTermSteps st next rest

-- After a call, what an update argument is to gets its post-call version: the old version keeps the old facts, and
-- facts about the new one come from the callee's promises, which applyCall has already added (REFERENCES.md)
versionMutArgs :: Ctx -> PState -> FnInfo -> [M.Operand] -> [(Variable, Iota)] -> V PState
versionMutArgs _ st _ _ [] = return st
versionMutArgs cx st info args mutPosts = foldM apply st (zip (fnParamNames info) args)
  where
    apply s (name, operand)
        | Just post <- lookup name mutPosts = case operandLocalOf operand of
            Just l -> do
                let (root, steps) = fromMaybe (l, []) (Map.lookup l (psBorrows s))
                s1 <- setPlaceVersion s root steps post
                s2 <- reversionBorrows (forgetProofVar root s1) root
                return (withTypeFacts (cxFn cx) root s2)
            Nothing -> return s
        | otherwise = return s
    oldRootOf s root = ATerm <$> Map.lookup root (psLocals s)
    operandLocalOf (M.Copy l) = Just l
    operandLocalOf (M.Move l) = Just l
    operandLocalOf _ = Nothing

-- The index steps of a place have to be in the value they index, as an index of `get` is: a reference to an
-- element that is not there is not made, and an assignment through one does not write there
checkPlaceBounds :: PState -> M.Local -> [M.RefStep] -> V ()
checkPlaceBounds st root steps = do
    rootTerm <- operandTerm st (M.Copy root)
    go rootTerm steps
  where
    go _ [] = return ()
    go term (step : rest) = case step of
        M.RefField _ field -> go (FApp (CTerm (builtinFunct (Field Nothing field))) [term]) rest
        M.RefIndex index -> do
            indexTerm <- operandTerm st index
            let sizeTerm = FApp (CTerm (builtinFunct Size)) [term]
                inBounds = Engine.entails (FApp (CTerm (builtinFunct (Rel GtEq))) [indexTerm, CTerm (VInt 0)]) (proofContext st)
                    && Engine.entails (FApp (CTerm (builtinFunct (Rel Lt))) [indexTerm, sizeTerm]) (proofContext st)
            unless inBounds $ throwV "A reference is to an index that is not known to be in the value it borrows"
            go (FApp (CTerm (builtinFunct Get)) [term, indexTerm]) rest

-- Each struct that a write through a reference builds again (the owner of each field step, at its new version)
-- has to meet its invariant, as a struct that is made does (a construction is checked by checkInvariant)
checkWriteInvariants :: PState -> M.Local -> [M.RefStep] -> V ()
checkWriteInvariants st root steps = do
    rootTerm <- operandTerm st (M.Copy root)
    go rootTerm steps
  where
    go _ [] = return ()
    go term (step : rest) = case step of
        M.RefField ctor field -> do
            let fields = case Map.lookup ctor (M.progTypes (psProgram st)) of
                    Just (M.StructDecl fs) -> map fst fs
                    _ -> []
            checkInvariant st ctor [(f, FApp (CTerm (builtinFunct (Field Nothing f))) [term]) | f <- fields]
            go (FApp (CTerm (builtinFunct (Field Nothing field))) [term]) rest
        M.RefIndex index -> do
            indexTerm <- operandTerm st index
            go (FApp (CTerm (builtinFunct Get)) [term, indexTerm]) rest

-- A root's new version, whose place at the steps is the given version: the rest of a struct keeps its fields,
-- the rest of a list or an array is the old one at every other index (which `set` says), and a whole place is it
setPlaceVersion :: PState -> M.Local -> [M.RefStep] -> Iota -> V PState
setPlaceVersion s root steps post = case steps of
    [] -> return s{psLocals = Map.insert root post (psLocals s)}
    [M.RefField ctor field] -> do
        newRoot <- fresh
        let fieldOf t f = FApp (CTerm (builtinFunct (Field Nothing f))) [t]
            fields = case Map.lookup ctor (M.progTypes (psProgram s)) of
                Just (M.StructDecl fs) -> map fst fs
                _ -> [field]
            oldRootTerm = fromMaybe (ATerm post) (ATerm <$> Map.lookup root (psLocals s))
            facts = [FApp eqProof [fieldOf (ATerm newRoot) field, ATerm post]]
                ++ [FApp eqProof [fieldOf (ATerm newRoot) f, fieldOf oldRootTerm f] | f <- fields, f /= field]
        return (addFacts s{psLocals = Map.insert root newRoot (psLocals s)} facts)
    [M.RefIndex index] -> do
        indexTerm <- operandTerm s index
        newRoot <- fresh
        let oldRootTerm = fromMaybe (ATerm post) (ATerm <$> Map.lookup root (psLocals s))
        return (addFacts s{psLocals = Map.insert root newRoot (psLocals s)} [FApp eqProof [ATerm newRoot, FApp (CTerm (builtinFunct Set)) [oldRootTerm, indexTerm, ATerm post]]])
    _ -> do
        newRoot <- fresh
        term <- placeTermSteps s (ATerm newRoot) steps
        return (addFacts s{psLocals = Map.insert root newRoot (psLocals s)} [FApp eqProof [term, ATerm post]])

-- After an assignment to a local, the reference locals that are to a place of it see its new version
reversionBorrows :: PState -> M.Local -> V PState
reversionBorrows st dest = do
    let targets = [(ref, steps) | (ref, (root, steps)) <- Map.toList (psBorrows st), root == dest, ref /= dest]
    case Map.lookup dest (psLocals st) of
        Nothing -> return st
        Just rootIota -> foldM (\s (ref, steps) -> do
            term <- placeTermSteps s (ATerm rootIota) steps
            case term of
                ATerm iota -> return s{psLocals = Map.insert ref iota (psLocals s)}
                _ -> do
                    iota <- fresh
                    return (addFacts s{psLocals = Map.insert ref iota (psLocals s)} [FApp eqProof [ATerm iota, term]])) st targets

-- The term for the value of an operand
operandTerm :: PState -> M.Operand -> V IotaProof
operandTerm st (M.Copy l) =
    case Map.lookup l (psLocals st) of
        Just iota -> return (ATerm iota)
        Nothing -> throwV ("Undefined variable: " ++ show l)
operandTerm st (M.Const (M.CFn name))
    | Map.member name (psFns st) = return (ATerm (fnIota name))
    | otherwise = case wrapperInfo st name of
        Just _ -> return (ATerm (fnIota name))
        Nothing -> throwV ("Undefined variable: " ++ name ++ " (a function must be defined before the functions that call it)")
operandTerm st (M.Const c) = checkConstant c >> return (constantValue c)
  where
    -- (a struct written as a constant is made here, so it meets its invariant)
    checkConstant constant = case constant of
        M.CData name fields -> do
            mapM_ (checkConstant . snd) fields
            checkInvariant st name [(f, constantValue v) | (f, v) <- fields]
        M.CList cs -> mapM_ checkConstant cs
        M.CArray cs -> mapM_ checkConstant cs
        _ -> return ()

-- Ghost statements

ghostStatement :: Ctx -> PState -> M.Env -> M.GhostStatement -> V PState
ghostStatement _ st env g =
    case g of
        M.GhostValidation vs -> runStatements (withEnv env st) [vs]
        M.GhostAxiom name args ins outs -> defineAxiom st name args ins outs
        M.GhostProof name args ins outs body -> defineProofRule st name args ins outs body
        M.GhostFunction name source top -> defineFunction st name source top
        M.GhostPosition _ _ -> return st
        M.GhostDissolve _ -> return st

-- A function is validated where it is defined: its body, against what holds everywhere, and its output contract.
-- The functions of a mutually recursive group are validated together there: each body is checked against the
-- contracts of the others, which is all a call of one of them ever learns.
defineFunction :: PState -> Name -> Variable -> Bool -> V PState
defineFunction st name source top
    | not top = do
        info <- inImplCheck name (validateFunction st name top)
        return st{psFns = Map.insert name info (psFns st)}
    | Set.member name (psValidated st) = return st
    | Map.member source (psGlobals st) = throwV ("Function already defined: " ++ source)
    | otherwise = do
        let program = psProgram st
            group = callGroup program name
            sources = topLevelSources program
            members = Set.toList group
            termOf member = maybe Nothing (M.specTermination . M.fnSpec) (Map.lookup member (M.progFunctions program))
        when (Set.size group > 1 && not (all (== Just MayDiverge) (map termOf members)) && any (== Nothing) (map termOf members)) $
            throwV "Mutually recursive functions must say what shrinks, or be declared ~"
        -- (each member is seen by the others as it sees itself: a call of it is a recursive call, checked against the caller's variant)
        let stGroup = st{psFns = foldr (\member m -> Map.adjust (\info -> info{fnTermination = Just (Recursing (termOf member))}) member m) (psFns st) members}
        infos <- mapM (\member -> inImplCheck member (validateFunction stGroup member True)) members
        let st' =
                st
                    { psFns = foldr (\(member, info) m -> Map.insert member info m) (psFns st) (zip (Set.toList group) infos)
                    , psValidated = Set.union group (psValidated st)
                    , psGlobals = foldr (\member m -> maybe m (\src -> Map.insert src (fnIota member) m) (Map.lookup member sources)) (psGlobals st) (Set.toList group)
                    }
        return st'

-- The function that stands for the check that an impl meets its trait fails with the reason, and says which impl
inImplCheck :: Name -> V a -> V a
inImplCheck name action =
    case parseImplCheckName name of
        Nothing -> action
        Just (trait, owner, function) -> do
            outcome <- tryV action
            case outcome of
                Ok a -> return a
                Error e ->
                    throwV ("impl " ++ trait ++ " for " ++ owner ++ ": " ++ function ++ " does not meet what " ++ trait ++ " declares (its input contract must follow from " ++ trait ++ "'s, and its output contract must give " ++ trait ++ "'s): " ++ e)

-- A body only inspects main to find top-level definition names. The incoming solver is rebuilt
-- before use; every other proof-state field and every program declaration belongs in the key.
functionValidationKey :: PState -> Name -> Bool -> String
functionValidationKey st name top = show
    ( name, top
    , (M.progTypes program, M.progFunctions program, M.progGenerics program, M.progInvariants program, topLevelSources program)
    , (psLocals st, psLocalNames st, psVars st, psView st, psFacts st, psGlobalFacts st, psGlobals st)
    , (psRules st, psFns st, psInBody st, psTerminates st, psReaders st, psBorrows st, psValidated st)
    )
  where
    program = psProgram st

validateFunction :: PState -> Name -> Bool -> V FnInfo
validateFunction st name top
    | Map.size (M.progFunctions (psProgram st)) > 64 = validateFunctionBody st name top
    | otherwise = memoFunction (functionValidationKey st name top) (validateFunctionBody st name top)

validateFunctionBody :: PState -> Name -> Bool -> V FnInfo
validateFunctionBody st name top = do
    fn <- maybe (throwV ("Undefined function: " ++ name)) return (Map.lookup name (M.progFunctions (psProgram st)))
    let spec = M.fnSpec fn
        term = M.specTermination spec
        requires = M.specRequires spec
        ensures = M.specEnsures spec
        params = M.fnParams fn
        names = [n | p <- params, Just d <- [Map.lookup p (M.fnLocals fn)], Just n <- [M.localName d]]
        term' = FnInfo names requires [] term (ATerm (fnIota name)) top (KUser name) (Set.member name (psReaders st)) (M.specMutParams spec)
        -- the function can call itself: it promises what its output contract says of its parameters and result, and the body is
        -- checked against that
        assumed = [p | ProofAssert p <- ensures, all (`elem` ("return" : names ++ ["$old " ++ n | n <- M.specMutParams spec])) (proofVars p)]
        selfInfo = term'{fnExported = assumed, fnTermination = Just (Recursing term)}
        inner0 = withFunctions fn (bodyState st{psFns = if top then Map.insert name selfInfo (psFns st) else psFns st})
        inner = inner0{psTerminates = case term of Just MayDiverge -> False; _ -> True}
    entry <- freshN (length params)
    let started = inner{psLocals = Map.fromList (zip params entry), psVars = Map.union (Map.fromList [("$old " ++ n, i) | (n, i) <- zip names entry, n `elem` M.specMutParams spec]) (psVars inner)}
        env = M.specEnv spec
    -- (a size is not negative)
    let sizeLocals = drop (length params - length (M.fnSizeParams fn)) params
        withSizes' = foldr (\l st' -> maybe st' (\iota -> addFacts st' [FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm iota, CTerm (VInt 0)]]) (Map.lookup l (psLocals st'))) started sizeLocals
    withRequires <- assumeStatements (withEnv env (foldr (withTypeFacts fn) withSizes' params)) requires
    withVariant <- startFunctionVariant (withEnv env withRequires) term
    -- (an extern function, `extern fn`, has no body here: what its contract promises is assumed, and `tersus assumptions` lists it)
    let extern = "extern " `isPrefixOf` name
    returned <- if extern then return [] else walkFunction withVariant fn
    let returnEnv = Map.insert "return" (M.Copy (M.Local 0)) env
    checked <- mapM (\s -> runStatements (withEnv returnEnv s) ensures) returned
    exported <- case checked of
        [] | not extern -> return []
        _ -> do
            -- (the result has no value of its own in the contracts' view: they only say things about it)
            result <- fresh
            -- (an update parameter's entry snapshot is a version of its own at export, equal to the entry version:
            -- otherwise a promise about $old x could not be told from one about x)
            oldIotas <- freshN (length (M.specMutParams spec))
            let oldEntries = [(n, i) | (n, i) <- zip names entry, n `elem` M.specMutParams spec]
                oldBindings = [("$old " ++ n, o) | ((n, _), o) <- zip oldEntries oldIotas]
                known =
                    concat [typeInvariants st (M.localType d) (ATerm iota) | (p, iota) <- zip params entry, Just d <- [Map.lookup p (M.fnLocals fn)]]
                        ++ maybe [] (\t -> typeInvariants st t (ATerm result)) (M.fnReturns fn)
                        ++ [FApp eqProof [ATerm o, ATerm i] | ((_, i), o) <- zip oldEntries oldIotas]
            exported0 <- exportContract started known (zip names entry ++ oldBindings ++ [("return", result)]) requires ensures
            -- (the equality of an entry snapshot with the entry version is how the snapshot was made, not a promise:
            -- exported, it would say that an update changed nothing)
            let isOldEquality (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [ATerm a, ATerm b]) = any (\n -> (a, b) == ("$old " ++ n, n) || (a, b) == (n, "$old " ++ n)) (M.specMutParams spec)
                isOldEquality _ = False
            return (filter (not . isOldEquality) exported0)
    return (term'{fnExported = exported})

-- A function that says what shrinks has it at least 0 for any arguments that meet the input contract, and keeps its value at the start
startFunctionVariant :: PState -> Maybe Termination -> V PState
startFunctionVariant st (Just clause)
    | Just variant <- variantOf (Just clause) = do
        let bounded = boundedBelow entryVariantName clause variant
        variantFailure "Function variant is not bounded below" bounded (checkStatements st bounded)
        assumeStatements st (variantStatements entryVariantName variant)
startFunctionVariant st _ = return st

-- Joins

-- The paths that meet at a block become one state
joinStates :: Ctx -> M.BlockId -> [PState] -> V PState
joinStates _ _ [st] = return st
joinStates cx b states = do
    let live = filter (not . vacuous) states
    case live of
        [] -> return (head states)
        [st] -> return st
        _ -> mergeStates (wantedAt cx b) live

-- (a state whose facts contradict each other cannot run, so it places no requirement on the others)
vacuous :: PState -> Bool
vacuous st = Engine.entails zeroBelowZero (proofContext st)
  where
    zeroBelowZero = FApp (CTerm (builtinFunct (Rel Lt))) [CTerm (VInt 0), CTerm (VInt 0)]

-- The states at the returns of a function, as one
joinAll :: [PState] -> V PState
joinAll = joinAllWanted (const [])

joinAllWanted :: (PState -> [IotaProof]) -> [PState] -> V PState
joinAllWanted wanted states = do
    let live = filter (not . vacuous) states
    case (live, states) of
        ([st], _) -> return st
        ([], st : _) -> return st
        ([], []) -> throwV "No path to join"
        _ -> mergeStates wanted live

-- What the join of paths tries to keep, besides what the paths state: the proofs the program is about to need. The statements
-- that may still run assert some (`affirm`, the invariant of a loop that follows, what a function promises about its result),
-- and a join that keeps a fact like that spares the program from stating it again in each path.
wantedAt :: Ctx -> M.BlockId -> PState -> [IotaProof]
wantedAt cx b joined = concat [[ip | proof <- proofs, Ok ip <- [toIotaProof (withEnv env joined) proof]] | (env, proofs) <- upcoming cx b (psRules joined)]

-- The proofs that the statements of a block and the blocks after it assert, with the names of the program where they stand
upcoming :: Ctx -> M.BlockId -> RuleContext -> [(M.Env, [VariableProof])]
upcoming cx b rules = concatMap fromBlock reachable
  where
    fn = cxFn cx
    blocks = M.fnBlocks fn
    reachable = Set.toList (closure Set.empty [b])
    closure seen [] = seen
    closure seen (x : xs)
        | Set.member x seen = closure seen xs
        | otherwise = closure (Set.insert x seen) (maybe [] (M.successors . M.blockTerminator) (Map.lookup x blocks) ++ xs)
    fromBlock x =
        let stmts = maybe [] M.blockStatements (Map.lookup x blocks)
            ghosts = [(env, assertedProofs rules [vs]) | M.Ghost env (M.GhostValidation vs) <- stmts]
            loop = case Map.lookup x (cxLoops cx) of
                Just info ->
                    let spec = liSpec info
                        name = loopVariantName x
                        decrease = case M.loopTermination spec of
                            Just clause | Just variant <- variantOf (Just clause) -> smallerThan (name ++ " after") name clause variant
                            _ -> []
                     in [(M.loopEnv spec, assertedProofs rules (M.loopInvariant spec ++ decrease))]
                Nothing -> []
            returning = case maybe M.Unreachable M.blockTerminator (Map.lookup x blocks) of
                M.Return -> outputsAbout stmts
                _ -> []
         in ghosts ++ loop ++ returning
    -- what the function promises about the value that a return gives, written for the expression that computes it
    outputsAbout stmts =
        case [rv | M.Assign (M.Local 0) rv <- reverse stmts] of
            rv : _ | Just term <- rvalueTerm rv ->
                let env = Map.union (M.specEnv (M.fnSpec fn)) (Map.fromList [(pseudo l, M.Copy l) | l <- locals rv])
                    ensures = M.specEnsures (M.fnSpec fn)
                 in [(env, map (replaceReturn term) (assertedProofs rules ensures)) | not (null ensures)]
            _ -> []
    locals rv = [l | M.Copy l <- operands rv]
    operands rv = case rv of
        M.Use o -> [o]
        M.BinaryOp _ a c -> [a, c]
        M.ListOp _ os -> os
        M.MakeData _ fs -> map snd fs
        M.ReadField o _ _ -> [o]
        M.IsVariant o _ -> [o]
        M.AsVariant o _ -> [o]
        M.MakeList os -> os
        M.MakeBox o -> [o]
        M.Unbox o -> [o]
        M.Unsize o -> [o]
        M.CopyOf o -> [o]
        M.TakeField{} -> []
    rvalueTerm rv = case rv of
        M.Use o -> Just (atom o)
        _ -> do
            (builtin, os) <- rvalueCall rv
            Just (FApp (CTerm (builtinFunct builtin)) (map atom os))
    atom (M.Copy l) = ATerm (pseudo l)
    atom (M.Const c) = case c of
        M.CFn _ -> CTerm (VInt 0)
        _ -> CTerm (valueOfConstant c)
    replaceReturn value (ATerm "return") = value
    replaceReturn value (FApp funct args) = FApp (replaceReturn value funct) (map (replaceReturn value) args)
    replaceReturn value (Forall index guards body) = Forall index (map (replaceReturn value) guards) (replaceReturn value body)
    replaceReturn _ proof = proof

-- A name for a local, in the environments built for the join (no program can write a name with a %)
pseudo :: M.Local -> Variable
pseudo l = "%" ++ drop 1 (show l)

-- The proofs that stating the statements asserts, with a variable they define replaced by its definition. A rewrite
-- asserts what it needs to hold where it is used.
assertedProofs :: RuleContext -> [ValidationStatement] -> [VariableProof]
assertedProofs rules stmts = [substituteVars definitions proof | proof <- concatMap asserted stmts]
  where
    definitions = Map.fromList [(var, exprToProof expr) | AssignProofVar var expr <- stmts]
    asserted (ProofAssert proof) = [proof]
    asserted (Rewrite rule) = rewriteNeeds rules rule
    asserted _ = []

-- What a rewrite needs to hold where it is applied: the relation a check asks about, and the input contract of a rule
rewriteNeeds :: RuleContext -> RwRule -> [VariableProof]
rewriteNeeds _ (CheckRel proof) = [proof]
rewriteNeeds _ (CheckGtZero proof) = [FApp (CTerm (builtinFunct (Rel Gt))) [proof, CTerm (VInt 0)]]
rewriteNeeds rules (UserRewrite name args) =
    case Map.lookup name rules of
        Just (AxiomRule vars inputs _) -> instantiate vars (assertedProofs rules inputs)
        Just (ProofRule vars inputs _) -> instantiate vars (assertedProofs rules inputs)
        Nothing -> []
  where
    instantiate vars proofs
        | length vars == length args = [substituteVars (Map.fromList (zip vars args)) proof | proof <- proofs]
        | otherwise = []
rewriteNeeds _ _ = []

substituteVars :: Map Variable VariableProof -> VariableProof -> VariableProof
substituteVars replacements = replace
  where
    replace (ATerm var) = fromMaybe (ATerm var) (Map.lookup var replacements)
    replace (FApp funct args) = FApp (replace funct) (map replace args)
    replace (Forall index guards body) = Forall index (map replace guards) (replace body)
    replace proof = proof

-- One state from several paths that meet. A local that has a different value on the paths gets a new one that equals each of
-- them, and a fact is kept if every path establishes it: the facts of the first path are the candidates, and the others must
-- entail them.
mergeStates :: (PState -> [IotaProof]) -> [PState] -> V PState
mergeStates _ [] = throwV "No path to join"
mergeStates _ [st] = return st
mergeStates wantedOf states@(s1 : others) = do
    let common = foldr1 Set.intersection (map (Map.keysSet . psLocals) states)
        iotaOf s l = psLocals s Map.! l
        differing = [l | l <- Set.toList common, any (\s -> iotaOf s l /= iotaOf s1 l) others]
    merged <- freshN (length differing)
    let mergeOf = zip differing merged
        locals' = Map.union (Map.fromList mergeOf) (Map.filterWithKey (\l _ -> Set.member l common) (psLocals s1))
        vars' = Map.filterWithKey (\k v -> all (\s -> Map.lookup k (psVars s) == Just v) others) (psVars s1)
        common' = foldr1 Set.intersection (map (Set.fromList . psFacts) states)
        s0Facts = filter (`Set.member` common') (psFacts s1)
        own s = filter (`Set.notMember` common') (psFacts s)
        toMerged s proof = foldl (\p (l, m) -> fromMaybe p (substituteProofTerm (ATerm (iotaOf s l)) (ATerm m) p)) proof mergeOf
        globalIotas = Set.fromList (concatMap proofIotas (psGlobalFacts s1))
        visible = Set.union globalIotas (Set.fromList (concatMap proofIotas s0Facts ++ Map.elems locals' ++ Map.elems vars'))
        isVisible p = all (`Set.member` visible) (proofIotas p)
        base =
            (refreshCache s1)
                { psLocals = locals'
                , psVars = vars'
                , psBorrows = Map.filterWithKey (\k v -> all (\s -> Map.lookup k (psBorrows s) == Just v) states) (psBorrows s1)
                , psFacts = s0Facts
                , psRules = Map.unions (map psRules states)
                , psFns = Map.unions (map psFns states)
                , psValidated = Set.unions (map psValidated states)
                , psGlobals = Map.unions (map psGlobals states)
                , psGlobalFacts = nubOrd (concatMap psGlobalFacts states)
                }
        based = base{psCache = Nothing}
        equalities s = [FApp eqProof [ATerm m, ATerm (iotaOf s l)] | (l, m) <- mergeOf]
        contexts = [(s, proofContextWith s (equalities s)) | s <- states]
        candidates = nubOrd [c | p <- own s1, let c = toMerged s1 p, isVisible c, c `notElem` s0Facts]
        entailedByOthers cs = foldl (\flags (_, ctx) -> zipWith (&&) flags (Engine.entailsAll cs ctx)) (map (const True) cs) (drop 1 contexts)
        keptFromFirst = [c | (c, True) <- zip candidates (entailedByOthers candidates)]
        -- (a fact about the value that a local had, for the new value of the local: also one local at a time, since locals can
        -- hold the same value, and then the value is replaced by the new value of only one of them)
        toMergedOne s (l, m) = substituteProofTerm (ATerm (iotaOf s l)) (ATerm m)
        carried = [p' | s <- states, p <- s0Facts, let p' = toMerged s p, p' /= p] ++ [p' | s <- states, lm <- mergeOf, p <- s0Facts, Just p' <- [toMergedOne s lm p]]
        fromOthers = [toMerged s p | s <- others, p <- own s] ++ [p' | s <- others, lm <- mergeOf, p <- own s, Just p' <- [toMergedOne s lm p]]
        extras =
            take maxJoinCandidates . nubOrd $
                [ c
                | c <- wantedOf (refreshCache based{psFacts = s0Facts}) ++ carried ++ fromOthers
                , c `notElem` s0Facts
                , c `notElem` candidates
                , isVisible c
                ]
        entailedDirect cs = foldl (\flags (_, ctx) -> zipWith (&&) flags (Engine.entailsDirect cs ctx)) (map (const True) cs) contexts
        keptExtras = [c | (c, True) <- zip extras (entailedDirect extras)]
    return (addFacts (refreshCache based{psFacts = s0Facts}) (keptFromFirst ++ keptExtras))

-- Loops

-- Validates a loop by its invariant, without running it.
--
-- 1. The loop has to say how it ends, see loopTermination.
-- 2. The invariant must hold before the first iteration.
-- 3. Every local the body assigns is given a fresh value with no facts, so nothing about its earlier values is assumed.
--    Facts about other values stay true because values are immutable.
-- 4. Assuming the invariant and the condition, the body must re-establish the invariant, and the variant (if the loop has
--    one) must be at least 0 at the start and smaller at the end.
-- 5. After the loop, the invariant holds and the condition does not.
enterLoop :: Ctx -> M.BlockId -> LoopInfo -> [PState] -> V Walked
enterLoop cx header info incoming = do
    entry <- joinStates cx header incoming
    let spec = liSpec info
        env = M.loopEnv spec
        invariant = M.loopInvariant spec
    liftR (loopTermination entry (M.loopTermination spec))
    prefixError "Loop invariant does not hold on entry: " (rangeHint (checkStatements (withEnv env entry) invariant))
    let loopLocals = [l | l <- Set.toList (assignedIn cx (liRegion info)), Map.member l (psLocals entry)]
    freshIotas <- freshN (length loopLocals)
    let havocked = foldr (withTypeFacts (cxFn cx)) entry{psLocals = Map.union (Map.fromList (zip loopLocals freshIotas)) (psLocals entry)} loopLocals
    let variantName = loopVariantName header
        -- (the candidates are written for the locals the loop assigns, by names that no program can write)
        env' = Map.union env (Map.fromList [(pseudo l, M.Copy l) | l <- loopLocals])
        run = LoopRun header (M.loopBody spec) env' (do clause <- M.loopTermination spec; variant <- variantOf (Just clause); Just (variantName, clause, variant))
        attempt extra = loopFrom cx info run havocked (invariant ++ extra)
    inferred <- inferInvariants cx info run entry havocked loopLocals
    result <- tryV (attempt inferred)
    case result of
        Ok walked -> return walked{wdBacks = []}
        Error e
            | namesInferred e inferred -> (\walked -> walked{wdBacks = []}) <$> attempt []
            | otherwise -> throwV e

-- The name of the proof variable that holds the value of the variant of a loop at the start of an iteration
loopVariantName :: M.BlockId -> Variable
loopVariantName header = "variant " ++ show header

-- A for loop whose range is not known to end at or after its start does not hold its bounds on entry
rangeHint :: V a -> V a
rangeHint action = do
    result <- tryV action
    case result of
        Ok a -> return a
        Error e
            | "(end of for" `isInfixOf` e -> throwV (e ++ " (the range has to be known to end at or after its start, as 0..n does with n >= 0)")
            | otherwise -> throwV e

-- Whether an error says that one of the invariants was not preserved
namesInferred :: String -> [ValidationStatement] -> Bool
namesInferred e inferred = or [e == "Loop invariant is not preserved: Could not prove: " ++ renderVarProof p | ProofAssert p <- inferred]

-- A loop has to say how it ends. One that may not end is code that may not terminate, which a function
-- has to be declared ~ to contain.
loopTermination :: PState -> Maybe Termination -> Result () String
loopTermination _ Nothing = Error "Loop must say how it ends: add `shrinks <expression>` before its body, or `~`"
loopTermination st (Just MayDiverge) = noteDivergence st "a loop is declared ~"
loopTermination _ _ = Ok ()

-- The locals that a region assigns
assignedIn :: Ctx -> Set M.BlockId -> Set M.Local
assignedIn cx region = Set.fromList (concat [assigned b | b <- Set.toList region])
  where
    assigned b = case Map.lookup b (M.fnBlocks (cxFn cx)) of
        Nothing -> []
        Just (M.BasicBlock stmts term) -> [d | M.Assign d _ <- stmts] ++ [root | M.AssignRef root _ _ <- stmts] ++ (case term of M.Call _ _ d _ -> [d]; _ -> []) ++ mutRoots stmts term
    -- (what a call through an update parameter changes is assigned by the call, so a loop may not keep its old version:
    -- an argument made by &mut place, or a local of an update-reference type, stands for its root)
    mutRoots _ (M.Call _ args _ _) = concatMap rootOf args
      where
        borrowOf = Map.fromList [(d, root) | blk <- Map.elems (M.fnBlocks (cxFn cx)), M.Assign d (M.Borrow root _ True) <- M.blockStatements blk]
        rootOf (M.Copy l) = mutRoot l
        rootOf (M.Move l) = mutRoot l
        rootOf _ = []
        mutRoot l = case (Map.lookup l borrowOf, M.localType <$> Map.lookup l (M.fnLocals (cxFn cx))) of
            (Just root, _) -> [root]
            (_, Just (TMutRef _)) -> [l]
            _ -> []
    mutRoots _ _ = []

-- The rest of the validation of a loop, from the state where the variables its body assigns are unknown: the invariant is
-- assumed, the body is walked, and each way back to the start has to establish the invariant again
loopFrom :: Ctx -> LoopInfo -> LoopRun -> PState -> [ValidationStatement] -> V Walked
loopFrom cx info run havocked invariant = do
    assumed <- assumeStatements (withEnv (lrEnv run) havocked) invariant
    walked <- walk cx (Just run) (liRegion info) (lrHeader run) assumed
    forM_ (wdBacks walked) $ \back -> do
        let backState = withEnv (lrEnv run) back
        prefixError "Loop invariant is not preserved: " (checkStatements backState invariant)
        case lrVariant run of
            Just (name, clause, variant) -> do
                let decrease = smallerThan (name ++ " after") name clause variant
                variantFailure "Loop variant does not shrink" decrease (checkStatements backState decrease)
            Nothing -> return ()
    return walked

-- The state at the start of an iteration, where the invariant and the condition hold. For a loop with a variant, that must
-- be at least 0, and the state keeps its value.
startIteration :: LoopRun -> PState -> V PState
startIteration run st =
    case lrVariant run of
        Just (name, clause, variant) -> do
            let viewed = withEnv (lrEnv run) st
                bounded = boundedBelow name clause variant
            variantFailure "Loop variant is not bounded below" bounded (checkStatements viewed bounded)
            assumeStatements viewed (variantStatements name variant)
        Nothing -> return st

-- Invariants that a loop gets without the program writing them. The variables the body assigns start with
-- candidates, from what the facts say when the loop is entered:
--   * a variable that is a number there is at least and at most that number, the size of a list likewise, and
--     two of these differ by what they differed by;
--   * a variable (or the size of a list) that is not known to be a number is compared with the other variables
--     the loop does not assign, and the comparison is a candidate if the facts already entail it (i <= n when
--     i starts at 0 and n is size(a), size(out) = size(a) when out starts as a copy of a).
-- A candidate is kept only if the body establishes it again, assuming the candidates that are left, which is
-- repeated until none is dropped, so what is kept is an invariant: it holds on entry, and is preserved. A body
-- that does not validate infers nothing.
inferInvariants :: Ctx -> LoopInfo -> LoopRun -> PState -> PState -> [M.Local] -> V [ValidationStatement]
inferInvariants cx info run entry havocked loopLocals
    | null candidates = return []
    | otherwise = houdini maxInferenceRounds (map ProofAssert candidates)
  where
    env = lrEnv run
    invariant = M.loopInvariant (liSpec info)
    entryView = withEnv env entry
    context = proofContext entry
    loopVars = map pseudo loopLocals
    sizeOf term = FApp (CTerm (builtinFunct Size)) [term]
    relation rel lhs rhs = FApp (CTerm (builtinFunct (Rel rel))) [lhs, rhs]
    termOf name = fromMaybe (ATerm (Iota name)) (lookupName entryView name)
    -- The terms of a variable that candidates are about, with the number they equal on entry if there is one
    -- (a variable that is not a known number or list can still have a size that is known: push(push([], a), b) has size 2)
    termsOf var (Just (VInt n)) _ = [(ATerm var, Just n)]
    termsOf var (Just (VList items)) _ = [(sizeOf (ATerm var), Just (fromIntegral (length items)))]
    termsOf _ (Just _) _ = []
    termsOf var Nothing size = [(ATerm var, Nothing), (sizeOf (ATerm var), size)]
    -- the first elements of a list, which a loop that only pushes (or sets elsewhere) leaves as they were
    elementsOf var (Just (VList items)) _ = [(element var k, Just n) | (k, VInt n) <- take maxInferenceElements (zip [0 ..] items)]
    elementsOf var Nothing size = [(element var k, Nothing) | Just n <- [size], k <- [0 .. min n (fromIntegral maxInferenceElements) - 1]]
    elementsOf _ _ _ = []
    element var k = FApp (CTerm (builtinFunct Get)) [ATerm var, CTerm (VInt k)]
    loopValues = Engine.constantValues [termOf var | var <- loopVars] context
    loopSizes = [case value of Just (VInt n) -> Just n; _ -> Nothing | value <- Engine.constantValues [sizeOf (termOf var) | var <- loopVars] context]
    loopEntries = zip3 loopVars loopValues loopSizes
    -- (the numbers and sizes come first, so that the elements of the lists never push a counter out)
    loopTerms = take maxInferenceTerms (concat [termsOf var value size | (var, value, size) <- loopEntries] ++ concat [elementsOf var value size | (var, value, size) <- loopEntries])
    -- Variables the loop does not assign, that are not known to be a number or a list, and that the program wrote
    anchorVars =
        take maxInferenceAnchors . nubOrd . sort $
            [name | (name, M.Copy l) <- Map.toList env, l `notElem` loopLocals, Map.member l (psLocals entry), ' ' `notElem` name, take 1 name /= "$", take 1 name /= "%"]
                ++ [name | name <- Map.keys (psVars entry), ' ' `notElem` name, take 1 name /= "$"]
    anchorValues = Engine.constantValues [termOf var | var <- anchorVars] context
    anchors = concat [termsOf var Nothing Nothing | (var, Nothing) <- zip anchorVars anchorValues]
    isElement (FApp (CTerm funct) [ATerm _, CTerm (VInt _)]) = funct == builtinFunct Get
    isElement _ = False
    known = [(term, k) | (term, Just k) <- loopTerms, not (isElement term)]
    -- (an element that starts as a number is only bounded, and after the rest, since there can be many)
    elementBounds = concat [[relation GtEq term (CTerm (VInt k)), relation LtEq term (CTerm (VInt k))] | (term, Just k) <- loopTerms, isElement term]
    constantCandidates =
        concat [[relation GtEq term (CTerm (VInt k)), relation LtEq term (CTerm (VInt k))] | (term, k) <- known]
            ++ [ relation Eq t1 (if k1 == k2 then t2 else FApp (CTerm (builtinFunct Plus)) [t2, CTerm (VInt (k1 - k2))])
               | (i, (t1, k1)) <- zip [0 :: Int ..] known
               , (j, (t2, k2)) <- zip [0 ..] known
               , i < j
               ]
    comparisons = [relation rel term anchor | (term, _) <- loopTerms, (anchor, _) <- anchors, rel <- [Eq, LtEq, GtEq]]
    -- a sum of two terms that is a variable the loop does not assign, plus the number one of them starts at: s + i = n
    sums =
        [ relation Eq (FApp (CTerm (builtinFunct Plus)) [t1, t2]) (if offset == 0 then anchor else FApp (CTerm (builtinFunct Plus)) [anchor, CTerm (VInt offset)])
        | (i, (t1, k1)) <- zip [0 :: Int ..] loopTerms
        , (j, (t2, k2)) <- zip [0 ..] loopTerms
        , i < j
        , isNothing k1 || isNothing k2
        , let offset = fromMaybe 0 k1 + fromMaybe 0 k2
        , (anchor, _) <- anchors
        ]
    converted = [(c, goal) | c <- comparisons ++ sums, Ok goal <- [toIotaProof entryView c]]
    entailedAt goals = [c | ((c, _), True) <- zip goals (Engine.entailsDirect (map snd goals) context)]
    entailedBasic = entailedAt converted
    -- a term that starts at a variable the loop does not assign, next to a term that starts at a number: i = lo, size(out) = 0
    -- gives i = size(out) + lo, which holds as long as both grow by the same amount (slice of a buffer from lo)
    differences =
        [ relation Eq t (FApp (CTerm (builtinFunct Plus)) [t2, if k == 0 then anchor else FApp (CTerm (builtinFunct Plus)) [anchor, CTerm (VInt (negate k))]])
        | FApp rel [t, anchor] <- entailedBasic
        , rel == CTerm (builtinFunct (Rel Eq))
        , t `elem` unknownTerms
        , (t2, k) <- known
        , t2 /= t
        ]
    unknownTerms = [term | (term, Nothing) <- loopTerms]
    convertedDifferences = [(c, goal) | c <- differences, Ok goal <- [toIotaProof entryView c]]
    entailed = entailedBasic ++ entailedAt convertedDifferences
    -- sums of terms that start at numbers, last so that they never push out the distances and comparisons
    knownSums =
        [ relation Eq (FApp (CTerm (builtinFunct Plus)) [t1, t2]) (CTerm (VInt (k1 + k2)))
        | (i, (t1, k1)) <- zip [0 :: Int ..] known
        , (j, (t2, k2)) <- zip [0 ..] known
        , i < j
        ]
    candidates = take maxInferenceCandidates (constantCandidates ++ entailed ++ knownSums ++ elementBounds)
    houdini rounds survivors
        | null survivors || rounds <= 0 = return []
        | otherwise = do
            ends <- iterationEnds survivors
            case ends of
                Nothing -> return []
                Just backs -> do
                    kept <- filterM (\c -> allM (\back -> succeeds (checkStatements (withEnv env back) [c])) backs) survivors
                    if length kept == length survivors then return survivors else houdini (rounds - 1) kept
    -- the states at the ends of an iteration, when the body validates with the candidates assumed
    iterationEnds survivors = do
        result <- tryV $ do
            assumed <- assumeStatements (withEnv env havocked) (invariant ++ survivors)
            walked <- walk cx (Just run{lrVariant = Nothing}) (liRegion info) (lrHeader run) assumed
            return (wdBacks walked)
        return (case result of Ok backs -> Just backs; Error _ -> Nothing)

succeeds :: V a -> V Bool
succeeds action = do
    result <- tryV action
    return (case result of Ok _ -> True; Error _ -> False)

allM :: (a -> V Bool) -> [a] -> V Bool
allM _ [] = return True
allM f (x : xs) = f x >>= \ok -> if ok then allM f xs else return False

maxInferenceRounds :: Int
maxInferenceRounds = 4

maxInferenceTerms :: Int
maxInferenceTerms = 8

-- The first elements of a list that are looked at
maxInferenceElements :: Int
maxInferenceElements = 3

maxInferenceAnchors :: Int
maxInferenceAnchors = 12

maxInferenceCandidates :: Int
maxInferenceCandidates = 32
