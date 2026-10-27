-- A conservative bridge from a supported MIR subset to the Tersus checker.
-- Unsupported instructions or proof forms are reported as Nothing, never
-- accepted. This is not used as the production validator.
module SelfHostedMir (validateMirSubset) where

import Control.Monad (foldM)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Mir as M
import MirEval (MirValue (..), runNamedFunction)
import MirVerify (verifyProgram)
import TersusTypes
import Utils (Result (..), bindResult, inIntRange)

data Build = Build { nextTerm :: Integer, literalIds :: [(M.Constant, Integer)], literalTerms :: [MirValue], literalApps :: [MirValue], namedFunctions :: [(String, Integer)] }

emptyBuild :: Build
emptyBuild = Build 0 [] [] [] []

record :: String -> [(String, MirValue)] -> MirValue
record = MData

fresh :: Build -> (Integer, Build)
fresh b = (nextTerm b, b{nextTerm = nextTerm b + 1})

namedFunction :: String -> Build -> (Integer, Build)
namedFunction name b = case lookup name (namedFunctions b) of
    Just i -> (i, b)
    Nothing -> let (i, b') = fresh b in (i, b'{namedFunctions = (name, i) : namedFunctions b'})

literal :: M.Constant -> Build -> Maybe (Integer, Build)
literal c b = case lookup c (literalIds b) of
    Just i -> Just (i, b)
    Nothing | Just (constructor, values) <- sequenceLiteral c -> do
        (ids, b1) <- foldM addLiteral ([], b) values
        (len, b2) <- literal (M.CInt (toInteger (length values))) b1
        let (i, b3) = fresh b2
            listApp = record "ApplicationTerm" [("id", MInt i), ("function", MInt constructor), ("arguments", MList (map MInt ids))]
            sizeApp = record "ApplicationTerm" [("id", MInt len), ("function", MInt (-13)), ("arguments", MList [MInt i])]
            b4 = b3{literalIds = (c, i) : literalIds b3, literalApps = listApp : sizeApp : literalApps b3}
        b5 <- foldM (addElement i) b4 (zip [0..] ids)
        pure (i, b5)
    Nothing -> do
        (kind, value) <- case c of
            M.CInt n | inIntRange n -> Just (0, n)
            M.CBool x -> Just (1, if x then 1 else 0)
            _ -> Nothing
        let (i, b') = fresh b
            entry = record "ConstantTerm" [("id", MInt i), ("kind", MInt kind), ("value", MInt value)]
        pure (i, b'{literalIds = (c, i) : literalIds b', literalTerms = entry : literalTerms b'})
  where
    sequenceLiteral (M.CList values) = Just (-12, values)
    sequenceLiteral (M.CArray values) = Just (-15, values)
    sequenceLiteral _ = Nothing
    addLiteral (ids, current) value = do
        (i, next) <- literal value current
        pure (ids ++ [i], next)
    addElement listId current (index, valueId) = do
        (indexId, next) <- literal (M.CInt index) current
        let app = record "ApplicationTerm" [("id", MInt valueId), ("function", MInt (-14)), ("arguments", MList [MInt listId, MInt indexId])]
        pure next{literalApps = app : literalApps next}

operand :: M.Operand -> Build -> Maybe (MirValue, Build)
operand (M.Copy (M.Local n)) b = Just (record "ValueRef::Local" [("local", MInt (toInteger n))], b)
operand (M.Const c) b = do
    (i, b') <- literal c b
    pure (record "ValueRef::Term" [("term", MInt i)], b')
operand _ _ = Nothing

step :: String -> [(String, MirValue)] -> MirValue
step name = record ("ExecutionStep::" ++ name)

-- Evaluate proof expressions into temporary symbolic terms. The arithmetic
-- operations are pure; division and remainder require a proved nonzero
-- divisor before the application is introduced.
proofOperand :: M.Env -> VariableProof -> Build -> Maybe ([MirValue], MirValue, Build)
proofOperand env (ATerm name) b = do
    o <- Map.lookup name env
    (v, b') <- operand o b
    pure ([], v, b')
proofOperand _ (CTerm (VInt n)) b = do
    (v, b') <- operand (M.Const (M.CInt n)) b
    pure ([], v, b')
proofOperand _ (CTerm (VBool x)) b = do
    (v, b') <- operand (M.Const (M.CBool x)) b
    pure ([], v, b')
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Size) _)) [arg]) b0 = do
    (prefix, value, b1) <- proofOperand env arg b0
    let (i, b2) = fresh b1
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (-13)), ("arguments", MList [value])]
    pure (prefix ++ [apply], ref, b2)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Field _ field)) _)) [arg]) b0 = do
    (prefix, value, b1) <- proofOperand env arg b0
    let (function, b2) = namedFunction ("field:" ++ field) b1
        (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [value])]
    pure (prefix ++ [apply], ref, b3)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [list, index]) b0 = do
    (listSteps, listRef, b1) <- proofOperand env list b0
    (indexSteps, indexRef, b2) <- proofOperand env index b1
    let (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
    (steps, b4) <- getSteps local listRef indexRef b3
    pure (listSteps ++ indexSteps ++ steps, ref, b4)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Push) _)) [list, value]) b0 = do
    (listSteps, listRef, b1) <- proofOperand env list b0
    (valueSteps, valueRef, b2) <- proofOperand env value b1
    let (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
    (steps, b4) <- pushSteps local listRef valueRef b3
    pure (listSteps ++ valueSteps ++ steps, ref, b4)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Set) _)) [list, index, value]) b0 = do
    (listSteps, listRef, b1) <- proofOperand env list b0
    (indexSteps, indexRef, b2) <- proofOperand env index b1
    (valueSteps, valueRef, b3) <- proofOperand env value b2
    let (i, b4) = fresh b3
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
    (steps, b5) <- setSteps local listRef indexRef valueRef b4
    pure (listSteps ++ indexSteps ++ valueSteps ++ steps, ref, b5)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct f) _)) [list]) b0
    | f == First || f == Last = do
        (prefix, listRef, b1) <- proofOperand env list b0
        let (i, b2) = fresh b1
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
        (steps, b4) <- if f == First then do
            (zero, b3) <- operand (M.Const (M.CInt 0)) b2
            getSteps local listRef zero b3
          else lastSteps local listRef b2
        pure (prefix ++ steps, ref, b4)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct f) _)) [a, b]) b0 = do
    op <- case f of
        Plus -> Just M.Add
        Minus -> Just M.Sub
        Times -> Just M.Mul
        Div -> Just M.Div
        Mod -> Just M.Mod
        _ -> Nothing
    (leftSteps, x, b1) <- proofOperand env a b0
    (rightSteps, y, b2) <- proofOperand env b b1
    (requires, b3) <- case op of
        M.Div -> nonzero y b2
        M.Mod -> nonzero y b2
        _ -> Just ([], b2)
    let (i, b4) = fresh b3
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (functionId op)), ("arguments", MList [x, y])]
    pure (leftSteps ++ rightSteps ++ requires ++ [apply], ref, b4)
  where
    nonzero y b' = do
        (zero, b'') <- operand (M.Const (M.CInt 0)) b'
        pure ([check 1 y zero], b'')
proofOperand _ _ _ = Nothing

check :: Integer -> MirValue -> MirValue -> MirValue
check relation a b = step "Check" [("relation", MInt relation), ("left", a), ("right", b)]

-- The indexing preconditions must be proved before the pure application is
-- introduced, including when get occurs inside a proof expression.
getSteps :: Integer -> MirValue -> MirValue -> Build -> Maybe ([MirValue], Build)
getSteps dest listRef indexRef b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    let (i, b2) = fresh b1
        lengthLocal = negate i - 1
        lengthRef = record "ValueRef::Local" [("local", MInt lengthLocal)]
        size = step "ApplyFresh" [("local", MInt lengthLocal), ("function", MInt (-13)), ("arguments", MList [listRef])]
        get = step "ApplyFresh" [("local", MInt dest), ("function", MInt (-14)), ("arguments", MList [listRef, indexRef])]
    pure ([size, check 3 zero indexRef, check 2 indexRef lengthRef, get], b2)

pushSteps :: Integer -> MirValue -> MirValue -> Build -> Maybe ([MirValue], Build)
pushSteps dest listRef valueRef b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    pure ([step "Push" [("local", MInt dest), ("list", listRef), ("value", valueRef), ("zero", zero)]], b1)

lastSteps :: Integer -> MirValue -> Build -> Maybe ([MirValue], Build)
lastSteps dest listRef b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    pure ([step "Last" [("local", MInt dest), ("list", listRef), ("zero", zero)]], b1)

setSteps :: Integer -> MirValue -> MirValue -> MirValue -> Build -> Maybe ([MirValue], Build)
setSteps dest listRef indexRef valueRef b0 = do
    let (i, b1) = fresh b0
    (bounds, b2) <- getSteps (negate i - 1) listRef indexRef b1
    let update = step "Set" [("local", MInt dest), ("list", listRef), ("index", indexRef), ("value", valueRef)]
    pure (bounds ++ [update], b2)

proofCheck :: M.Env -> VariableProof -> Build -> Maybe ([MirValue], MirValue, Build)
proofCheck env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel r)) _)) [a, b]) b0 = do
    (leftSteps, x, b1) <- proofOperand env a b0
    (rightSteps, y, b2) <- proofOperand env b b1
    let (kind, left, right) = case r of
            Eq -> (0, x, y)
            NotEq -> (1, x, y)
            Lt -> (2, x, y)
            LtEq -> (3, x, y)
            Gt -> (2, y, x)
            GtEq -> (3, y, x)
    pure (leftSteps ++ rightSteps, check kind left right, b2)
proofCheck _ _ _ = Nothing

-- Stable negative identifiers name pure builtin operations; all literals and
-- fresh results use non-negative identifiers from the same allocation stream.
functionId :: M.BinOp -> Integer
functionId op = case op of
    M.Add -> -1
    M.Sub -> -2
    M.Mul -> -3
    M.Div -> -4
    M.Mod -> -5
    M.Compare Eq -> -6
    M.Compare NotEq -> -7
    M.Compare Lt -> -8
    M.Compare LtEq -> -9
    M.Compare Gt -> -10
    M.Compare GtEq -> -11

statement :: M.Statement -> Build -> Maybe ([MirValue], Build)
statement (M.Assign (M.Local dest) (M.Use source)) b = do
    (v, b') <- operand source b
    pure ([step "Assign" [("local", MInt (toInteger dest)), ("value", v)]], b')
-- Boxes and unsizing preserve the proof value, as in the reference MIR
-- validator. Ownership and representation are handled by later passes.
statement (M.Assign dest (M.MakeBox source)) b = statement (M.Assign dest (M.Use source)) b
statement (M.Assign dest (M.Unbox source)) b = statement (M.Assign dest (M.Use source)) b
statement (M.Assign dest (M.Unsize source)) b = statement (M.Assign dest (M.Use source)) b
statement (M.Assign (M.Local dest) (M.MakeData name fields)) b0 = do
    (snapshots, b1) <- foldM snapshot ([], b0) fields
    let (constructor, b2) = namedFunction ("ctor:" ++ name) b1
        destination = record "ValueRef::Local" [("local", MInt (toInteger dest))]
        create = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt constructor), ("arguments", MList [ref | (_, ref, _) <- snapshots])]
    (projections, b3) <- foldM (project destination) ([], b2) snapshots
    pure ([saved | (_, _, saved) <- snapshots] ++ [create] ++ projections, b3)
  where
    snapshot (acc, b) (field, source) = do
        (value, b1) <- operand source b
        let (i, b2) = fresh b1
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            save = step "Assign" [("local", MInt local), ("value", value)]
        pure (acc ++ [(field, ref, save)], b2)
    project destination (acc, b) (field, original, _) = do
        let (function, b1) = namedFunction ("field:" ++ field) b
            (i, b2) = fresh b1
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            readField = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [destination])]
            known = step "Assume" [("relation", MInt 0), ("left", ref), ("right", original)]
        pure (acc ++ [readField, known], b2)
statement (M.Assign (M.Local dest) (M.ReadField source _ field)) b0 = do
    (value, b1) <- operand source b0
    let (function, b2) = namedFunction ("field:" ++ field) b1
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList [value])]], b2)
statement (M.Assign (M.Local dest) (M.ListOp M.Length [source])) b = do
    (value, b') <- operand source b
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (-13)), ("arguments", MList [value])]], b')
statement (M.Assign (M.Local dest) (M.ListOp M.Get [source, index])) b0 = do
    (listRef, b1) <- operand source b0
    (indexRef, b2) <- operand index b1
    getSteps (toInteger dest) listRef indexRef b2
statement (M.Assign (M.Local dest) (M.ListOp M.Push [source, value])) b0 = do
    (listRef, b1) <- operand source b0
    (valueRef, b2) <- operand value b1
    pushSteps (toInteger dest) listRef valueRef b2
statement (M.Assign (M.Local dest) (M.ListOp M.Set [source, index, value])) b0 = do
    (listRef, b1) <- operand source b0
    (indexRef, b2) <- operand index b1
    (valueRef, b3) <- operand value b2
    setSteps (toInteger dest) listRef indexRef valueRef b3
statement (M.Assign (M.Local dest) (M.ListOp operation [source])) b0
    | operation == M.First || operation == M.Last = do
        (listRef, b1) <- operand source b0
        if operation == M.First then do
            (zero, b2) <- operand (M.Const (M.CInt 0)) b1
            getSteps (toInteger dest) listRef zero b2
          else lastSteps (toInteger dest) listRef b1
statement (M.Assign (M.Local dest) (M.BinaryOp op a b)) b0 = do
    (x, b1) <- operand a b0
    (y, b2) <- operand b b1
    (checks, b3) <- case op of
        M.Div -> nonzero y b2
        M.Mod -> nonzero y b2
        _ -> Just ([], b2)
    let apply = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (functionId op)), ("arguments", MList [x, y])]
    pure (checks ++ [apply], b3)
  where
    nonzero y b' = do
        (zero, b'') <- operand (M.Const (M.CInt 0)) b'
        pure ([check 1 y zero], b'')
statement (M.Ghost env (M.GhostValidation (ProofAssert proof))) b = do
    (prefix, s, b') <- proofCheck env proof b
    pure (prefix ++ [s], b')
statement _ _ = Nothing

block :: M.Function -> (M.BlockId, M.BasicBlock) -> Build -> Maybe (MirValue, Build)
block fn (blockId@(M.BlockId n), M.BasicBlock stmts end) b0 = do
    (steps, b1, conditions) <- foldM add ([], b0, Map.empty) stmts
    (extra, ending, b2) <- case (Map.lookup blockId (M.specLoops (M.fnSpec fn)), end) of
        (Just spec, M.SwitchBool (M.Copy local) yes no) -> do
            (loopEnd, b') <- encodeLoop spec local yes no conditions b1
            pure ([], loopEnd, b')
        (Just _, _) -> Nothing
        (Nothing, M.Return) -> Just ([], record "ExecutionEnd::Done" [], b1)
        (Nothing, M.Goto target) -> Just ([], jump target, b1)
        (Nothing, M.SwitchBool (M.Const (M.CBool choice)) yes no) -> Just ([], jump (if choice then yes else no), b1)
        (Nothing, M.SwitchBool (M.Copy local) yes no) -> do
            let ref = localRef (localNumber local)
                required = step "RequireDefined" [("value", ref)]
            (trueRef, b2) <- operand (M.Const (M.CBool True)) b1
            (falseRef, b3) <- operand (M.Const (M.CBool False)) b2
            let M.BlockId yesId = yes
                M.BlockId noId = no
                ending = record "ExecutionEnd::BooleanBranch"
                    [("yes", MInt (toInteger yesId)), ("no", MInt (toInteger noId)), ("value", ref), ("trueValue", trueRef), ("falseValue", falseRef)]
            Just ([required], ending, b3)
        _ -> Nothing
    pure (record "ExecutionBlock" [("id", MInt (toInteger n)), ("steps", MList (steps ++ extra)), ("end", ending)], b2)
  where
    -- The initial induction implementation only accepts a canonical loop:
    -- one comparison in the header and a single body block returning to it.
    -- This makes every entry, invariant check and back edge explicit.
    encodeLoop spec local yes no conditions b = do
        case stmts of
            [M.Assign dest (M.BinaryOp (M.Compare _) _ _)] | dest == local -> Just ()
            _ -> Nothing
        if yes == M.loopBody spec && yes /= blockId && no /= blockId && no /= yes then Just () else Nothing
        if Map.member yes (M.specLoops (M.fnSpec fn)) then Nothing else Just ()
        bodyBlock <- Map.lookup yes (M.fnBlocks fn)
        case M.blockTerminator bodyBlock of M.Goto target | target == blockId -> Just (); _ -> Nothing
        let incoming = [from | (from, candidate) <- Map.toList (M.fnBlocks fn), yes `elem` M.successors (M.blockTerminator candidate)]
        if incoming == [blockId] then Just () else Nothing
        (r, a, c) <- Map.lookup local conditions
        (mode, variant, variantLocal, upper) <- case M.loopTermination spec of
            Just (Counting (Var name)) -> case Map.lookup name (M.loopEnv spec) of
                Just op@(M.Copy v) -> Just (0, op, v, M.Const (M.CInt 0))
                _ -> Nothing
            Just (Counting (F (Val (VFunct _ _ _ (BuiltinFunct Minus) _)) [upperExpr, Var name])) -> do
                counter <- Map.lookup name (M.loopEnv spec)
                upperOperand <- expressionOperand (M.loopEnv spec) upperExpr
                case counter of M.Copy v -> Just (1, counter, v, upperOperand); _ -> Nothing
            _ -> Nothing
        decl <- Map.lookup variantLocal (M.fnLocals fn)
        if M.localType decl == TInt then Just () else Nothing
        let assigned = nub (local : [v | M.Assign v _ <- M.blockStatements bodyBlock])
        case upper of
            M.Copy v -> do
                upperDecl <- Map.lookup v (M.fnLocals fn)
                if M.localType upperDecl == TInt && v `notElem` assigned then Just () else Nothing
            M.Const (M.CInt _) -> Just ()
            _ -> Nothing
        (variantRef, b1) <- operand variant b
        (upperRef, b2) <- operand upper b1
        (zeroRef, b3) <- operand (M.Const (M.CInt 0)) b2
        (checks, assumptions, b4) <- foldM (invariant (M.loopEnv spec)) ([], [], b3) (M.loopInvariant spec)
        (bodyEncoded, b5) <- block fn (yes, bodyBlock) b4
        bodySteps <- case bodyEncoded of
            MData "ExecutionBlock" fields -> case lookup "steps" fields of
                Just (MList xs) -> Just xs
                _ -> Nothing
            _ -> Nothing
        let (kind, left, right) = normal r a c
            M.BlockId exitId = no
        pure (record "ExecutionEnd::Loop" [("exit", MInt (toInteger exitId)), ("body", MList bodySteps),
             ("checks", MList checks), ("assumptions", MList assumptions), ("havoc", MList (map (MInt . localNumber) assigned)),
             ("relation", MInt kind), ("left", left), ("right", right), ("variant", variantRef), ("variantMode", MInt mode),
             ("variantOther", upperRef), ("zero", zeroRef)], b5)
    expressionOperand env expr = case expr of
        Var name -> Map.lookup name env
        Val (VInt value) -> Just (M.Const (M.CInt value))
        _ -> Nothing
    invariant env (checks, assumptions, b) (ProofAssert p) = do
        (prefix, checkStep, b') <- proofCheck env p b
        assumption <- asAssumption checkStep
        pure (checks ++ prefix ++ [checkStep], assumptions ++ prefix ++ [assumption], b')
    invariant _ _ _ = Nothing
    asAssumption (MData "ExecutionStep::Check" fields) = Just (MData "ExecutionStep::Assume" fields)
    asAssumption _ = Nothing
    add (steps, b, conditions) s = case s of
        M.Assign dest (M.BinaryOp (M.Compare r) a c) -> do
            (left, b1) <- operand a b
            (right, b2) <- operand c b1
            let (x, b3) = fresh b2
                (y, b4) = fresh b3
                leftLocal = negate x - 1
                rightLocal = negate y - 1
                save i v = step "Assign" [("local", MInt i), ("value", v)]
            (more, b5) <- statement s b4
            pure (steps ++ [save leftLocal left, save rightLocal right] ++ more, b5,
                  Map.insert dest (r, localRef leftLocal, localRef rightLocal) conditions)
        M.Assign dest _ -> do
            (more, b') <- statement s b
            pure (steps ++ more, b', Map.delete dest conditions)
        _ -> do
            (more, b') <- statement s b
            pure (steps ++ more, b', conditions)

    localNumber (M.Local i) = toInteger i
    localRef i = record "ValueRef::Local" [("local", MInt i)]
    jump (M.BlockId target) = record "ExecutionEnd::Jump" [("target", MInt (toInteger target))]
    normal r a b = case r of
                Eq -> (0, a, b)
                NotEq -> (1, a, b)
                Lt -> (2, a, b)
                LtEq -> (3, a, b)
                Gt -> (2, b, a)
                GtEq -> (3, b, a)

encode :: M.Program -> Maybe (MirValue, MirValue)
encode program
    | not (Map.null (M.progFunctions program)) = Nothing
    | any (not . null) (Map.elems (M.progInvariants program)) = Nothing
    | any isEnum (Map.elems (M.progTypes program)) = Nothing
    | not (null (M.fnParams mainFn)) = Nothing
    | any (\(M.Local n) -> n < 0) (Map.keys (M.fnLocals mainFn)) = Nothing
    | not (null (M.specRequires spec) && null (M.specEnsures spec)) = Nothing
    | otherwise = do
        (blocks, b) <- foldM add ([], emptyBuild) (Map.toList (M.fnBlocks mainFn))
        let context = record "ValidatorContext" [("equalities", MList []), ("applications", MList (literalApps b)), ("constants", MList (literalTerms b)), ("orders", MList []), ("different", MList []), ("differences", MList [])]
        pure (MList blocks, record "ExecutionState" [("context", context), ("locals", MList [])])
  where
    isEnum M.EnumDecl{} = True
    isEnum _ = False
    mainFn = M.progMain program
    spec = M.fnSpec mainFn
    add (blocks, b) entry = do
        (v, b') <- block mainFn entry b
        pure (blocks ++ [v], b')

-- The first argument is the validated lib/validation.tersus program. A false
-- result means an obligation was unproved; Nothing means the MIR is outside
-- this bridge's current subset (including most loop shapes and function calls).
validateMirSubset :: M.Program -> M.Program -> Result (Maybe Bool) String
validateMirSubset checker program = verifyProgram program `bindResult` \_ -> case encode program of
    Nothing -> Ok Nothing
    Just (blocks, initial) -> runNamedFunction checker "validateExecution" [blocks, MInt 0, initial] `bindResult` \result -> case result of
        Just (MData "ExecutionFlowResult" fields) -> case lookup "status" fields of
            Just (MInt 0) -> Ok (Just True)
            Just (MInt 1) -> Ok (Just False)
            Just (MInt _) -> Ok Nothing
            _ -> Error "Tersus validator returned an invalid status"
        _ -> Error "Tersus validator returned an invalid result"
