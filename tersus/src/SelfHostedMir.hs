-- A conservative bridge from a supported MIR subset to the Tersus checker.
-- Unsupported instructions or proof forms are reported as Nothing, never
-- accepted. This is not used as the production validator.
module SelfHostedMir (validateMirSubset) where

import Control.Monad (foldM)
import Data.List (nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Mir as M
import MirEval (MirValue (..), runNamedFunction)
import MirVerify (verifyProgram)
import StdLib (builtinFunct, stdLibValCtx)
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
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct NewArray) _)) [lengthExpr, valueExpr]) b0 = do
    (lengthSteps, lengthRef, b1) <- proofOperand env lengthExpr b0
    (valueSteps, valueRef, b2) <- proofOperand env valueExpr b1
    let (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
    (steps, b4) <- arraySteps local lengthRef valueRef b3
    pure (lengthSteps ++ valueSteps ++ steps, ref, b4)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Pop) _)) [list]) b0 = do
    (prefix, listRef, b1) <- proofOperand env list b0
    let (i, b2) = fresh b1
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
    (steps, b3) <- popSteps local listRef b2
    pure (prefix ++ steps, ref, b3)
-- Proof parsing leaves pop as a name; it denotes the builtin only when the
-- MIR environment does not bind that name to a program value.
proofOperand env (FApp (ATerm "pop") [list]) b
    | Map.notMember "pop" env = proofOperand env (FApp (CTerm (builtinFunct Pop)) [list]) b
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

popSteps :: Integer -> MirValue -> Build -> Maybe ([MirValue], Build)
popSteps dest listRef b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    let (i, b2) = fresh b1
        local = negate i - 1
        sizeRef = record "ValueRef::Local" [("local", MInt local)]
        size = step "ApplyFresh" [("local", MInt local), ("function", MInt (-13)), ("arguments", MList [listRef])]
        pop = step "Pop" [("local", MInt dest), ("list", listRef)]
    pure ([size, check 2 zero sizeRef, pop], b2)

arraySteps :: Integer -> MirValue -> MirValue -> Build -> Maybe ([MirValue], Build)
arraySteps dest lengthRef valueRef b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    let make = step "NewArray" [("local", MInt dest), ("length", lengthRef), ("value", valueRef)]
    pure ([check 3 zero lengthRef, make], b1)

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

-- Evaluate total expressions before assuming a clause. The reference can
-- assume partial expressions without proving their safety, so decline those
-- rather than treating an unproved safety check as a validation failure.
contractSteps :: Bool -> M.Env -> [ValidationStatement] -> Build -> Maybe ([MirValue], Build)
contractSteps assume env clauses b0 = foldM add ([], b0) clauses
  where
    add (steps, b) (ProofAssert proof) = do
        (prefix, checked, b') <- proofCheck env proof b
        if not assume || all totalStep prefix then Just () else Nothing
        encoded <- if assume then case checked of
            MData "ExecutionStep::Check" fields -> Just (MData "ExecutionStep::Assume" fields)
            _ -> Nothing
          else Just checked
        pure (steps ++ prefix ++ [encoded], b')
    add _ _ = Nothing
    totalStep (MData "ExecutionStep::ApplyFresh" _) = True
    totalStep _ = False

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
statement (M.Assign dest (M.Clone source)) b = statement (M.Assign dest (M.Use source)) b
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
statement (M.Assign (M.Local dest) (M.ListOp M.Pop [source])) b0 = do
    (listRef, b1) <- operand source b0
    popSteps (toInteger dest) listRef b1
statement (M.Assign (M.Local dest) (M.ListOp operation [lengthValue, value])) b0
    | operation == M.NewArray || operation == M.NewBoxed = do
        (lengthRef, b1) <- operand lengthValue b0
        (valueRef, b2) <- operand value b1
        arraySteps (toInteger dest) lengthRef valueRef b2
statement (M.Assign (M.Local dest) (M.ListOp M.NewEmptyBoxed [])) b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    let (i, b2) = fresh b1
        sizeLocal = negate i - 1
        resultRef = record "ValueRef::Local" [("local", MInt (toInteger dest))]
        sizeRef = record "ValueRef::Local" [("local", MInt sizeLocal)]
        make = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (-15)), ("arguments", MList [])]
        size = step "ApplyFresh" [("local", MInt sizeLocal), ("function", MInt (-13)), ("arguments", MList [resultRef])]
        known = step "Assume" [("relation", MInt 0), ("left", sizeRef), ("right", zero)]
    pure ([make, size, known], b2)
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
-- Function bodies are checked independently before the main graph. Function
-- definitions have already been checked for uniqueness and placement.
statement (M.Ghost _ M.GhostFunction{}) b = Just ([], b)
statement _ _ = Nothing

-- A direct call uses only contracts of bodies checked separately. Snapshot
-- arguments before writing the result, and decline callees that reassign a
-- parameter: their postconditions can refer to its final value.
directCall :: M.Function -> M.Function -> [M.Operand] -> M.Local -> Build -> Maybe ([MirValue], Build)
directCall caller callee args (M.Local dest) b0 = do
    if length args == length params then Just () else Nothing
    if all validSizeArg (drop (length args - length (M.fnSizeParams callee)) args) then Just () else Nothing
    if any parameterAssigned (concatMap M.blockStatements (Map.elems (M.fnBlocks callee))) then Nothing else Just ()
    if any terminatorAssignsParameter (map M.blockTerminator (Map.elems (M.fnBlocks callee))) then Nothing else Just ()
    case M.fnReturns callee of Just _ -> Just (); Nothing -> Nothing
    (snapshots, b1) <- foldM snapshot ([], b0) args
    let bindings = Map.fromList (zip params [local | (local, _) <- snapshots])
        remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
        remap constant@(M.Const _) = Just constant
        remap _ = Nothing
        env = Map.mapMaybe remap (M.specEnv (M.fnSpec callee))
    (sizeChecks, withSizes) <- sizeParameterSteps False callee (map fst snapshots) b1
    (checks, b2) <- contractSteps False env (M.specRequires (M.fnSpec callee)) withSizes
    let resultEnv = Map.insert "return" (M.Copy (M.Local dest)) env
    (assumptions, b3) <- contractSteps True resultEnv (M.specEnsures (M.fnSpec callee)) b2
    let (function, b4) = namedFunction ("call:" ++ M.fnName callee) b3
        argumentRefs = [record "ValueRef::Local" [("local", MInt (toInteger n))] | (M.Local n, _) <- snapshots]
        result = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList argumentRefs)]
    pure ([save | (_, save) <- snapshots] ++ sizeChecks ++ checks ++ [result] ++ assumptions, b4)
  where
    params = M.fnParams callee
    callerSizeParams = drop (length (M.fnParams caller) - length (M.fnSizeParams caller)) (M.fnParams caller)
    validSizeArg (M.Const (M.CInt _)) = True
    validSizeArg (M.Copy local) = local `elem` callerSizeParams
    validSizeArg _ = False
    parameterAssigned (M.Assign local _) = local `elem` params
    parameterAssigned (M.Peek local _) = local `elem` params
    parameterAssigned (M.Drop local) = local `elem` params
    parameterAssigned _ = False
    terminatorAssignsParameter (M.Call _ _ local _) = local `elem` params
    terminatorAssignsParameter _ = False
    snapshot (saved, b) arg = do
        (value, b1) <- operand arg b
        let (i, b2) = fresh b1
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            save = step "Assign" [("local", MInt (toInteger number)), ("value", value)]
        pure (saved ++ [(local, save)], b2)

-- Size parameters are the trailing parameters and must be nonnegative. At a
-- call the corresponding fact is an obligation, not an assumption.
sizeParameterSteps :: Bool -> M.Function -> [M.Local] -> Build -> Maybe ([MirValue], Build)
sizeParameterSteps assume fn values b0
    | count > length values = Nothing
    | count == 0 = Just ([], b0)
    | otherwise = do
        (zero, b1) <- operand (M.Const (M.CInt 0)) b0
        let make (M.Local local) = step (if assume then "Assume" else "Check")
                [("relation", MInt 3), ("left", zero), ("right", record "ValueRef::Local" [("local", MInt (toInteger local))])]
        pure (map make (drop (length values - count) values), b1)
  where
    count = length (M.fnSizeParams fn)

-- Facts guaranteed by a value's type are trusted in the same places as in
-- the reference validator: parameters and values assigned to typed locals.
typeSteps :: Map.Map Name M.TypeDecl -> Map.Map Name [ValidationStatement] -> M.Function -> M.Local -> Build -> Maybe ([MirValue], Build)
typeSteps types invariants fn local@(M.Local number) b0 = do
    decl <- Map.lookup local (M.fnLocals fn)
    facts (M.localType decl) b0
  where
    value = record "ValueRef::Local" [("local", MInt (toInteger number))]
    assume relation a b = step "Assume" [("relation", MInt relation), ("left", a), ("right", b)]
    facts TByte b = do
        (zero, b1) <- operand (M.Const (M.CInt 0)) b
        (limit, b2) <- operand (M.Const (M.CInt 256)) b1
        pure ([assume 3 zero value, assume 2 value limit], b2)
    facts (TArrayOf _ (SizeConst size)) b = sized size b
    facts (TBox (TArrayOf _ (SizeConst size))) b = sized size b
    facts (TArrayOf _ (SizeParam name)) b = sizedByParam name b
    facts (TBox (TArrayOf _ (SizeParam name))) b = sizedByParam name b
    facts (TBox inner) b = facts inner b
    facts (TNamed name) b = do
        let base = maybe name fst (instanceOf name)
            clauses = Map.findWithDefault [] base invariants
        if null clauses then Just ([], b) else do
            case instanceOf name of Just _ -> Nothing; Nothing -> Just ()
            fields <- case Map.lookup base types of Just (M.StructDecl fs) -> Just (map fst fs); _ -> Nothing
            (projections, env, b1) <- foldM project ([], Map.empty, b) fields
            (assumptions, b2) <- contractSteps True env clauses b1
            pure (projections ++ assumptions, b2)
    facts _ b = Just ([], b)
    sized size b = do
        (expected, b1) <- operand (M.Const (M.CInt size)) b
        let (i, b2) = fresh b1
            localId = negate i - 1
            sizeRef = record "ValueRef::Local" [("local", MInt localId)]
            apply = step "ApplyFresh" [("local", MInt localId), ("function", MInt (-13)), ("arguments", MList [value])]
        pure ([apply, assume 0 sizeRef expected], b2)
    sizedByParam name b = case [p | p <- sizeParams, Just d <- [Map.lookup p (M.fnLocals fn)], M.localName d == Just name] of
        param : _ -> do
            (expected, b1) <- operand (M.Copy param) b
            let (i, b2) = fresh b1
                localId = negate i - 1
                sizeRef = record "ValueRef::Local" [("local", MInt localId)]
                apply = step "ApplyFresh" [("local", MInt localId), ("function", MInt (-13)), ("arguments", MList [value])]
            pure ([apply, assume 0 sizeRef expected], b2)
        [] -> Just ([], b)
    sizeParams = drop (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn)
    project (steps, env, b) field = do
        let (function, b1) = namedFunction ("field:" ++ field) b
            (i, b2) = fresh b1
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let localId = negate (fromInteger i) - 1
            fieldLocal = M.Local localId
            apply = step "ApplyFresh" [("local", MInt (toInteger localId)), ("function", MInt function), ("arguments", MList [value])]
        pure (steps ++ [apply], Map.insert field (M.Copy fieldLocal) env, b2)

block :: Map.Map Name M.TypeDecl -> Map.Map Name [ValidationStatement] -> Map.Map Name M.Function -> Bool -> M.Function -> (M.BlockId, M.BasicBlock) -> Build -> Maybe (MirValue, Build)
block types invariants functions allowCalls fn (blockId@(M.BlockId n), M.BasicBlock stmts end) b0 = do
    (steps, b1, conditions) <- foldM add ([], b0, Map.empty) stmts
    (extra, ending, b2) <- case (Map.lookup blockId (M.specLoops (M.fnSpec fn)), end) of
        (Just spec, M.SwitchBool (M.Copy local) yes no) -> do
            (loopEnd, b') <- encodeLoop spec local yes no conditions b1
            pure ([], loopEnd, b')
        (Just _, _) -> Nothing
        (Nothing, M.Return) -> do
            let env = Map.insert "return" (M.Copy (M.Local 0)) (M.specEnv (M.fnSpec fn))
            (postconditions, b') <- contractSteps False env (M.specEnsures (M.fnSpec fn)) b1
            let resultCheck = case M.fnReturns fn of
                    Just _ -> [step "RequireDefined" [("value", localRef 0)]]
                    Nothing -> []
            Just (resultCheck ++ postconditions, record "ExecutionEnd::Done" [], b')
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
                    [("yes", MInt (toInteger yesId)), ("no", MInt (toInteger noId)), ("join", MInt (-1)), ("value", ref), ("trueValue", trueRef), ("falseValue", falseRef)]
            Just ([required], ending, b3)
        (Nothing, M.Call (M.Const (M.CFn name)) args dest target) | allowCalls -> do
            callee <- Map.lookup name functions
            (callSteps, b') <- directCall fn callee args dest b1
            (typeFacts, b'') <- typeSteps types invariants fn dest b'
            Just (callSteps ++ typeFacts, jump target, b'')
        _ -> Nothing
    pure (record "ExecutionBlock" [("id", MInt (toInteger n)), ("steps", MList (steps ++ extra)), ("end", ending)], b2)
  where
    -- A loop is checked by its invariant: its region is walked once, and every
    -- edge back to the header has to re-establish the invariant and shrink the
    -- variant. A block that leaves the loop (a return, or an exit from inside
    -- the body) is not in the region and is walked as an exit, as the reference
    -- validator does.
    encodeLoop spec local yes no conditions b = do
        if yes == M.loopBody spec && yes /= blockId && no /= blockId && no /= yes then Just () else Nothing
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
        let region = Map.findWithDefault (Set.singleton blockId) blockId (loopRegions fn)
            assigned = nub
                [ v
                | member <- Set.toList region
                , Just (M.BasicBlock blockStmts term) <- [Map.lookup member (M.fnBlocks fn)]
                , v <- [d | M.Assign d _ <- blockStmts] ++ (case term of M.Call _ _ d _ -> [d]; _ -> [])
                ]
        case upper of
            M.Copy v -> do
                upperDecl <- Map.lookup v (M.fnLocals fn)
                if M.localType upperDecl == TInt && v `notElem` assigned then Just () else Nothing
            M.Const (M.CInt _) -> Just ()
            _ -> Nothing
        (variantRef, b1) <- operand variant b
        (upperRef, b2) <- operand upper b1
        (zeroRef, b3) <- operand (M.Const (M.CInt 0)) b2
        (typeAssumptions, withTypes) <- foldM (loopType fn) ([], b3) assigned
        (checks, assumptions, b4) <- foldM (invariant (M.loopEnv spec)) ([], typeAssumptions, withTypes) (M.loopInvariant spec)
        let (kind, left, right) = normal r a c
            M.BlockId exitId = no
            M.BlockId bodyId = yes
        pure (record "ExecutionEnd::Loop" [("exit", MInt (toInteger exitId)), ("body", MInt (toInteger bodyId)),
             ("region", MList [MInt (toInteger number) | M.BlockId number <- Set.toList region]),
             ("checks", MList checks), ("assumptions", MList assumptions), ("havoc", MList (map (MInt . localNumber) assigned)),
             ("relation", MInt kind), ("left", left), ("right", right), ("variant", variantRef), ("variantMode", MInt mode),
             ("variantOther", upperRef), ("zero", zeroRef)], b4)
    expressionOperand env expr = case expr of
        Var name -> Map.lookup name env
        Val (VInt value) -> Just (M.Const (M.CInt value))
        _ -> Nothing
    invariant env (checks, assumptions, b) (ProofAssert p) = do
        (prefix, checkStep, b') <- proofCheck env p b
        assumption <- asAssumption checkStep
        pure (checks ++ prefix ++ [checkStep], assumptions ++ prefix ++ [assumption], b')
    invariant _ _ _ = Nothing
    loopType current (steps, b) local = do
        (more, b') <- typeSteps types invariants current local b
        pure (steps ++ more, b')
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
            (typeFacts, b6) <- typeSteps types invariants fn dest b5
            pure (steps ++ [save leftLocal left, save rightLocal right] ++ more ++ typeFacts, b6,
                  Map.insert dest (r, localRef leftLocal, localRef rightLocal) conditions)
        M.Assign dest (M.MakeData name fields) -> do
            let base = maybe name fst (instanceOf name)
                clauses = Map.findWithDefault [] base invariants
            case instanceOf name of
                Just _ | not (null clauses) -> Nothing
                _ -> Just ()
            (checks, b1) <- contractSteps False (Map.fromList fields) clauses b
            (more, b2) <- statement s b1
            (typeFacts, b3) <- typeSteps types invariants fn dest b2
            pure (steps ++ checks ++ more ++ typeFacts, b3, Map.delete dest conditions)
        M.Assign dest (M.ListOp M.NewArray [lengthValue, _]) -> do
            decl <- Map.lookup dest (M.fnLocals fn)
            case M.localType decl of
                TArrayOf _ (SizeParam name) ->
                    case [p | p <- drop (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn), Just d <- [Map.lookup p (M.fnLocals fn)], M.localName d == Just name] of
                        p : _ | lengthValue == M.Copy p -> Just ()
                        _ -> Nothing
                _ -> Just ()
            (more, b1) <- statement s b
            (typeFacts, b2) <- typeSteps types invariants fn dest b1
            pure (steps ++ more ++ typeFacts, b2, Map.delete dest conditions)
        M.Assign dest _ -> do
            (more, b') <- statement s b
            (typeFacts, b'') <- typeSteps types invariants fn dest b'
            pure (steps ++ more ++ typeFacts, b'', Map.delete dest conditions)
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

-- The blocks of each loop: its header and every block that can get back to it
-- without passing the header. A block that leaves the loop (a return, or an
-- exit from inside the body) is not in the region, so the checker walks it as
-- an exit from the loop, as the reference validator does.
loopRegions :: M.Function -> Map.Map M.BlockId (Set.Set M.BlockId)
loopRegions fn = Map.mapWithKey regionOf (M.specLoops (M.fnSpec fn))
  where
    blocks = M.fnBlocks fn
    succs b = maybe [] (M.successors . M.blockTerminator) (Map.lookup b blocks)
    (_, _, _, backEdges) = dfs (Set.empty, [], Set.empty, []) (M.BlockId 0)
    dfs (seen, acc, active, edges) b
        | Set.member b seen = (seen, acc, active, edges)
        | otherwise =
            let visit (s0, a0, act0, e0) next
                    | Set.member next act0 = (s0, a0, act0, (b, next) : e0)
                    | otherwise = dfs (s0, a0, act0, e0) next
                (s1, a1, _, e1) = foldl visit (Set.insert b seen, acc, Set.insert b active, edges) (succs b)
             in (s1, b : a1, active, e1)
    preds = Map.fromListWith (++) [(target, [from]) | from <- Map.keys blocks, target <- succs from]
    regionOf header _ = go (Set.singleton header) [from | (from, target) <- backEdges, target == header]
    go seen [] = seen
    go seen (b : rest)
        | Set.member b seen = go seen rest
        | otherwise = go (Set.insert b seen) (Map.findWithDefault [] b preds ++ rest)

encodeFunction :: Map.Map Name M.TypeDecl -> Map.Map Name [ValidationStatement] -> Map.Map Name M.Function -> Bool -> M.Function -> Maybe (MirValue, MirValue, Integer)
encodeFunction types invariants functions allowCalls fn
    | any (\(M.Local n) -> n < 0) (Map.keys (M.fnLocals fn)) = Nothing
    | length (M.fnParams fn) /= length (nub (M.fnParams fn)) = Nothing
    | M.Local 0 `elem` M.fnParams fn = Nothing
    | length (M.fnSizeParams fn) > length (M.fnParams fn) = Nothing
    | length (M.fnSizeParams fn) /= length (nub (M.fnSizeParams fn)) = Nothing
    | any ambiguousSizeName (M.fnSizeParams fn) = Nothing
    | any parameterAssigned sizeParams = Nothing
    | any wrongSizeName (zip sizeParams (M.fnSizeParams fn)) = Nothing
    | M.specTermination spec /= Nothing = Nothing
    | Map.member (M.BlockId (-1)) (M.fnBlocks fn) = Nothing
    | otherwise = do
        let (params, start) = foldl addParam ([], emptyBuild) (M.fnParams fn)
        (paramFacts, withTypes) <- foldM addType ([], start) (M.fnParams fn)
        (sizeFacts, withSizes) <- sizeParameterSteps True fn (M.fnParams fn) withTypes
        (requires, withRequires) <- contractSteps True (M.specEnv spec) (M.specRequires spec) withSizes
        (blocks, b) <- foldM add ([], withRequires) (Map.toList (M.fnBlocks fn))
        let context = record "ValidatorContext" [("equalities", MList []), ("applications", MList (literalApps b)), ("constants", MList (literalTerms b)), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList []), ("constructorFunctions", MList []), ("constructorFields", MList []), ("differences", MList [])]
            entry = record "ExecutionBlock" [("id", MInt (-1)), ("steps", MList (paramFacts ++ sizeFacts ++ requires)), ("end", record "ExecutionEnd::Jump" [("target", MInt 0)])]
        pure (MList (entry : blocks), record "ExecutionState" [("context", context), ("locals", MList params)], -1)
  where
    spec = M.fnSpec fn
    sizeParams = drop (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn)
    parameterAssigned local = any (writes local) (concatMap M.blockStatements (Map.elems (M.fnBlocks fn))) || any (terminatorWrites local . M.blockTerminator) (Map.elems (M.fnBlocks fn))
    writes local (M.Assign dest _) = local == dest
    writes local (M.Peek dest _) = local == dest
    writes local (M.Drop dest) = local == dest
    writes _ _ = False
    terminatorWrites local (M.Call _ _ dest _) = local == dest
    terminatorWrites _ _ = False
    wrongSizeName (local, name) = (M.localName =<< Map.lookup local (M.fnLocals fn)) /= Just name
    ambiguousSizeName name = length [p | p <- M.fnParams fn, Just d <- [Map.lookup p (M.fnLocals fn)], M.localName d == Just name] /= 1
    addParam (params, b) (M.Local local) =
        let (term, b') = fresh b
            binding = record "LocalBinding" [("local", MInt (toInteger local)), ("term", MInt term)]
         in (params ++ [binding], b')
    addType (steps, b) local = do
        (more, b') <- typeSteps types invariants fn local b
        pure (steps ++ more, b')
    add (blocks, b) entry = do
        (v, b') <- block types invariants functions allowCalls fn entry b
        pure (blocks ++ [v], b')

encode :: M.Program -> Maybe [(MirValue, MirValue, Integer)]
encode program
    | any isEnum (Map.elems (M.progTypes program)) = Nothing
    -- Results of world-reading functions are not determined by arguments.
    | not (Set.null (M.readersOfInput program)) = Nothing
    | not (null (M.fnParams (M.progMain program))) = Nothing
    | not (null (M.specRequires mainSpec) && null (M.specEnsures mainSpec)) = Nothing
    | any invalidDefinition definitions = Nothing
    | length names /= length (nub names) = Nothing
    | any (\name -> Map.member name (fst stdLibValCtx)) names = Nothing
    | length targets /= length (nub targets) = Nothing
    | length targets /= Map.size (M.progFunctions program) = Nothing
    | any (\name -> Map.notMember name (M.progFunctions program)) targets = Nothing
    | any (\(name, fn) -> name /= M.fnName fn) (Map.toList (M.progFunctions program)) = Nothing
    | any invalidCall functionCalls = Nothing
    | otherwise = do
        let functions = M.progFunctions program
            invariants = M.progInvariants program
            types = M.progTypes program
        checked <- traverse (encodeFunction types invariants functions True) (Map.elems functions)
        main <- encodeFunction types invariants functions True (M.progMain program)
        pure (checked ++ [main])
  where
    isEnum M.EnumDecl{} = True
    isEnum _ = False
    mainSpec = M.fnSpec (M.progMain program)
    definitions = [(isMain, blockId, name, source, top) | (isMain, fn) <- (True, M.progMain program) : [(False, f) | f <- Map.elems (M.progFunctions program)],
        (blockId, block') <- Map.toList (M.fnBlocks fn), M.Ghost _ (M.GhostFunction name source top) <- M.blockStatements block']
    names = [source | (_, _, _, source, _) <- definitions]
    targets = [name | (_, _, name, _, _) <- definitions]
    invalidDefinition (isMain, blockId, _, _, top) = not top || not isMain || blockId /= M.BlockId 0
    definitionOrder = Map.fromList (zip targets [0 :: Int ..])
    functionCalls = [(name, called) | (name, fn) <- Map.toList (M.progFunctions program),
        block' <- Map.elems (M.fnBlocks fn), M.Call (M.Const (M.CFn called)) _ _ _ <- [M.blockTerminator block']]
    invalidCall (caller, called) = case (Map.lookup caller definitionOrder, Map.lookup called definitionOrder) of
        (Just callerIndex, Just calledIndex) -> calledIndex >= callerIndex
        _ -> True

-- The first argument is the validated lib/validation.tersus program. A false
-- result means an obligation was unproved; Nothing means the MIR is outside
-- this bridge's current subset (including most loop shapes and function calls).
validateMirSubset :: M.Program -> M.Program -> Result (Maybe Bool) String
validateMirSubset checker program = verifyProgram program `bindResult` \_ -> case encode program of
    Nothing -> Ok Nothing
    Just functions -> checkFunctions functions
  where
    checkFunctions [] = Ok (Just True)
    checkFunctions ((blocks, initial, entry) : rest) = runNamedFunction checker "validateExecution" [blocks, MInt entry, initial] `bindResult` \result -> case result of
        Just (MData "ExecutionFlowResult" fields) -> case lookup "status" fields of
            Just (MInt 0) -> checkFunctions rest
            Just (MInt 1) -> Ok (Just False)
            Just (MInt _) -> Ok Nothing
            _ -> Error "Tersus validator returned an invalid status"
        _ -> Error "Tersus validator returned an invalid result"
