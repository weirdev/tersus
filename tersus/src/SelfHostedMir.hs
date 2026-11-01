-- The bridge from MIR to the validator written in Tersus
-- (lib/validation.tersus): encode is a data-only translation, and anything it
-- does not fully model is reported as an Unmodeled verdict, never accepted.
module SelfHostedMir (Verdict (..), verdictProved, validateMirSubset, validateByTersus, encode) where

import Control.Monad (foldM)
import Data.List (find, isPrefixOf, nub)
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Control.Applicative ((<|>))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Mir as M
import MirEval (MirValue (..), runNamedFunction)
import MirGhost (eraseGhosts)
import MirLower (lowerElaborated)
import MirMono (monomorphizeForValidation)
import MirVerify (verifyProgram)
import Libraries (parseSourceWith)
import PreludeSource (validationSource)
import StdLib (builtinFunct, eqVarProof, stdLibRuleCtx)
import StdLibDefs (stdLibValCtx)
import TersusTypes
import TypeCheck (elaborate)
import Utils (Result (..), bindResult, inIntRange)

data Build = Build { nextTerm :: Integer, literalIds :: [(M.Constant, Integer)], literalTerms :: [MirValue], literalApps :: [MirValue], namedFunctions :: [(String, Integer)], ctorFields :: [(Integer, Integer, Integer)], buildFunctions :: Map.Map Name M.Function, buildRules :: Rules, buildInline :: Int }

emptyBuild :: Build
emptyBuild = Build 0 [] [] [] [] [] Map.empty Map.empty 0

record :: String -> [(String, MirValue)] -> MirValue
record = MData

localNum :: M.Local -> Integer
localNum (M.Local n) = toInteger n

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
proofOperand env (BVar name) b = do
    o <- Map.lookup name env
    (v, b') <- operand o b
    pure ([], v, b')
proofOperand _ (CTerm (VInt n)) b = do
    (v, b') <- operand (M.Const (M.CInt n)) b
    pure ([], v, b')
proofOperand _ (CTerm (VBool x)) b = do
    (v, b') <- operand (M.Const (M.CBool x)) b
    pure ([], v, b')
proofOperand _ (CTerm (VList values)) b = do
    constants <- mapM valueConstant values
    (v, b') <- operand (M.Const (M.CList constants)) b
    pure ([], v, b')
  where
    valueConstant (VInt n) = Just (M.CInt n)
    valueConstant (VBool x) = Just (M.CBool x)
    valueConstant (VList vs) = M.CList <$> mapM valueConstant vs
    valueConstant (VData name fields) = M.CData name <$> mapM (\(f, v) -> (,) f <$> valueConstant v) fields
    valueConstant _ = Nothing
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct ToByte) _)) [arg]) b = proofOperand env arg b
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct BytesFrom) _)) [arg]) b = proofOperand env arg b
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct DerefOf) _)) [arg]) b = proofOperand env arg b
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct FromByte) _)) [arg]) b = proofOperand env arg b
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
        -- A get in a proof is a term, as in the reference: its bounds are
        -- checked where a get runs in code, not where one is written in a
        -- contract or an affirm.
        steps = [step "ApplyFresh" [("local", MInt local), ("function", MInt (-14)), ("arguments", MList [listRef, indexRef])]]
    pure (listSteps ++ indexSteps ++ steps, ref, b3)
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
-- A program function named in a proof denotes the same call application as a
-- call in the code, so its result is the term the function's contract speaks of.
proofOperand env (FApp (ATerm name) args) b0
    | Just (M.Const (M.CFn callee)) <- Map.lookup name env = do
        (prefixes, refs, b1) <- foldM evalArg ([], [], b0) args
        let (function, b2) = namedFunction ("call:" ++ callee) b1
            (i, b3) = fresh b2
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList refs)]
        (facts, b4) <- proofCallFacts callee refs local b3
        pure (prefixes ++ [apply] ++ facts, ref, b4)
  where
    evalArg (steps, refs, b) arg = do
        (more, ref, b') <- proofOperand env arg b
        pure (steps ++ more, refs ++ [ref], b')

-- A method named in a proof of its own impl is named by its source
-- name (sz), where the environment binds the function it denotes by
-- its full name (<HM>::sz): the one the name is the source name of.
proofOperand env (FApp (ATerm name) args) b
    | Map.notMember name env
    , [full] <- [key | (key, M.Const (M.CFn _)) <- Map.toList env, sourceNameOf key == name] =
        proofOperand env (FApp (ATerm full) args) b
  where
    sourceNameOf key = case break (== ':') (reverse key) of
        (revSuffix, ':' : ':' : _) -> reverse revSuffix
        _ -> key
-- Builtins also occur in proofs under their source names (size, get, ...);
-- they denote the builtin only when the name is not a program value.
proofOperand env (FApp (ATerm name) args) b
    | Map.notMember name env = case name of
        "size" -> proofOperand env (FApp (CTerm (builtinFunct Size)) args) b
        "get" -> proofOperand env (FApp (CTerm (builtinFunct Get)) args) b
        "first" -> proofOperand env (FApp (CTerm (builtinFunct First)) args) b
        "last" -> proofOperand env (FApp (CTerm (builtinFunct Last)) args) b
        "push" -> proofOperand env (FApp (CTerm (builtinFunct Push)) args) b
        "set" -> proofOperand env (FApp (CTerm (builtinFunct Set)) args) b
        "newArray" -> proofOperand env (FApp (CTerm (builtinFunct NewArray)) args) b
        "toByte" -> case args of
            [arg] -> proofOperand env arg b
            _ -> Nothing
        "toInt" -> case args of
            [arg] -> proofOperand env arg b
            _ -> Nothing
        _ -> Nothing
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
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variantName)) _)) [arg]) b0 = do
    (prefix, value, b1) <- proofOperand env arg b0
    let (predicate, b2) = namedFunction ("isvariant:" ++ variantName) b1
        (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt predicate), ("arguments", MList [value])]
    pure (prefix ++ [apply], ref, b3)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args) b0 = do
    (prefixes, refs, b1) <- foldM evalArg ([], [], b0) args
    let (constructor, b2) = namedFunction ("ctor:" ++ name) b1
        (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt constructor), ("arguments", MList refs)]
        (fieldIds, b4) = foldl register ([], b3) fields
        b5 = b4{ctorFields = nub ([(constructor, fieldId, toInteger index) | (index, fieldId) <- zip [0 ..] fieldIds] ++ ctorFields b4)}
    pure (prefixes ++ [apply], ref, b5)
  where
    evalArg (steps, refs, b) arg = do
        (more, ref, b') <- proofOperand env arg b
        pure (steps ++ more, refs ++ [ref], b')
    register (ids, b) field = let (fieldId, b') = namedFunction ("field:" ++ field) b in (ids ++ [fieldId], b')
-- A relation used as a value in a proof (`return = (a = b)` in a contract) is
-- the comparison application itself, as a comparison in code is.
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel r)) _)) [a, b]) b0 = do
    (leftSteps, x, b1) <- proofOperand env a b0
    (rightSteps, y, b2) <- proofOperand env b b1
    let function = case r of
            Eq -> -6
            NotEq -> -7
            Lt -> -8
            LtEq -> -9
            Gt -> -10
            GtEq -> -11
        (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [x, y])]
    pure (leftSteps ++ rightSteps ++ [apply], ref, b3)
-- What a permission is (its base, its size, its ghost arrays, ...): an
-- application the contracts relate, as a field is.
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct f) _)) args) b0
    | Just name <- accessorName f = do
        (prefixes, refs, b1) <- foldM evalArg ([], [], b0) args
        let (function, b2) = namedFunction name b1
            (i, b3) = fresh b2
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList refs)]
        pure (prefixes ++ [apply], ref, b3)
  where
    evalArg (steps, refs, b) arg = do
        (more, ref, b') <- proofOperand env arg b
        pure (steps ++ more, refs ++ [ref], b')
    accessorName g = case g of
        BlockBase -> Just "blockbase"
        BlockCap -> Just "blockcap"
        BlockOrigin -> Just "blockorigin"
        BlockStart -> Just "blockstart"
        BlockExtent -> Just "blockextent"
        BlockCount -> Just "blockcount"
        BlockFilled -> Just "blockfilled"
        BlockContents -> Just "blockcontents"
        UninitFilled -> Just "uninitfilled"
        UninitAt -> Just "uninitat"
        AddrOffset -> Just "ghostop:addroffset"
        AddrCast -> Just "ghostop:addrcast"
        AddrToInt -> Just "ghostop:addrtoint"
        AddrFromInt -> Just "ghostop:addrfromint"
        _ -> Nothing
-- An operation on a permission in a proof (the parts of one, in the
-- contract of another): an application, with what the operation needs
-- and promises, as a call in the code is worth.
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct f) _)) args) b0
    | Just _ <- pointerFunctName f = do
        (prefixes, refs, b1) <- foldM evalArg ([], [], b0) args
        let (function, b2) = namedFunction ("ghostop:" ++ pointerFunctName' f) b1
            (i, b3) = fresh b2
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList refs)]
        (facts, b4) <- builtinCallFacts f refs local b3
        pure (prefixes ++ [apply] ++ facts, ref, b4)
  where
    evalArg (steps, refs, b) arg = do
        (more, ref, b') <- proofOperand env arg b
        pure (steps ++ more, refs ++ [ref], b')
    pointerFunctName g = case g of
        BlockNew -> Just ()
        BlockTaken -> Just ()
        BlockResized -> Just ()
        BlockSplitLo -> Just ()
        BlockSplitHi -> Just ()
        BlockJoin -> Just ()
        BlockAssume -> Just ()
        BlockCast -> Just ()
        _ -> Nothing
    pointerFunctName' g = case g of
        BlockNew -> "blocknew"
        BlockTaken -> "blocktaken"
        BlockResized -> "blockresized"
        BlockSplitLo -> "blocksplitlo"
        BlockSplitHi -> "blocksplithi"
        BlockJoin -> "blockjoin"
        BlockAssume -> "blockassume"
        BlockCast -> "blockcast"
        _ -> "op"
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

-- What a call of an operation on a permission is worth: what it needs
-- (checked) and what it promises (assumed of the application's term),
-- one level deep, as proofCallFacts does for a function of the program.
builtinCallFacts :: BuiltinFunct -> [MirValue] -> Integer -> Build -> Maybe ([MirValue], Build)
builtinCallFacts funct refs result b
    | buildInline b > 0 = pure ([], b)
    | Just (params, ins, outs) <- builtinSpecOf funct
    , length argOperands == length refs
    , length params == length refs = do
        let env = Map.insert "return" (M.Copy (M.Local (fromInteger result))) (Map.fromList (zip params argOperands))
            deeper = b{buildInline = buildInline b + 1}
        (required, b1) <- contractSteps (buildRules b) False env ins deeper
        (promised, b2) <- contractSteps (buildRules b) True env outs b1
        pure (required ++ promised, b2{buildInline = buildInline b})
    | otherwise = pure ([], b)
  where
    argOperands = [op | ref <- refs, Just op <- [refOperandOf b ref]]


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

-- The operand a step's value reference names, where it names a local
-- or a literal: what a contract is bound with at a call.
refOperandOf :: Build -> MirValue -> Maybe M.Operand
refOperandOf b (MData "ValueRef::Local" fields) = case lookup "local" fields of
    Just (MInt n) -> Just (M.Copy (M.Local (fromInteger n)))
    _ -> Nothing
refOperandOf b (MData "ValueRef::Term" fields) = case lookup "term" fields of
    Just (MInt t) -> case [c | (c, i) <- literalIds b, i == t] of
        c : _ -> Just (M.Const c)
        [] -> Nothing
    _ -> Nothing
refOperandOf _ _ = Nothing

-- What a call in a proof is worth beyond the call application itself:
-- the callee's ensures, with its parameters bound to the argument
-- terms and its result to the application's term, as a call in the
-- code is worth. One level only: a contract whose proofs call again
-- leaves those inner calls as applications.
proofCallFacts :: Name -> [MirValue] -> Integer -> Build -> Maybe ([MirValue], Build)
proofCallFacts callee refs result b
    | Just fn <- Map.lookup callee (buildFunctions b)
    , M.specTermination (M.fnSpec fn) == Just MayDiverge = Nothing
    | buildInline b > 0 = pure ([], b)
    | Just fn <- Map.lookup callee (buildFunctions b)
    , length argOperands == length argRefs
    , let params = take (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn)
    , length params == length argRefs = do
        let bindings = Map.fromList (zip params argOperands)
            substitute op = case op of
                M.Copy l | Just replacement <- Map.lookup l bindings -> replacement
                M.Move l | Just replacement <- Map.lookup l bindings -> replacement
                _ -> op
            env = Map.insert "return" (M.Copy (M.Local (fromInteger result))) (Map.map substitute (M.specEnv (M.fnSpec fn)))
            deeper = b{buildInline = buildInline b + 1}
        (required, b1) <- contractSteps (buildRules b) False env (M.specRequires (M.fnSpec fn)) deeper
        (promised, b2) <- contractSteps (buildRules b) True env (M.specEnsures (M.fnSpec fn)) b1
        pure (required ++ promised, b2{buildInline = buildInline b})
    | otherwise = pure ([], b)
  where
    argOperands = [op | ref <- refs, Just op <- [refOperandOf b ref]]
    argRefs = refs

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
-- A bounded forall is checked by universal generalisation: the index is
-- havoced to a fresh term, the guards are assumed for it, and the body is
-- checked. (Using such a fact at a particular index is not modelled yet.)
proofCheck env (Forall index guards body) b0 = do
    let (i, b1) = fresh b0
        local = negate i - 1
        env' = Map.insert index (M.Copy (M.Local (fromInteger local))) env
        havoc = step "Havoc" [("local", MInt local)]
        assumeGuard (steps, b) guard = do
            (prefix, checked, b') <- proofCheck env' guard b
            if all totalStep prefix then Just () else Nothing
            assumed <- case checked of
                MData "ExecutionStep::Check" fields -> Just (MData "ExecutionStep::Assume" fields)
                _ -> Nothing
            pure (steps ++ prefix ++ [assumed], b')
        totalStep (MData "ExecutionStep::ApplyFresh" _) = True
        totalStep _ = False
    (guardSteps, b2) <- foldM assumeGuard ([], b1) guards
    (bodyPrefix, checked, b3) <- proofCheck env' body b2
    -- The check is scoped to the havoced index: everything the guards and
    -- the body made of it is forgotten once the body is checked, because
    -- an index whose guards cannot hold (an empty range) must not leave
    -- the context contradictory for what follows.
    let (fi, b4) = fresh b3
        forget = step "ApplyFresh" [("local", MInt (negate fi - 1)), ("function", MInt (-40)), ("arguments", MList [record "ValueRef::Local" [("local", MInt local)]])]
    pure (havoc : guardSteps ++ bodyPrefix ++ [checked], forget, b4)
proofCheck env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variantName)) _)) [arg]) b0 = do
    (prefix, value, b1) <- proofOperand env arg b0
    let (familyId, b2) = namedFunction ("enum:" ++ takeWhile (/= ':') variantName) b1
        (constructorId, b3) = namedFunction ("variant:" ++ variantName) b2
        require = step "RequireVariant" [("object", value), ("family", MInt familyId), ("constructor", MInt constructorId)]
    pure (prefix, require, b3)
proofCheck _ _ _ = Nothing

-- A forall over the elements of two lists, assumed as one fact (function
-- -30) that the checker instantiates: `forall j in lo..hi: get(a, j) =
-- get(b, j)`. An index the guards exclude (`j != i`: the one slot an
-- operation changed) splits the range at that index: one fact below it
-- and one above it, so nothing is claimed of the changed slot.
forallFactSteps :: M.Env -> VariableProof -> Build -> Maybe ([MirValue], Build)
forallFactSteps env (Forall index guards body) b0
    | otherwise = case body of
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [x, y]
        | Just (a1, base, c) <- constSide x y -> emitConst a1 base c
        | Just (a1, base, c) <- constSide y x -> emitConst a1 base c
      where
        constSide g c = do
            (list, off) <- getParts g
            if mentionsIndex c then Nothing else Just ()
            Just (list, maybe (CTerm (VInt 0)) id off, c)
        emitConst a1 base c = do
            if any excluded guards then Nothing else Just ()
            lo <- guardLo
            hi <- guardHi
            (sA, refA, b1) <- proofOperand env a1 b0
            (sC, refC, b2) <- proofOperand env c b1
            (sLo, refLo, b3) <- proofOperand env lo b2
            (sHi, refHi, b4) <- proofOperand env hi b3
            (sBase, refBase, b5) <- proofOperand env base b4
            let (i, b6) = fresh b5
                local = negate i - 1
                apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (-32)), ("arguments", MList [refA, refLo, refHi, refBase, refC])]
            pure (sA ++ sC ++ sLo ++ sHi ++ sBase ++ [apply], b6)
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [x, y]
        | Just (a1, base, a2, delta, mode) <- shiftSide x y -> emitShift a1 base a2 delta mode
        | Just (a1, base, a2, delta, mode) <- shiftSide y x -> emitShift a1 base a2 delta mode
      where
        shiftSide g e = do
            (listA, off) <- getParts g
            (listB, delta, mode) <- shiftParts e
            Just (listA, maybe (CTerm (VInt 0)) id off, listB, delta, mode)
        shiftParts (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [g, d]) = do
            (listB, off) <- getParts g
            if off == Nothing && not (mentionsIndex d) then Just () else Nothing
            Just (listB, d, 0)
        shiftParts (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [d, g]) = do
            (listB, off) <- getParts g
            if off == Nothing && not (mentionsIndex d) then Just () else Nothing
            Just (listB, d, 0)
        shiftParts (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Minus) _)) [g, d]) = do
            (listB, off) <- getParts g
            if off == Nothing && not (mentionsIndex d) then Just () else Nothing
            Just (listB, d, 1)
        shiftParts _ = Nothing
        emitShift a1 base a2 delta mode = do
            if any excluded guards then Nothing else Just ()
            lo <- guardLo
            hi <- guardHi
            (sA, refA, b1) <- proofOperand env a1 b0
            (sB, refB, b2) <- proofOperand env a2 b1
            (sLo, refLo, b3) <- proofOperand env lo b2
            (sHi, refHi, b4) <- proofOperand env hi b3
            (sBase, refBase, b5) <- proofOperand env base b4
            (sD, refD, b6) <- proofOperand env delta b5
            (sM, refM, b7) <- proofOperand env (CTerm (VInt mode)) b6
            let (i, b8) = fresh b7
                local = negate i - 1
                apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (-33)), ("arguments", MList [refA, refB, refLo, refHi, refBase, refD, refM])]
            pure (sA ++ sB ++ sLo ++ sHi ++ sBase ++ sD ++ sM ++ [apply], b8)
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [x, y] -> do
        (listL, offL) <- getParts x
        (listR, offR) <- getParts y
        (a1, a2, base) <- case (offL, offR) of
            (Nothing, Nothing) -> Just (listL, listR, CTerm (VInt 0))
            (Just e, Nothing) -> Just (listL, listR, e)
            (Nothing, Just e) -> Just (listR, listL, e)
            (Just _, Just _) -> Nothing
        lo <- guardLo
        hi <- guardHi
        (sA, refA, b1) <- proofOperand env a1 b0
        (sB, refB, b2) <- proofOperand env a2 b1
        (sLo, refLo, b3) <- proofOperand env lo b2
        (sHi, refHi, b4) <- proofOperand env hi b3
        (sBase, refBase, b5) <- proofOperand env base b4
        let (i, b6) = fresh b5
            local = negate i - 1
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (-30)), ("arguments", MList [refA, refB, refLo, refHi, refBase])]
            baseSteps = sA ++ sB ++ sLo ++ sHi ++ sBase
        case exclusionProof of
            Just excl -> do
                (sE, refE, c1) <- proofOperand env excl b5
                (sOne, refOne, c2) <- proofOperand env (CTerm (VInt 1)) c1
                let (pi, c3) = fresh c2
                    plocal = negate pi - 1
                    plus = step "ApplyFresh" [("local", MInt plocal), ("function", MInt (-1)), ("arguments", MList [refE, refOne])]
                    (i1, c4) = fresh c3
                    below = step "ApplyFresh" [("local", MInt (negate i1 - 1)), ("function", MInt (-30)), ("arguments", MList [refA, refB, refLo, refE, refBase])]
                    (i2, c5) = fresh c4
                    above = step "ApplyFresh" [("local", MInt (negate i2 - 1)), ("function", MInt (-30)), ("arguments", MList [refA, refB, record "ValueRef::Local" [("local", MInt plocal)], refHi, refBase])]
                pure (baseSteps ++ sE ++ sOne ++ [plus, below, above], c5)
            Nothing
                | any excluded guards -> Nothing
                | otherwise -> pure (baseSteps ++ [apply], b6)
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [x, y] -> do
        if any excluded guards then Nothing else Just ()
        (a1, base) <- getArg x
        if indexOf x == Just index && not (mentionsIndex y) then Just () else Nothing
        lo <- guardLo
        hi <- guardHi
        (sA, refA, b1) <- proofOperand env a1 b0
        (sC, refC, b2) <- proofOperand env y b1
        (sLo, refLo, b3) <- proofOperand env lo b2
        (sHi, refHi, b4) <- proofOperand env hi b3
        (sBase, refBase, b5) <- proofOperand env base b4
        let (i, b6) = fresh b5
            local = negate i - 1
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (-31)), ("arguments", MList [refA, refLo, refHi, refBase, refC])]
        pure (sA ++ sC ++ sLo ++ sHi ++ sBase ++ [apply], b6)
    _ -> Nothing
  where
    getParts (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [list, idx]) = case idx of
        BVar i -> if i == index then Just (list, Nothing) else Nothing
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [e, BVar i] -> if i == index && not (mentionsIndex e) then Just (list, Just e) else Nothing
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [BVar i, e] -> if i == index && not (mentionsIndex e) then Just (list, Just e) else Nothing
        _ -> Nothing
    excluded (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [BVar i, _]) = i == index
    excluded (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [_, BVar i]) = i == index
    excluded _ = False
    exclusionProof = case [e | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [BVar i, e] <- guards, i == index, not (mentionsIndex e)] ++ [e | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel NotEq)) _)) [e, BVar i] <- guards, i == index, not (mentionsIndex e)] of
        e : _ -> Just e
        [] -> Nothing
    mentionsIndex (BVar i) = i == index
    mentionsIndex (FApp f args) = mentionsIndex f || any mentionsIndex args
    mentionsIndex _ = False
    indexOf (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [_, idx]) = case idx of
        BVar i -> Just i
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [_, BVar i] -> Just i
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [BVar i, _] -> Just i
        _ -> Nothing
    indexOf _ = Nothing
    -- get(a, base + j) or get(a, j): the list and the offset of the index
    getArg (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [list, idx]) = case idx of
        BVar i -> Just (list, CTerm (VInt 0))
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [e, BVar i] -> if mentions e then Nothing else Just (list, e)
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct Plus) _)) [BVar i, e] -> if mentions e then Nothing else Just (list, e)
        _ -> Nothing
      where
        mentions (BVar i) = i == index
        mentions (FApp f args) = mentions f || any mentions args
        mentions _ = False
    getArg _ = Nothing
    guardLo = case [e | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel GtEq)) _)) [BVar i, e] <- guards, i == index] ++ [e | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Lt)) _)) [e, BVar i] <- guards, i == index] of
        e : _ -> Just e
        [] -> Nothing
    guardHi = case [e | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Lt)) _)) [BVar i, e] <- guards, i == index] ++ [e | FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Gt)) _)) [e, BVar i] <- guards, i == index] of
        e : _ -> Just e
        [] -> Nothing
forallFactSteps _ _ _ = Nothing

-- Evaluate total expressions before assuming a clause. The reference can
-- assume partial expressions without proving their safety, so decline those
-- rather than treating an unproved safety check as a validation failure.
contractSteps :: Rules -> Bool -> M.Env -> [ValidationStatement] -> Build -> Maybe ([MirValue], Build)
contractSteps rules assume env clauses b0 = do
    (steps, _, b) <- foldM add ([], Map.empty, b0) clauses
    pure (steps, b)
  where
    add (steps, subst, b) clause = case clause of
        ProofAssert proof
            | assume, Just (fsteps, b') <- forallFactSteps env (substituteProof subst proof) b -> pure (steps ++ fsteps, subst, b')
            -- A forall that is not one of the fact shapes is assumed as
            -- nothing: the havoced-instance encoding assumes the guards
            -- for one index, and an index whose guards cannot hold would
            -- make the whole context contradictory.
            | assume, Forall _ _ _ <- substituteProof subst proof -> pure (steps, subst, b)
            | otherwise -> do
                (prefix, checked, b') <- proofCheck env (substituteProof subst proof) b
                if not assume || callsFunction env (substituteProof subst proof) || all droppable prefix then Just () else Nothing
                encoded <- if assume then case checked of
                    MData "ExecutionStep::Check" fields -> Just (MData "ExecutionStep::Assume" fields)
                    MData "ExecutionStep::RequireVariant" fields -> Just (MData "ExecutionStep::AssumeVariant" (fields ++ [("matches", MBool True)]))
                    _ -> Nothing
                  else Just checked
                pure (steps ++ (if assume && not (callsFunction env (substituteProof subst proof)) then filter keptStep prefix else prefix) ++ [encoded], subst, b')
        AssignProofVar var expr -> pure (steps, Map.insert var (substituteProof subst (exprToProof expr)) subst, b)
        Rewrite rule -> do
            (more, b') <- if assume then assumeRule (substituteRule subst rule) b else rewriteSteps rules env (substituteRule subst rule) b
            pure (steps ++ more, subst, b')
        _ -> Nothing
    assumeRule (UserRewrite name args) b = assumeRewrite (UserRewrite name args) b
    assumeRule (CheckRel proof) b = assumeProof proof b
    assumeRule (CheckGtZero proof) b = assumeProof (FApp (CTerm (builtinFunct (Rel Gt))) [proof, CTerm (VInt 0)]) b
    assumeRule (Refl proof) b = assumeProof (FApp eqVarProof [proof, proof]) b
    assumeRule _ _ = Nothing
    assumeProof (Forall _ _ _) b = pure ([], b)
    assumeProof proof b = do
        (prefix, checked, b') <- proofCheck env proof b
        if all droppable prefix then Just () else Nothing
        encoded <- case checked of
            MData "ExecutionStep::Check" fields -> Just (MData "ExecutionStep::Assume" fields)
            _ -> Nothing
        pure (filter keptStep prefix ++ [encoded], b')
    -- A clause list that is itself assumed assumes a rewrite's inputs too:
    -- they are part of the same hypothesis.
    assumeRewrite (UserRewrite name args) b0 = do
        (params, ins, outs, _) <- Map.lookup name rules
        if length params == length args then Just () else Nothing
        let substIn = buildSubst (Map.fromList (zip params args)) ins
        inClauses <- instantiate substIn ins
        (s1, b1) <- contractSteps rules True env inClauses b0
        let substOut = buildSubst substIn outs
        outClauses <- instantiate substOut outs
        (s2, b2) <- contractSteps rules True env outClauses b1
        pure (s1 ++ s2, b2)
    assumeRewrite _ _ = Nothing
    -- A clause list that is itself assumed assumes a rewrite's inputs too:
    -- they are part of the same hypothesis.
    assumeRewrite (UserRewrite name args) b0 = do
        (params, ins, outs, _) <- Map.lookup name rules
        if length params == length args then Just () else Nothing
        let substIn = buildSubst (Map.fromList (zip params args)) ins
        inClauses <- instantiate substIn ins
        (s1, b1) <- contractSteps rules True env inClauses b0
        let substOut = buildSubst substIn outs
        outClauses <- instantiate substOut outs
        (s2, b2) <- contractSteps rules True env outClauses b1
        pure (s1 ++ s2, b2)
    assumeRewrite _ _ = Nothing
    totalStep (MData "ExecutionStep::ApplyFresh" _) = True
    totalStep _ = False
    -- An assumed clause may mention a partial expression (a get, a division):
    -- the reference assumes it without proving it safe, so its safety checks
    -- are dropped rather than required. Anything else unmodelled declines.
    keptStep (MData "ExecutionStep::Havoc" _) = True
    keptStep (MData "ExecutionStep::Assume" _) = True
    keptStep value = totalStep value
    droppable value = keptStep value || case value of
        MData "ExecutionStep::Check" _ -> True
        _ -> False
    -- A clause that calls a program function: what the call needs (the
    -- callee's requires) is an obligation wherever the clause is used,
    -- assumed or checked, so the checks the call produced are kept.
    callsFunction env proof = case proof of
        FApp (ATerm name) _ -> isCall name
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel _)) _)) [x, y] -> callsFunction env x || callsFunction env y
        FApp f args -> callsFunction env f || any (callsFunction env) args
        Forall _ _ body -> callsFunction env body
        _ -> False
      where
        isCall name = case Map.lookup name env of
            Just (M.Const (M.CFn _)) -> True
            _ -> case [key | (key, M.Const (M.CFn _)) <- Map.toList env, sourceSuffix key == name] of
                [_] -> True
                _ -> False
        sourceSuffix key = case break (== ':') (reverse key) of
            (revSuffix, ':' : ':' : _) -> reverse revSuffix
            _ -> key

-- A rewrite rule: its parameters, input clauses, output clauses, and (for a
-- proof, not an axiom) the body that is checked once, generically.
type Rule = ([Variable], [ValidationStatement], [ValidationStatement], Maybe [ValidationStatement])

type Rules = Map.Map Variable Rule

collectRules :: M.Program -> Maybe Rules
collectRules program
    | length names /= length (nub names) = Nothing
    | otherwise = Just (Map.union programRules stdRules)
  where
    fns = M.progMain program : Map.elems (M.progFunctions program)
    found = [(name, rule) | fn <- fns, blk <- Map.elems (M.fnBlocks fn), stmt <- M.blockStatements blk, (name, rule) <- ruleOf stmt]
    names = map fst found
    programRules = Map.fromList found
    ruleOf (M.Ghost _ (M.GhostProof name args ins outs body)) = [(name, (args, ins, outs, Just body))]
    ruleOf (M.Ghost _ (M.GhostAxiom name args ins outs)) = [(name, (args, ins, outs, Nothing))]
    ruleOf _ = []
    stdRules = Map.fromList [(name, (args, ins, outs, Nothing)) | (name, AxiomRule args ins outs) <- Map.toList stdLibRuleCtx]

substituteProof :: Map.Map Variable VariableProof -> VariableProof -> VariableProof
substituteProof definitions proof = case proof of
    ATerm name -> Map.findWithDefault proof name definitions
    FApp function arguments -> FApp (substituteProof definitions function) (map (substituteProof definitions) arguments)
    Forall index guards body ->
        let scoped = Map.delete index definitions
         in Forall index (map (substituteProof scoped) guards) (substituteProof scoped body)
    _ -> proof

-- Definitions in a clause list, expanded in order against the bindings in
-- scope at their definition point (the semantics Ghost.defineProofRule gives
-- exported facts, expressed as translation).
buildSubst :: Map.Map Variable VariableProof -> [ValidationStatement] -> Map.Map Variable VariableProof
buildSubst bindings clauses = foldl add bindings [(var, expr) | AssignProofVar var expr <- clauses]
  where
    add m (var, expr) = Map.insert var (substituteProof m (exprToProof expr)) m

instantiate :: Map.Map Variable VariableProof -> [ValidationStatement] -> Maybe [ValidationStatement]
instantiate subst = fmap concat . traverse clause
  where
    clause (ProofAssert proof) = Just [ProofAssert (substituteProof subst proof)]
    clause (AssignProofVar _ _) = Just []
    clause (Assume proof) = Just [ProofAssert (substituteProof subst proof)]
    clause (Rewrite (CheckGtZero proof)) = Just [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [substituteProof subst proof, CTerm (VInt 0)])]
    clause (Rewrite (CheckRel proof)) = Just [ProofAssert (substituteProof subst proof)]
    clause (Rewrite _) = Nothing

substituteRule :: Map.Map Variable VariableProof -> RwRule -> RwRule
substituteRule subst (UserRewrite name args) = UserRewrite name (map (substituteProof subst) args)
substituteRule subst (Refl proof) = Refl (substituteProof subst proof)
substituteRule subst (CheckGtZero proof) = CheckGtZero (substituteProof subst proof)
substituteRule subst (CheckRel proof) = CheckRel (substituteProof subst proof)
substituteRule _ rule = rule

rewriteSteps :: Rules -> M.Env -> RwRule -> Build -> Maybe ([MirValue], Build)
rewriteSteps rules env (UserRewrite name args) b0 = do
    (params, ins, outs, _) <- Map.lookup name rules
    if length params == length args then Just () else Nothing
    let substIn = buildSubst (Map.fromList (zip params args)) ins
    inClauses <- instantiate substIn ins
    (checks, b1) <- contractSteps rules False env inClauses b0
    let substOut = buildSubst substIn outs
    outClauses <- instantiate substOut outs
    (assumptions, b2) <- contractSteps rules True env outClauses b1
    pure (checks ++ assumptions, b2)
rewriteSteps _ env (Refl proof) b0 = do
    (prefix, checked, b1) <- proofCheck env (FApp eqVarProof [proof, proof]) b0
    assumed <- case checked of
        MData "ExecutionStep::Check" fields -> Just (MData "ExecutionStep::Assume" fields)
        _ -> Nothing
    pure (prefix ++ [checked, assumed], b1)
rewriteSteps _ env (CheckGtZero proof) b0 = do
    (prefix, checked, b1) <- proofCheck env (FApp (CTerm (builtinFunct (Rel Gt))) [proof, CTerm (VInt 0)]) b0
    pure (prefix ++ [checked], b1)
rewriteSteps _ env (CheckRel proof) b0 = do
    (prefix, checked, b1) <- proofCheck env proof b0
    pure (prefix ++ [checked], b1)
rewriteSteps _ _ _ _ = Nothing

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

-- The operations on addresses and permissions (POINTERS.md), and on
-- Uninit: what they need and what they promise is what the standard
-- library's builtin says of them (StdLib), with the permission's ghost
-- arrays read as the lists the proofs read them as.
pointerSpec :: M.ListOp -> Maybe ([Variable], [ValidationStatement], [ValidationStatement])
pointerSpec op = do
    funct <- case op of
        M.AddrNull -> Just AddrNull
        M.AddrOffset -> Just AddrOffset
        M.AddrCast -> Just AddrCast
        M.AddrToInt -> Just AddrToInt
        M.AddrFromInt -> Just AddrFromInt
        M.AddrAlloc -> Just AddrAlloc
        M.AddrGet -> Just AddrGet
        M.AddrWrite -> Just AddrWrite
        M.AddrTake -> Just AddrTake
        M.AddrDropValue -> Just AddrDropValue
        M.AddrDropRange -> Just AddrDropRange
        M.AddrResize -> Just AddrResize
        M.AddrFree -> Just AddrFree
        M.BlockNew -> Just BlockNew
        M.BlockTaken -> Just BlockTaken
        M.BlockResized -> Just BlockResized
        M.BlockSplitLo -> Just BlockSplitLo
        M.BlockSplitHi -> Just BlockSplitHi
        M.BlockJoin -> Just BlockJoin
        M.BlockAssume -> Just BlockAssume
        M.BlockCast -> Just BlockCast
        M.UninitEmpty -> Just UninitEmpty
        M.UninitNew -> Just UninitNew
        M.UninitGet -> Just UninitGet
        M.UninitTake -> Just UninitTake
        M.UninitDiscard -> Just UninitDiscard
        _ -> Nothing
    builtinSpecOf funct

-- The name of an operation on a permission, shared by the statement
-- that runs it and a proof that names its result.
ghostOpShort :: M.ListOp -> String
ghostOpShort op = case op of
    M.AddrNull -> "addrnull"
    M.AddrOffset -> "addroffset"
    M.AddrCast -> "addrcast"
    M.AddrToInt -> "addrtoint"
    M.AddrFromInt -> "addrfromint"
    M.AddrAlloc -> "addralloc"
    M.AddrGet -> "addrget"
    M.AddrWrite -> "addrwrite"
    M.AddrTake -> "addrtake"
    M.AddrDropValue -> "addrdropvalue"
    M.AddrDropRange -> "addrdroprange"
    M.AddrResize -> "addrresize"
    M.AddrFree -> "addrfree"
    M.BlockNew -> "blocknew"
    M.BlockTaken -> "blocktaken"
    M.BlockResized -> "blockresized"
    M.BlockSplitLo -> "blocksplitlo"
    M.BlockSplitHi -> "blocksplithi"
    M.BlockJoin -> "blockjoin"
    M.BlockAssume -> "blockassume"
    M.BlockCast -> "blockcast"
    M.UninitEmpty -> "uninitempty"
    M.UninitNew -> "uninitnew"
    M.UninitGet -> "uninitget"
    M.UninitTake -> "uninittake"
    M.UninitDiscard -> "uninitdiscard"
    _ -> "op"

builtinSpecOf :: BuiltinFunct -> Maybe ([Variable], [ValidationStatement], [ValidationStatement])
builtinSpecOf funct = case builtinFunct funct of
    VFunct params ins outs _ extra -> Just (params, ins, outs ++ map ProofAssert extra)
    _ -> Nothing

statement :: Rules -> M.Statement -> Build -> Maybe ([MirValue], Build)
statement _ (M.Assign (M.Local dest) (M.Use (M.Const (M.CFn _)))) b =
    Just ([step "Havoc" [("local", MInt (toInteger dest))]], b)
statement rules (M.Assign (M.Local dest) (M.Use source)) b = do
    (v, b') <- operand source b
    pure ([step "Assign" [("local", MInt (toInteger dest)), ("value", v)]], b')
-- Boxes and unsizing preserve the proof value, as in the reference MIR
-- validator. Ownership and representation are handled by later passes.
statement rules (M.Assign dest (M.MakeBox source)) b = statement rules (M.Assign dest (M.Use source)) b
statement rules (M.Assign dest (M.Unbox source)) b = statement rules (M.Assign dest (M.Use source)) b
statement rules (M.Assign dest (M.Unsize source)) b = statement rules (M.Assign dest (M.Use source)) b
statement rules (M.Assign dest (M.Clone source)) b = statement rules (M.Assign dest (M.Use source)) b
-- A reference to a whole local has the value of what it is to, as in the reference MIR validator; a reference
-- to a part of one, a read through one and an assignment through one are outside this bridge's subset for now
statement rules (M.Assign dest (M.Borrow root [] _)) b = statement rules (M.Assign dest (M.Use (M.Copy root))) b
statement rules (M.Assign dest (M.Deref source)) b = statement rules (M.Assign dest (M.Use source)) b
statement rules (M.Assign (M.Local dest) (M.MakeData name fields)) b0 = do
    (snapshots, b1) <- foldM snapshot ([], b0) fields
    let (constructor, b2) = namedFunction ("ctor:" ++ name) b1
        destination = record "ValueRef::Local" [("local", MInt (toInteger dest))]
        create = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt constructor), ("arguments", MList [ref | (_, ref, _) <- snapshots])]
    (projections, b3) <- foldM (project destination) ([], b2) snapshots
    let b4 = b3{ctorFields = nub ([(constructor, fieldId, toInteger index) | (index, (field, _, _)) <- zip [0 ..] snapshots, let (fieldId, _) = namedFunction ("field:" ++ field) b3] ++ ctorFields b3)}
        (variantStep, b5) = case break (== ':') name of
            (family, ':' : ':' : _) ->
                let (familyId, b') = namedFunction ("enum:" ++ family) b4
                    (constructorId, b'') = namedFunction ("variant:" ++ name) b'
                 in ([step "AssumeVariant" [("object", destination), ("family", MInt familyId), ("constructor", MInt constructorId), ("matches", MBool True)]], b'')
            _ -> ([], b4)
    pure ([saved | (_, _, saved) <- snapshots] ++ [create] ++ variantStep ++ projections, b5)
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
statement rules (M.Assign (M.Local dest) (M.ReadField source _ field)) b0 = do
    (value, b1) <- operand source b0
    let (function, b2) = namedFunction ("field:" ++ field) b1
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList [value])]], b2)
statement rules (M.Assign (M.Local dest) (M.IsVariant source variantName)) b0 = do
    (value, b1) <- operand source b0
    let (predicate, b2) = namedFunction ("isvariant:" ++ variantName) b1
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt predicate), ("arguments", MList [value])]], b2)
statement rules (M.Assign (M.Local dest) (M.AsVariant source variantName)) b0 = do
    (value, b1) <- operand source b0
    let assign = step "Assign" [("local", MInt (toInteger dest)), ("value", value)]
        (familyId, b2) = namedFunction ("enum:" ++ takeWhile (/= ':') variantName) b1
        (constructorId, b3) = namedFunction ("variant:" ++ variantName) b2
        require = step "RequireVariant" [("object", record "ValueRef::Local" [("local", MInt (toInteger dest))]), ("family", MInt familyId), ("constructor", MInt constructorId)]
    pure ([assign, require], b3)
statement rules (M.Assign (M.Local dest) (M.ListOp M.Length [source])) b = do
    (value, b') <- operand source b
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (-13)), ("arguments", MList [value])]], b')
statement rules (M.Assign (M.Local dest) (M.ListOp M.Get [source, index])) b0 = do
    (listRef, b1) <- operand source b0
    (indexRef, b2) <- operand index b1
    getSteps (toInteger dest) listRef indexRef b2
statement rules (M.Assign (M.Local dest) (M.ListOp M.Push [source, value])) b0 = do
    (listRef, b1) <- operand source b0
    (valueRef, b2) <- operand value b1
    pushSteps (toInteger dest) listRef valueRef b2
statement rules (M.Assign (M.Local dest) (M.ListOp M.Pop [source])) b0 = do
    (listRef, b1) <- operand source b0
    popSteps (toInteger dest) listRef b1
statement rules (M.Assign (M.Local dest) (M.ListOp operation [lengthValue, value])) b0
    | operation == M.NewArray || operation == M.NewBoxed = do
        (lengthRef, b1) <- operand lengthValue b0
        (valueRef, b2) <- operand value b1
        arraySteps (toInteger dest) lengthRef valueRef b2
statement rules (M.Assign (M.Local dest) (M.ListOp M.NewEmptyBoxed [])) b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    let (i, b2) = fresh b1
        sizeLocal = negate i - 1
        resultRef = record "ValueRef::Local" [("local", MInt (toInteger dest))]
        sizeRef = record "ValueRef::Local" [("local", MInt sizeLocal)]
        make = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (-15)), ("arguments", MList [])]
        size = step "ApplyFresh" [("local", MInt sizeLocal), ("function", MInt (-13)), ("arguments", MList [resultRef])]
        known = step "Assume" [("relation", MInt 0), ("left", sizeRef), ("right", zero)]
    pure ([make, size, known], b2)
statement rules (M.Assign (M.Local dest) (M.ListOp M.Set [source, index, value])) b0 = do
    (listRef, b1) <- operand source b0
    (indexRef, b2) <- operand index b1
    (valueRef, b3) <- operand value b2
    setSteps (toInteger dest) listRef indexRef valueRef b3
statement rules (M.Assign (M.Local dest) (M.ListOp M.ReadByte [])) b0 = do
    let (function, b1) = namedFunction "readByte" b0
    (minusOne, b2) <- operand (M.Const (M.CInt (-1))) b1
    (limit, b3) <- operand (M.Const (M.CInt 256)) b2
    let ref = record "ValueRef::Local" [("local", MInt (toInteger dest))]
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList [])], step "Assume" [("relation", MInt 3), ("left", minusOne), ("right", ref)], step "Assume" [("relation", MInt 2), ("left", ref), ("right", limit)]], b3)
statement rules (M.Assign (M.Local dest) (M.ListOp M.ToByte [source])) b0 = do
    (value, b1) <- operand source b0
    (zero, b2) <- operand (M.Const (M.CInt 0)) b1
    (limit, b3) <- operand (M.Const (M.CInt 256)) b2
    pure ([check 3 zero value, check 2 value limit, step "Assign" [("local", MInt (toInteger dest)), ("value", value)]], b3)
statement rules (M.Assign (M.Local dest) (M.ListOp M.FromByte [source])) b = do
    (value, b') <- operand source b
    pure ([step "Assign" [("local", MInt (toInteger dest)), ("value", value)]], b')
statement rules (M.Assign (M.Local dest) (M.ListOp op [source])) b
    | op `elem` [M.WriteByte, M.WriteError, M.PathByte, M.StoreByte] = do
    (value, b') <- operand source b
    let ref = record "ValueRef::Local" [("local", MInt (toInteger dest))]
        isWrite = op == M.WriteByte || op == M.WriteError
    pure
        ( [ if isWrite then step "Assign" [("local", MInt (toInteger dest)), ("value", value)] else step "Havoc" [("local", MInt (toInteger dest))]
          , step "Assume" [("relation", MInt 3), ("left", value), ("right", ref)]
          , step "Assume" [("relation", MInt 3), ("left", ref), ("right", value)]
          ]
        , b'
        )
statement rules (M.Assign (M.Local dest) (M.ListOp op [])) b0
    | op `elem` [M.ArgCount, M.FileLoad] = do
        let (function, b1) = namedFunction (case op of M.ArgCount -> "argCount"; _ -> "fileLoad") b0
        (minusOne, b2) <- operand (M.Const (M.CInt (-1))) b1
        (zero, b3) <- operand (M.Const (M.CInt 0)) b2
        let ref = record "ValueRef::Local" [("local", MInt (toInteger dest))]
            bound = if op == M.ArgCount then zero else minusOne
        pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList [])], step "Assume" [("relation", MInt 3), ("left", bound), ("right", ref)]], b3)
statement rules (M.Assign (M.Local dest) (M.ListOp op args)) b
    | op `elem` [M.ArgByte, M.PathByte, M.FileByte, M.StoreByte] = do
        let name = case op of M.ArgByte -> "argByte"; M.PathByte -> "pathByte"; M.FileByte -> "fileByte"; _ -> "storeByte"
            (function, b1) = namedFunction name b
        (refs, b2) <- foldM (\(rs, bb) a -> do (r, bb') <- operand a bb; pure (rs ++ [r], bb')) ([], b1) args
        (low, b3) <- operand (M.Const (M.CInt (if op == M.ArgByte || op == M.FileByte then -1 else 0))) b2
        (high, b4) <- operand (M.Const (M.CInt 256)) b3
        (zero, b5) <- operand (M.Const (M.CInt 0)) b4
        let ref = record "ValueRef::Local" [("local", MInt (toInteger dest))]
            bounds = case op of
                M.ArgByte -> [step "Assume" [("relation", MInt 3), ("left", low), ("right", ref)], step "Assume" [("relation", MInt 2), ("left", ref), ("right", high)]]
                M.FileByte -> [step "Assume" [("relation", MInt 3), ("left", low), ("right", ref)], step "Assume" [("relation", MInt 2), ("left", ref), ("right", high)]]
                _ -> [step "Assume" [("relation", MInt 3), ("left", zero), ("right", ref)]]
        pure (step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList refs)] : bounds, b5)
statement rules (M.Assign (M.Local dest) (M.ListOp op args)) b0
    | Just (params, ins, outs) <- pointerSpec op = do
        if length params == length args then Just () else Nothing
        -- The arguments are read as they are, into terms of their own,
        -- before the result is the local's value: one local can be both
        -- an argument and the result (b = Addr::write(p, i, x, b)), and
        -- what the operation needs and promises is read of each in its
        -- own time.
        (snapshots, snapped, b1) <- foldM snapshot ([], [], b0) args
        let env = Map.fromList (zip params snapped ++ [("return", M.Copy (M.Local dest))])
            (function, b2) = namedFunction ("ghostop:" ++ ghostOpShort op) b1
        (argRefs, b3) <- foldM (\(rs, bb) a -> do (r, bb') <- operand a bb; pure (rs ++ [r], bb')) ([], b2) snapped
        -- An operation that makes a new address or permission is not a
        -- function of its arguments: doing it twice makes two things, so
        -- its application carries a tag no other application has.
        (argRefs, b3) <- if op `elem` [M.AddrAlloc, M.BlockNew, M.UninitNew, M.UninitEmpty]
            then do
                let (tag, bx) = fresh b3
                (tagRef, bx') <- operand (M.Const (M.CInt tag)) bx
                pure (argRefs ++ [tagRef], bx')
            else pure (argRefs, b3)
        (required, b4) <- contractSteps rules False env ins b3
        (promised, b5) <- contractSteps rules True env outs b4
        (framed, b6) <- frameSteps op snapped (toInteger dest) b5
        pure (snapshots ++ required ++ [step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList argRefs)]] ++ promised ++ framed, b6)
  where
    -- A slot written (or emptied) is a set on the permission's ghost
    -- arrays, so what the checker knows of a set is known of the block
    -- after: every other slot as it was, without a forall said again.
    snapshot (steps, ops, b) arg = do
        (ref, b1) <- operand arg b
        let (i, b2) = fresh b1
            local = M.Local (negate (fromInteger i) - 1)
        pure (steps ++ [step "Assign" [("local", MInt (toInteger (localNum local))), ("value", ref)]], ops ++ [M.Copy local], b2)
    frameSteps operation operands dest bIn = case (operation, operands) of
        (M.AddrWrite, [_, indexOp, valueOp, blockOp]) -> written dest blockOp indexOp (Just valueOp) True bIn
        (M.AddrDropValue, [_, indexOp, blockOp]) -> written dest blockOp indexOp Nothing False bIn
        _ -> pure ([], bIn)
    written dest blockOp indexOp valueOp filled bIn = do
        (blockRef, b1) <- operand blockOp bIn
        (indexRef, b2) <- operand indexOp b1
        (destRef, b3) <- operand (M.Copy (M.Local (fromInteger dest))) b2
        (f1, srcFilled, b4) <- ghostApp "blockfilled" blockRef b3
        (f2, dstFilled, b5) <- ghostApp "blockfilled" destRef b4
        (flagRef, b6) <- operand (M.Const (M.CBool filled)) b5
        (f3, setFilled, b7) <- setResult srcFilled indexRef flagRef b6
        (rest, b8) <- case valueOp of
            Just vOp -> do
                (valueRef, c1) <- operand vOp b7
                (g1, srcContents, c2) <- ghostApp "blockcontents" blockRef c1
                (g2, dstContents, c3) <- ghostApp "blockcontents" destRef c2
                (g3, setContents, c4) <- setResult srcContents indexRef valueRef c3
                pure (g1 ++ g2 ++ g3 ++ [assumeEq dstContents setContents], c4)
            Nothing -> pure ([], b7)
        pure (f1 ++ f2 ++ f3 ++ [assumeEq dstFilled setFilled] ++ rest, b8)
    ghostApp name argRef bIn =
        let (function, b1) = namedFunction name bIn
            (i, b2) = fresh b1
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
         in pure ([step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [argRef])]], ref, b2)
    setResult listRef indexRef valueRef bIn =
        let (i, b1) = fresh bIn
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
         in pure ([step "ApplyFresh" [("local", MInt local), ("function", MInt (-17)), ("arguments", MList [listRef, indexRef, valueRef])]], ref, b1)
    assumeEq a b = step "Assume" [("relation", MInt 0), ("left", a), ("right", b)]
statement rules (M.Assign (M.Local dest) (M.ListOp M.FileStore [])) b0 = do
    let (function, b1) = namedFunction "fileStore" b0
    (minusOne, b2) <- operand (M.Const (M.CInt (-1))) b1
    (zero, b3) <- operand (M.Const (M.CInt 0)) b2
    let ref = record "ValueRef::Local" [("local", MInt (toInteger dest))]
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList [])], step "Assume" [("relation", MInt 3), ("left", minusOne), ("right", ref)], step "Assume" [("relation", MInt 3), ("left", ref), ("right", zero)]], b3)
statement rules (M.Assign (M.Local dest) (M.ListOp operation [source])) b0
    | operation == M.First || operation == M.Last = do
        (listRef, b1) <- operand source b0
        if operation == M.First then do
            (zero, b2) <- operand (M.Const (M.CInt 0)) b1
            getSteps (toInteger dest) listRef zero b2
          else lastSteps (toInteger dest) listRef b1
statement rules (M.Assign (M.Local dest) (M.BinaryOp op a b)) b0 = do
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
statement rules (M.Ghost env (M.GhostValidation (ProofAssert proof))) b = do
    (prefix, s, b') <- proofCheck env proof b
    pure (prefix ++ [s], b')
statement rules (M.Ghost env (M.GhostValidation (Rewrite rule))) b = rewriteSteps rules env rule b
statement rules (M.Ghost env (M.GhostValidation (Assume proof))) b = contractSteps rules True env [ProofAssert proof] b
-- Definitions are skipped where they stand: a proof rule is checked once,
-- generically (encodeRule), and an axiom is taken on trust.
statement _ (M.Ghost _ (M.GhostProof _ _ _ _ _)) b = Just ([], b)
statement _ (M.Ghost _ (M.GhostAxiom _ _ _ _)) b = Just ([], b)
-- Function bodies are checked independently before the main graph. Function
-- definitions have already been checked for uniqueness and placement.
statement _ (M.Ghost _ M.GhostFunction{}) b = Just ([], b)
-- Taking a value apart uses it up; its fields keep the values (the
-- reads of them are the statements of their own).
statement _ (M.Ghost _ (M.GhostDissolve _)) b = Just ([], b)
statement _ (M.Ghost _ (M.GhostPosition _ _)) b = Just ([], b)
statement _ _ _ = Nothing



proofNames :: VariableProof -> [Variable]
proofNames (ATerm name) = [name]
proofNames (BVar _) = []
proofNames (CTerm _) = []
proofNames (FApp f args) = proofNames f ++ concatMap proofNames args
proofNames (Forall index guards body) = filter (/= index) (concatMap proofNames guards ++ proofNames body)

-- The top-level program and a function declared ~ may use code that is not
-- guaranteed to end; other functions may not.
mayDivergeFn :: M.Function -> Bool
mayDivergeFn fn = M.fnName fn == "main" || M.specTermination (M.fnSpec fn) == Just MayDiverge

-- A call through a local that holds a builtin (h = size; h(xs)): the pure
-- sequence operations have no contract to check, only safety conditions.
stripBuiltin :: Name -> Name
stripBuiltin name
    | "builtin::" `isPrefixOf` name = drop 9 name
    | otherwise = name

builtinCall :: Name -> [M.Operand] -> M.Local -> Build -> Maybe ([MirValue], Build)
builtinCall name args (M.Local dest) b0 = case (name, args) of
    ("size", [source]) -> do
        (value, b1) <- operand source b0
        pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (-13)), ("arguments", MList [value])]], b1)
    ("get", [source, index]) -> do
        (listRef, b1) <- operand source b0
        (indexRef, b2) <- operand index b1
        getSteps (toInteger dest) listRef indexRef b2
    ("push", [source, value]) -> do
        (listRef, b1) <- operand source b0
        (valueRef, b2) <- operand value b1
        pushSteps (toInteger dest) listRef valueRef b2
    ("set", [source, index, value]) -> do
        (listRef, b1) <- operand source b0
        (indexRef, b2) <- operand index b1
        (valueRef, b3) <- operand value b2
        setSteps (toInteger dest) listRef indexRef valueRef b3
    ("pop", [source]) -> do
        (listRef, b1) <- operand source b0
        popSteps (toInteger dest) listRef b1
    ("last", [source]) -> do
        (listRef, b1) <- operand source b0
        lastSteps (toInteger dest) listRef b1
    ("first", [source]) -> do
        (listRef, b1) <- operand source b0
        (zero, b2) <- operand (M.Const (M.CInt 0)) b1
        getSteps (toInteger dest) listRef zero b2
    _ -> Nothing

-- A direct call uses only contracts of bodies checked separately. Snapshot
-- arguments before writing the result, and decline callees that reassign a
-- parameter: their postconditions can refer to its final value.
directCall :: Rules -> M.Function -> M.Function -> [M.Operand] -> M.Local -> Maybe (Bool, MirValue) -> Bool -> Build -> Maybe ([MirValue], [(Name, MirValue)], Build)
directCall rules caller callee args (M.Local dest) termInfo recursiveCall b0 = do
    if length args == length params then Just () else Nothing
    if all validSizeArg (drop (length args - length (M.fnSizeParams callee)) args) then Just () else Nothing
    let calleeStmts = concatMap M.blockStatements (Map.elems (M.fnBlocks callee))
        calleeTerms = map M.blockTerminator (Map.elems (M.fnBlocks callee))
        reassignedNames = [name | local <- params, any (writesLocal local) calleeStmts || any (callWrites local) calleeTerms, Just name <- [M.localName =<< Map.lookup local (M.fnLocals callee)]]
        ensuredNames = concat [proofNames proof | ProofAssert proof <- M.specEnsures (M.fnSpec callee)]
    if any (\name -> name `elem` reassignedNames && name `notElem` M.specMutParams (M.fnSpec callee)) ensuredNames then Nothing else Just ()
    case M.specFrom (M.fnSpec callee) of
        [] -> Just ()
        [from] -> if from `elem` map fst paramNameLocals then Just () else Nothing
        _ -> Nothing
    case M.fnReturns callee of Just _ -> Just (); Nothing -> Nothing
    (snapshots, b1) <- foldM snapshot ([], b0) args
    (postSteps, postLocals, b1') <- foldM (addPost snapshots) ([], [], b1) (zip params args)
    let bindings = Map.fromList (zip params [local | (local, _) <- snapshots])
        remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
        remap constant@(M.Const _) = Just constant
        remap _ = Nothing
        env = Map.mapMaybe remap (M.specEnv (M.fnSpec callee))
    (sizeChecks, withSizes) <- sizeParameterSteps False callee (map fst snapshots) b1'
    (checks, b2) <- contractSteps rules False env (M.specRequires (M.fnSpec callee)) withSizes
    (variantSteps, b2') <- case (termInfo, recursiveCall, M.specTermination (M.fnSpec callee)) of
        (Just (isParts, callerRef), True, Just term) -> do
            expr <- case term of
                Counting e -> Just e
                Parts e -> Just e
                _ -> Nothing
            (steps, callRef, b') <- exprOperand env expr b2
            let chk = if isParts then step "CheckWithin" [("inner", callRef), ("outer", callerRef)] else check 2 callRef callerRef
            pure (steps ++ [chk], b')
        (_, True, Nothing) -> impossible b2
        (_, _, Just MayDiverge) | not (mayDivergeFn caller) -> impossible b2
        _ -> pure ([], b2)
    let postEnv = foldl (\e (name, postLocal, snapLocal) -> Map.insert name (M.Copy postLocal) (Map.insert ("$old " ++ name) (M.Copy snapLocal) e)) env [(name, post, snap) | (name, post, snap) <- postLocals]
        resultEnv = Map.insert "return" (M.Copy (M.Local dest)) postEnv
    (assumptions, b3) <- contractSteps rules True resultEnv (M.specEnsures (M.fnSpec callee)) b2'
    let (function, b4) = namedFunction ("call:" ++ M.fnName callee) b3
        argumentRefs = [record "ValueRef::Local" [("local", MInt (toInteger n))] | (M.Local n, _) <- snapshots]
        applyResult = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList argumentRefs)]
        result = case M.specFrom (M.fnSpec callee) of
            [from] | Just (_, postLocal, _snapLocal) <- find (\(name, _, _) -> name == from) postLocals -> step "Assign" [("local", MInt (toInteger dest)), ("value", record "ValueRef::Local" [("local", MInt (toInteger (localNum postLocal)))])]
            [from] | Just snapLocal <- lookup from (zip (map fst paramNameLocals) [local | (local, _) <- snapshots]) -> step "Assign" [("local", MInt (toInteger dest)), ("value", record "ValueRef::Local" [("local", MInt (toInteger (localNum snapLocal)))])]
            _ -> applyResult
    pure ([save | (_, save) <- snapshots] ++ postSteps ++ sizeChecks ++ checks ++ variantSteps ++ [result] ++ assumptions, [(name, record "ValueRef::Local" [("local", MInt (toInteger (localNum post)))]) | (name, post, _) <- postLocals], b4)
  where
    paramNameLocals = [(n, p) | p <- params, Just d <- [Map.lookup p (M.fnLocals callee)], Just n <- [M.localName d]]
    addPost snaps (steps, posts, b) (param, _) = case [name | (name, p) <- paramNameLocals, p == param] of
        [name] | name `elem` M.specMutParams (M.fnSpec callee) -> do
            let (i, b') = fresh b
                postLocal = M.Local (negate (fromInteger i) - 1)
                snapLocal = case lookup param (zip params [local | (local, _) <- snaps]) of Just l -> l; Nothing -> param
            pure (steps ++ [step "Havoc" [("local", MInt (toInteger (localNum postLocal)))]], posts ++ [(name, postLocal, snapLocal)], b')
        _ -> pure (steps, posts, b)
    -- A check no consistent context can prove (it still passes in a
    -- contradictory, unreachable one, as the reference treats such code).
    impossible b = do
        (zero, b') <- operand (M.Const (M.CInt 0)) b
        pure ([check 2 zero zero], b')
    params = M.fnParams callee
    callerSizeParams = drop (length (M.fnParams caller) - length (M.fnSizeParams caller)) (M.fnParams caller)
    validSizeArg (M.Const (M.CInt _)) = True
    validSizeArg (M.Copy local) = local `elem` callerSizeParams
    validSizeArg _ = False
    writesLocal wanted (M.Assign local _) = local == wanted
    writesLocal wanted (M.Peek local _) = local == wanted
    writesLocal wanted (M.Drop local) = local == wanted
    writesLocal _ _ = False
    callWrites wanted (M.Call _ _ local _) = local == wanted
    callWrites _ _ = False
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
typeSteps :: Rules -> Map.Map Name M.TypeDecl -> Map.Map Name [ValidationStatement] -> M.Function -> M.Local -> Build -> Maybe ([MirValue], Build)
typeSteps rules types invariants fn local@(M.Local number) b0 = do
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
        case Map.lookup name types <|> Map.lookup base types of
            Just (M.StructDecl fs) -> do
                let fields = map fst fs
                (projections, env, b1) <- foldM project ([], Map.empty, b) fields
                let (constructor, b2) = namedFunction ("ctor:" ++ name) b1
                    (i, b3) = fresh b2
                    clocal = negate i - 1
                    cref = record "ValueRef::Local" [("local", MInt clocal)]
                    argRefs = [record "ValueRef::Local" [("local", MInt (localNum l))] | f <- fields, Just (M.Copy l) <- [Map.lookup f env]]
                    create = step "ApplyFresh" [("local", MInt clocal), ("function", MInt constructor), ("arguments", MList argRefs)]
                    known = assume 0 value cref
                    (fieldIds, b4) = foldl (\(ids, bb) f -> let (fid, bb') = namedFunction ("field:" ++ f) bb in (ids ++ [fid], bb')) ([], b3) fields
                    b5 = b4{ctorFields = nub ([(constructor, fid, toInteger idx) | (idx, fid) <- zip [0 ..] fieldIds] ++ ctorFields b4)}
                (assumptions, b6) <- if null clauses then pure ([], b5) else contractSteps rules True env clauses b5
                pure (projections ++ [create, known] ++ assumptions, b6)
            _ -> if null clauses then Just ([], b) else do
                fields <- case Map.lookup name types <|> Map.lookup base types of Just (M.StructDecl fs) -> Just (map fst fs); _ -> Nothing
                (projections, env, b1) <- foldM project ([], Map.empty, b) fields
                (assumptions, b2) <- contractSteps rules True env clauses b1
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

-- Evaluate a pure expression (as inferred loop bounds are written) into
-- steps and a reference, mirroring proofOperand for proof terms.
exprOperand :: M.Env -> Expression -> Build -> Maybe ([MirValue], MirValue, Build)
exprOperand env expr b0 = case expr of
    Var name -> do
        o <- Map.lookup name env
        (v, b1) <- operand o b0
        pure ([], v, b1)
    Val (VInt value) -> do
        (v, b1) <- operand (M.Const (M.CInt value)) b0
        pure ([], v, b1)
    Val (VBool value) -> do
        (v, b1) <- operand (M.Const (M.CBool value)) b0
        pure ([], v, b1)
    F (Var "size") [arg] -> apply1 "size" (-13) arg
    F (Val (VFunct _ _ _ (BuiltinFunct Size) _)) [arg] -> apply1 "size" (-13) arg
    -- A trait method in a loop bound or variant (size of a Vec, say) is a
    -- call of the impl's function, as it is in a proof.
    F (Var name) args
        | Just (M.Const (M.CFn callee)) <- Map.lookup name env -> do
            (prefixes, refs, b1) <- foldM evalArg ([], [], b0) args
            let (function, b2) = namedFunction ("call:" ++ callee) b1
                (i, b3) = fresh b2
                local = negate i - 1
                ref = record "ValueRef::Local" [("local", MInt local)]
                apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList refs)]
            (facts, b4) <- proofCallFacts callee refs local b3
            pure (prefixes ++ [apply] ++ facts, ref, b4)
      where
        evalArg (steps, refs, b) arg = do
            (more, ref, b') <- exprOperand env arg b
            pure (steps ++ more, refs ++ [ref], b')
    F (Val (VFunct _ _ _ (BuiltinFunct (Field _ field)) _)) [arg] -> do
        (steps, value, b1) <- exprOperand env arg b0
        let (function, b2) = namedFunction ("field:" ++ field) b1
            (i, b3) = fresh b2
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [value])]
        pure (steps ++ [apply], ref, b3)
    F (Val (VFunct _ _ _ (BuiltinFunct f) _)) [a, b] -> do
        op <- case f of
            Plus -> Just M.Add
            Minus -> Just M.Sub
            Times -> Just M.Mul
            _ -> Nothing
        (leftSteps, x, b1) <- exprOperand env a b0
        (rightSteps, y, b2) <- exprOperand env b b1
        let (i, b3) = fresh b2
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (functionId op)), ("arguments", MList [x, y])]
        pure (leftSteps ++ rightSteps ++ [apply], ref, b3)
    _ -> Nothing
  where
    apply1 _ function arg = do
        (steps, value, b1) <- exprOperand env arg b0
        let (i, b2) = fresh b1
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [value])]
        pure (steps ++ [apply], ref, b2)


-- Locals that hold one known function: assigned exactly once in the whole
-- function, to a function constant or to another such local. A call through
-- one of these is a call to that function; anything else is not modelled.
fnValueLocals :: M.Function -> Map.Map M.Local Name
fnValueLocals f = Map.fromList [(d, n) | (d, _) <- fnAssignments, Just n <- [resolve Set.empty d]]
  where
    stmts = concatMap M.blockStatements (Map.elems (M.fnBlocks f))
    terms = map M.blockTerminator (Map.elems (M.fnBlocks f))
    fnAssignments = [(d, src) | M.Assign d (M.Use src) <- stmts, isFnSource src]
    isFnSource (M.Const (M.CFn _)) = True
    isFnSource (M.Copy _) = True
    isFnSource _ = False
    assignmentCount d = length [() | M.Assign d' _ <- stmts, d' == d] + length [() | M.Call _ _ d' _ <- terms, d' == d]
    resolve seen d
        | Set.member d seen = Nothing
        | assignmentCount d /= 1 = Nothing
        | otherwise = case [src | (d', src) <- fnAssignments, d' == d] of
            [M.Const (M.CFn n)] -> Just n
            [M.Copy src] -> resolve (Set.insert d seen) src
            _ -> Nothing

-- The place each reference local of a function is to, when the whole function
-- agrees on it: a borrow, a copy of a reference, or a call that returns a
-- reference from one of its arguments. A local that is lent two different
-- places is outside the bridge's subset.
borrowsOf :: Map.Map Name M.Function -> M.Function -> Maybe (Map.Map M.Local (M.Local, [M.RefStep]))
borrowsOf functions fn = loop Map.empty
  where
    stmts = concatMap M.blockStatements (Map.elems (M.fnBlocks fn))
    terms = map M.blockTerminator (Map.elems (M.fnBlocks fn))
    seeds = [(d, (root, steps)) | M.Assign d (M.Borrow root steps _) <- stmts]
    edges = [(d, src) | M.Assign d (M.Use (M.Copy src)) <- stmts] ++ [(d, src) | M.Assign d (M.Use (M.Move src)) <- stmts] ++ callEdges
    callEdges =
        [ (dest, src)
        | M.Call (M.Const (M.CFn name)) args dest _ <- terms
        , Just callee <- [Map.lookup name functions]
        , [from] <- [M.specFrom (M.fnSpec callee)]
        , Just idx <- [lookup from (zip (paramNamesOf callee) [0 ..])]
        , idx < length args
        , M.Copy src <- [args !! idx]
        ]
    paramNamesOf f = [n | p <- M.fnParams f, Just d <- [Map.lookup p (M.fnLocals f)], Just n <- [M.localName d]]
    loop known = case extend known of
        Nothing -> Nothing
        Just m -> if m == known then Just known else loop m
    extend known = do
        m1 <- foldM (\m (d, place) -> put m d place) known seeds
        foldM (\m (d, src) -> case Map.lookup src m of Just place -> put m d place; Nothing -> Just m) m1 edges
    put m d place = case Map.lookup d m of
        Nothing -> Just (Map.insert d place m)
        Just p -> if p == place then Just m else Nothing

-- The callees of a function, by name.
callNamesOf :: M.Function -> [Name]
callNamesOf f = [n | blk <- Map.elems (M.fnBlocks f), M.Call (M.Const (M.CFn n)) _ _ _ <- [M.blockTerminator blk]]

-- Whether starting from `from` a call chain reaches `target`, in the call
-- graph over the program's functions plus the caller itself.
reachesName :: Map.Map Name M.Function -> M.Function -> Name -> Name -> Bool
reachesName functions caller from target = go Set.empty [from]
  where
    allFns = Map.insert (M.fnName caller) caller functions
    go _ [] = False
    go seen (x : xs)
        | x == target = True
        | Set.member x seen = go seen xs
        | otherwise = go (Set.insert x seen) (maybe [] callNamesOf (Map.lookup x allFns) ++ xs)

block :: Map.Map Name M.TypeDecl -> Map.Map Name [ValidationStatement] -> Map.Map Name M.Function -> Rules -> Maybe (Bool, MirValue) -> Bool -> M.Function -> (M.BlockId, M.BasicBlock) -> Build -> Maybe (MirValue, Build)
block types invariants functions rules termInfo allowCalls fn (blockId@(M.BlockId n), M.BasicBlock stmts end) b0 = do
    (steps, b1, conditions, _) <- foldM add ([], b0, Map.empty, Map.empty) stmts
    (extra, ending, b2) <- case (Map.lookup blockId (M.specLoops (M.fnSpec fn)), end) of
        (Just spec, M.SwitchBool (M.Copy local) yes no) -> do
            resolution <- case Map.lookup local conditions of
                Just (r0, a0, c0) -> Just (r0, a0, c0, Nothing, b1)
                Nothing -> case variantTest fn local of
                    Just (source, variantName) -> do
                        (object, b2) <- operand source b1
                        let (familyId, b3) = namedFunction ("enum:" ++ takeWhile (/= ':') variantName) b2
                            (constructorId, b4) = namedFunction ("variant:" ++ variantName) b3
                        (trueRef, b5) <- operand (M.Const (M.CBool True)) b4
                        Just (Eq, localRef (localNumber local), trueRef, Just (object, familyId, constructorId), b5)
                    Nothing -> do
                        value <- constBoolTest fn local
                        (boolRef, b2) <- operand (M.Const (M.CBool value)) b1
                        Just (Eq, localRef (localNumber local), boolRef, Nothing, b2)
            (extra, loopEnd, b') <- encodeLoop spec yes no local resolution
            pure (extra, loopEnd, b')
        (Just spec, M.SwitchBool (M.Const (M.CBool value)) yes no) -> do
            (boolRef, b2) <- operand (M.Const (M.CBool value)) b1
            (extra, loopEnd, b') <- encodeLoop spec yes no (M.Local 0) (Eq, boolRef, boolRef, Nothing, b2)
            pure (extra, loopEnd, b')
        (Just spec, M.Call calleeOp args dest target) | allowCalls -> do
            next <- Map.lookup target (M.fnBlocks fn)
            (yes, no, compare) <- case (M.blockStatements next, M.blockTerminator next) of
                ([M.Assign condDest (M.BinaryOp (M.Compare r) a c)], M.SwitchBool (M.Copy condLocal) yes no)
                    | condDest == condLocal -> Just (yes, no, (r, a, c))
                _ -> Nothing
            name <- case calleeOp of
                M.Const (M.CFn n) -> Just n
                M.Copy local -> Map.lookup local (fnValueLocals fn)
                _ -> Nothing
            (callSteps, posts, b2) <- case Map.lookup name functions of
                Just callee -> directCall rules fn callee args dest termInfo (name == M.fnName fn || reachesName functions fn name (M.fnName fn)) b1
                _ -> do
                    (cs, bb) <- builtinCall (stripBuiltin name) args dest b1
                    pure (cs, [], bb)
            if null posts then Just () else Nothing
            (left, b3) <- operand (let (_, a, _) = compare in a) b2
            (right, b4) <- operand (let (_, _, c) = compare in c) b3
            let (r, _, _) = compare
            (loopExtra, loopEnd, b5) <- encodeLoop spec yes no (M.Local 0) (r, left, right, Nothing, b4)
            Just (callSteps ++ loopExtra, loopEnd, b5)
        (Just _, _) -> Nothing
        (Nothing, M.Return) -> do
            let env = Map.insert "return" (M.Copy (M.Local 0)) (foldl (\e (name, local) -> Map.insert ("$old " ++ name) (M.Copy (M.Local (-(1000000 + fromInteger (localNum local))))) e) (M.specEnv (M.fnSpec fn)) [(name, p) | p <- M.fnParams fn, Just d <- [Map.lookup p (M.fnLocals fn)], Just name <- [M.localName d], name `elem` M.specMutParams (M.fnSpec fn)])
            (postconditions, b') <- contractSteps rules False env (M.specEnsures (M.fnSpec fn)) b1
            let resultCheck = case M.fnReturns fn of
                    Just _ -> [step "RequireDefined" [("value", localRef 0)]]
                    Nothing -> []
            Just (resultCheck ++ postconditions, record "ExecutionEnd::Done" [], b')
        (Nothing, M.Goto target) -> Just ([], jump target, b1)
        (Nothing, M.SwitchBool (M.Const (M.CBool choice)) yes no) -> Just ([], jump (if choice then yes else no), b1)
        (Nothing, M.SwitchBool (M.Copy local) yes no) | Just (source, variantName) <- variantTest fn local -> do
            (object, b') <- operand source b1
            let (familyId, b2) = namedFunction ("enum:" ++ takeWhile (/= ':') variantName) b'
                (constructorId, b3) = namedFunction ("variant:" ++ variantName) b2
                assume matches = step "AssumeVariant" [("object", object), ("family", MInt familyId), ("constructor", MInt constructorId), ("matches", MBool matches)]
                M.BlockId yesId = yes
                M.BlockId noId = no
                ending = record "ExecutionEnd::Branch"
                    [("yes", MInt (toInteger yesId)), ("no", MInt (toInteger noId)), ("yesSteps", MList [assume True]), ("noSteps", MList [assume False])]
            Just ([step "RequireDefined" [("value", localRef (localNumber local))]], ending, b3)
        (Nothing, M.SwitchBool (M.Copy local) yes no) -> do
            let ref = localRef (localNumber local)
                required = step "RequireDefined" [("value", ref)]
            (trueRef, b2) <- operand (M.Const (M.CBool True)) b1
            (falseRef, b3) <- operand (M.Const (M.CBool False)) b2
            let M.BlockId yesId = yes
                M.BlockId noId = no
                ending = record "ExecutionEnd::BooleanBranch"
                    [("yes", MInt (toInteger yesId)), ("no", MInt (toInteger noId)), ("join", MInt (joinFor yes no)), ("value", ref), ("trueValue", trueRef), ("falseValue", falseRef)]
            Just ([required], ending, b3)
        (Nothing, M.Call calleeOp args dest target) | allowCalls -> do
            name <- case calleeOp of
                M.Const (M.CFn n) -> Just n
                M.Copy local -> Map.lookup local (fnValueLocals fn)
                _ -> Nothing
            (callSteps, posts, b') <- case Map.lookup name functions of
                Just callee | not ("builtin::" `isPrefixOf` name) -> directCall rules fn callee args dest termInfo (name == M.fnName fn || reachesName functions fn name (M.fnName fn)) b1
                _ -> do
                    (cs, bb) <- builtinCall (stripBuiltin name) args dest b1
                    pure (cs, [], bb)
            borrows <- borrowsOf functions fn
            (mutSteps, b'') <- case Map.lookup name functions of
                Just callee -> foldM (versionArg borrows callee posts) ([], b') (zip (M.fnParams callee) args)
                _ -> pure ([], b')
            (typeFacts, b''') <- typeSteps rules types invariants fn dest b''
            Just (callSteps ++ mutSteps ++ typeFacts, jump target, b''')
        _ -> Nothing
    pure (record "ExecutionBlock" [("id", MInt (toInteger n)), ("steps", MList (steps ++ extra)), ("end", ending)], b2)
  where
    -- A loop is checked by its invariant: its region is walked once, and every
    -- edge back to the header has to re-establish the invariant and shrink the
    -- variant. A block that leaves the loop (a return, or an exit from inside
    -- the body) is not in the region and is walked as an exit, as the reference
    -- validator does.
    encodeLoop spec yes no dummyLocal (r, a, c, variantTestInfo, withCondition) = do
        let orChainOf seen b
                | Set.member b seen = Nothing
                | otherwise = case Map.lookup b (M.fnBlocks fn) of
                    Just (M.BasicBlock [M.Assign cond (M.BinaryOp (M.Compare r2) a2 c2)] (M.SwitchBool (M.Copy cond') y2 n2))
                        | cond == cond' && y2 == yes -> do
                            (exitB, rest) <- orChainOf (Set.insert b seen) n2
                            Just (exitB, (r2, a2, c2) : rest)
                    _ -> Just (b, [])
        (exitBlock, orTestsRaw) <- orChainOf Set.empty no
        if (testChainToBody spec no yes || not (null orTestsRaw)) && yes /= blockId && no /= blockId && no /= yes then Just () else Nothing
        let region = Map.findWithDefault (Set.singleton blockId) blockId (loopRegions fn)
            assigned = nub
                [ v
                | member <- Set.toList region
                , Just (M.BasicBlock blockStmts term) <- [Map.lookup member (M.fnBlocks fn)]
                , v <- [d | M.Assign d _ <- blockStmts] ++ [r | M.AssignRef r _ _ <- blockStmts] ++ (case term of M.Call _ _ d _ -> [d]; _ -> []) ++ mutCallRoots term
                ]
        (genVariant, withCondition') <- case M.loopTermination spec of
            Just (Counting expr) -> case expr of
                Var _ -> Just (Nothing, withCondition)
                F (Val (VFunct _ _ _ (BuiltinFunct Minus) _)) [upperExpr, Var _]
                    | all (upperStable (M.loopEnv spec) assigned) (expressionVars upperExpr) -> Just (Nothing, withCondition)
                _ -> do
                    (vSteps, vRef, b') <- exprOperand (M.loopEnv spec) expr withCondition
                    Just (Just (vSteps, vRef), b')
            _ -> Just (Nothing, withCondition)
        (mode, variant, variantLocal, upper) <- case M.loopTermination spec of
            Just (Counting (Var name)) -> case Map.lookup name (M.loopEnv spec) of
                Just op@(M.Copy v) -> Just (0, op, v, Val (VInt 0))
                _ -> Nothing
            Just (Counting (F (Val (VFunct _ _ _ (BuiltinFunct Minus) _)) [upperExpr, Var name])) -> do
                counter <- Map.lookup name (M.loopEnv spec)
                case counter of M.Copy v -> Just (1, counter, v, upperExpr); _ -> Nothing
            Just (Counting _) -> Just (0, M.Const (M.CInt 0), dummyLocal, Val (VInt 0))
            Just (Parts (Var name)) -> case Map.lookup name (M.loopEnv spec) of
                Just op@(M.Copy v) -> Just (3, op, v, Val (VInt 0))
                _ -> Nothing
            Just MayDiverge -> Just (2, M.Const (M.CInt 0), dummyLocal, Val (VInt 0))
            _ -> Nothing
        decl <- Map.lookup variantLocal (M.fnLocals fn)
        if mode >= 2 || M.localType decl == TInt || genVariant /= Nothing then Just () else Nothing
        if genVariant /= Nothing || all (upperStable (M.loopEnv spec) assigned) (expressionVars upper) then Just () else Nothing
        (variantRef, variantSteps, b1) <- case genVariant of
            Just (vSteps, vRef) -> Just (vRef, vSteps, withCondition')
            Nothing -> do
                (vRef, b') <- operand variant withCondition'
                Just (vRef, [], b')
        (upperSteps, upperRef, b2) <- exprOperand (M.loopEnv spec) upper b1
        (zeroRef, b3) <- operand (M.Const (M.CInt 0)) b2
        (typeAssumptions, withTypes) <- foldM (loopType fn) ([], b3) assigned
        (checks, assumptions, b4) <- foldM (invariant (M.loopEnv spec)) (variantSteps, typeAssumptions, withTypes) (M.loopInvariant spec)
        (orTestValues, b5) <- foldM (\(acc, bb) (r2, a2, c2) -> do
            (lref, bb1) <- operand a2 bb
            (rref, bb2) <- operand c2 bb1
            let (k2, l2, r2') = normal r2 lref rref
            Just (acc ++ [record "LoopTest" [("relation", MInt k2), ("left", l2), ("right", r2')]], bb2)) ([], b4) orTestsRaw
        let (kind, left, right) = normal r a c
            M.BlockId exitId = exitBlock
            M.BlockId bodyId = yes
        let divergeGuard = if M.loopTermination spec == Just MayDiverge && not (mayDivergeFn fn) then [check 2 zeroRef zeroRef] else []
        pure (variantSteps ++ upperSteps ++ divergeGuard, record "ExecutionEnd::Loop" [("exit", MInt (toInteger exitId)), ("body", MInt (toInteger bodyId)),
             ("region", MList [MInt (toInteger number) | M.BlockId number <- Set.toList region]),
             ("checks", MList checks), ("assumptions", MList assumptions), ("havoc", MList (map (MInt . localNumber) assigned)),
             ("relation", MInt kind), ("left", left), ("right", right), ("variant", variantRef), ("variantMode", MInt (if genVariant /= Nothing then 0 else mode)),
             ("variantOther", upperRef), ("zero", zeroRef),
             ("variantObject", maybe (localRef (localNumber dummyLocal)) (\(object, _, _) -> object) variantTestInfo),
             ("variantFamily", MInt (maybe (-1) (\(_, familyId, _) -> familyId) variantTestInfo)),
             ("variantConstructor", MInt (maybe (-1) (\(_, _, constructorId) -> constructorId) variantTestInfo)),
             ("orTests", MList orTestValues)], b5)
    mutCallRoots (M.Call (M.Const (M.CFn name)) args _ _) = case Map.lookup name functions of
        Just callee ->
            [ root
            | (pname, arg) <- zip [n | p <- M.fnParams callee, Just d <- [Map.lookup p (M.fnLocals callee)], Just n <- [M.localName d]] args
            , pname `elem` M.specMutParams (M.fnSpec callee)
            , Just (root, _) <- [case arg of M.Copy l -> Just (maybe (l, []) id (Map.lookup l (fromMaybe Map.empty (borrowsOf functions fn)))); M.Move l -> Just (maybe (l, []) id (Map.lookup l (fromMaybe Map.empty (borrowsOf functions fn)))); _ -> Nothing]
            ]
        _ -> []
    mutCallRoots _ = []
    expressionVars expr = case expr of
        Var name -> [name]
        F (Var _) args -> concatMap expressionVars args
        F f args -> expressionVars f ++ concatMap expressionVars args
        _ -> []
    -- A condition of several tests (a && b && ...) reaches the body through a
    -- chain of test blocks, each leaving to the same exit when its test fails.
    testChainToBody spec exit start = go Set.empty start
      where
        go seen b
            | b == M.loopBody spec = True
            | Set.member b seen = False
            | otherwise = case Map.lookup b (M.fnBlocks fn) of
                Just (M.BasicBlock _ (M.SwitchBool _ next no')) -> no' == exit && go (Set.insert b seen) next
                Just (M.BasicBlock _ (M.Call _ _ _ target)) -> go (Set.insert b seen) target
                _ -> False
    upperStable env assigned name = case Map.lookup name env of
        Just (M.Copy v) -> v `notElem` assigned
        Just (M.Const _) -> True
        _ -> False
    expressionOperand env expr = case expr of
        Var name -> Map.lookup name env
        Val (VInt value) -> Just (M.Const (M.CInt value))
        _ -> Nothing
    invariant env (checks, assumptions, b) (ProofAssert p) = do
        (prefix, checkStep, b') <- proofCheck env p b
        case forallFactSteps env p b' of
            Just (fsteps, _) -> pure (checks ++ prefix ++ [checkStep], assumptions ++ fsteps, b')
            -- A forall in any other shape is checked but not assumed (see
            -- contractSteps): assuming one index of it could contradict
            -- the context when its guards cannot hold.
            Nothing -> case p of
                Forall _ _ _ -> pure (checks ++ prefix ++ [checkStep], assumptions, b')
                _ -> do
                    assumption <- asAssumption checkStep
                    pure (checks ++ prefix ++ [checkStep], assumptions ++ prefix ++ [assumption], b')
    invariant _ _ _ = Nothing
    loopType current (steps, b) local = do
        (more, b') <- typeSteps rules types invariants current local b
        pure (steps ++ more, b')
    asAssumption (MData "ExecutionStep::Check" fields) = Just (MData "ExecutionStep::Assume" fields)
    asAssumption _ = Nothing
    add (steps, b, conditions, penv) s = case s of
        M.Ghost env (M.GhostValidation (AssignProofVar var expr)) ->
            Just (steps, b, conditions, Map.insert var (substituteProof penv (exprToProof expr)) penv)
        M.Ghost env (M.GhostValidation (ProofAssert proof)) -> do
            (prefix, checked, b') <- proofCheck env (substituteProof penv proof) b
            pure (steps ++ prefix ++ [checked], b', conditions, penv)
        M.Ghost env (M.GhostValidation (Rewrite rule)) -> do
            (more, b') <- rewriteSteps rules env (substituteRule penv rule) b
            pure (steps ++ more, b', conditions, penv)
        M.Ghost env (M.GhostValidation (Assume proof)) -> do
            (more, b') <- contractSteps rules True env [ProofAssert (substituteProof penv proof)] b
            pure (steps ++ more, b', conditions, penv)
        M.Assign dest (M.BinaryOp (M.Compare r) a c) -> do
            (left, b1) <- operand a b
            (right, b2) <- operand c b1
            let (x, b3) = fresh b2
                (y, b4) = fresh b3
                leftLocal = negate x - 1
                rightLocal = negate y - 1
                save i v = step "Assign" [("local", MInt i), ("value", v)]
            (more, b5) <- statement rules s b4
            (typeFacts, b6) <- typeSteps rules types invariants fn dest b5
            pure (steps ++ [save leftLocal left, save rightLocal right] ++ more ++ typeFacts, b6,
                  Map.insert dest (r, localRef leftLocal, localRef rightLocal) conditions, penv)
        M.Assign dest (M.Borrow root place _) -> do
            (rootRef, b1) <- operand (M.Copy root) b
            (pSteps, placeRef, b2) <- placeRefOf True rootRef place b1
            (typeFacts, b3) <- typeSteps rules types invariants fn dest b2
            pure (steps ++ pSteps ++ [step "Assign" [("local", MInt (localNumber dest)), ("value", placeRef)]] ++ typeFacts, b3, Map.delete dest conditions, penv)
        M.AssignRef root place (M.Use value) -> do
            borrows <- borrowsOf functions fn
            (valueRef, b1) <- operand value b
            let (i, b2) = fresh b1
                tempLocal = negate i - 1
                tempRef = localRef tempLocal
                save = step "Assign" [("local", MInt tempLocal), ("value", valueRef)]
            (rootRef, _) <- operand (M.Copy root) b2
            (checkSteps, _, b3) <- placeRefOf True rootRef place b2
            (updSteps, newRootRef, b4) <- updateRefOf rootRef place tempRef b3
            (typeFacts, b5) <- typeSteps rules types invariants fn root b4
            (rebindSteps, b6) <- rebindAfter borrows root b5
            pure (steps ++ [save] ++ checkSteps ++ updSteps ++ [step "Assign" [("local", MInt (localNumber root)), ("value", newRootRef)]] ++ typeFacts ++ rebindSteps, b6, conditions, penv)
        M.AssignRef _ _ _ -> Nothing
        M.Assign dest (M.MakeData name fields) -> do
            let base = maybe name fst (instanceOf name)
                clauses = Map.findWithDefault [] base invariants
            (checks, b1) <- contractSteps rules False (Map.fromList fields) clauses b
            (more, b2) <- statement rules s b1
            (typeFacts, b3) <- typeSteps rules types invariants fn dest b2
            pure (steps ++ checks ++ more ++ typeFacts, b3, Map.delete dest conditions, penv)
        M.Assign dest (M.ListOp M.NewArray [lengthValue, _]) -> do
            decl <- Map.lookup dest (M.fnLocals fn)
            case M.localType decl of
                TArrayOf _ (SizeParam name) ->
                    case [p | p <- drop (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn), Just d <- [Map.lookup p (M.fnLocals fn)], M.localName d == Just name] of
                        p : _ | lengthValue == M.Copy p -> Just ()
                        _ -> Nothing
                _ -> Just ()
            (more, b1) <- statement rules s b
            (typeFacts, b2) <- typeSteps rules types invariants fn dest b1
            pure (steps ++ more ++ typeFacts, b2, Map.delete dest conditions, penv)
        M.Assign dest _ -> do
            (more, b') <- statement rules s b
            (typeFacts, b'') <- typeSteps rules types invariants fn dest b'
            borrows <- borrowsOf functions fn
            (rebindSteps, b''') <- rebindAfter borrows dest b''
            pure (steps ++ more ++ typeFacts ++ rebindSteps, b''', Map.delete dest conditions, penv)
        _ -> do
            (more, b') <- statement rules s b
            pure (steps ++ more, b', conditions, penv)

    localNumber (M.Local i) = toInteger i
    localRef i = record "ValueRef::Local" [("local", MInt i)]
    -- The term for the value at a place, from a reference to its root. Making
    -- a borrow checks the index steps; reading a place back after its root
    -- changed does not (the reference validator checks a place only where
    -- the borrow is made and where it is written through).
    placeRefOf checked ref steps b0 = case steps of
        [] -> Just ([], ref, b0)
        M.RefField _ field : rest -> do
            let (function, b1) = namedFunction ("field:" ++ field) b0
                (i, b2) = fresh b1
                local = negate i - 1
                ref' = localRef local
            (more, ref'', b3) <- placeRefOf checked ref' rest b2
            pure ([step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [ref])]] ++ more, ref'', b3)
        M.RefIndex index : rest -> do
            (indexRef, b1) <- operand index b0
            let (i, b2) = fresh b1
                local = negate i - 1
                ref' = localRef local
            (first, b3) <- if checked then getSteps local ref indexRef b2 else pure ([step "ApplyFresh" [("local", MInt local), ("function", MInt (-14)), ("arguments", MList [ref, indexRef])]], b2)
            (more, ref'', b4) <- placeRefOf checked ref' rest b3
            pure (first ++ more, ref'', b4)
    -- A root whose place at the steps is given a new value: the new root,
    -- built from the old one with that place replaced.
    updateRefOf rootRef steps valueRef b0 = case steps of
        [] -> Just ([], valueRef, b0)
        M.RefField ctor field : rest -> do
            (s1, innerRef, b1) <- placeRefOf False rootRef [M.RefField ctor field] b0
            (s2, newInner, b2) <- updateRefOf innerRef rest valueRef b1
            fields <- case Map.lookup ctor types of
                Just (M.StructDecl fs) -> Just (map fst fs)
                Just (M.EnumDecl variants) -> case [fs | (vname, fs) <- variants, vname == ctor || snd (break (== ':') ctor) == vname || ctor == vname] of
                    fs : _ -> Just (map fst fs)
                    [] -> Nothing
                Nothing -> case [map fst fs | (ename, M.EnumDecl variants) <- Map.toList types, (vname, fs) <- variants, ename ++ "::" ++ vname == ctor] of
                    fs : _ -> Just fs
                    [] -> Nothing
            (s3, argRefs, b3) <- foldM (fieldArg rootRef newInner field) ([], [], b2) fields
            let (constructor, b4) = namedFunction ("ctor:" ++ ctor) b3
                (i, b5) = fresh b4
                local = negate i - 1
                newRef = localRef local
                create = step "ApplyFresh" [("local", MInt local), ("function", MInt constructor), ("arguments", MList argRefs)]
            (projections, b6) <- foldM (projectNew newRef) ([], b5) (zip fields argRefs)
            (checks, b7) <- invariantChecks ctor newRef argRefs fields b6
            pure (s1 ++ s2 ++ s3 ++ [create] ++ projections ++ checks, newRef, b7)
        M.RefIndex index : rest -> do
            (indexRef, b1) <- operand index b0
            (s1, elemRef, b2) <- placeRefOf False rootRef [M.RefIndex index] b1
            (s2, newInner, b3) <- updateRefOf elemRef rest valueRef b2
            let (i, b4) = fresh b3
                local = negate i - 1
                newRef = localRef local
            (s3, b5) <- setSteps local rootRef indexRef newInner b4
            pure (s1 ++ s2 ++ s3, newRef, b5)
      where
        fieldArg rootRef newInner wanted (steps', refs, b) f
            | f == wanted = pure (steps', refs ++ [newInner], b)
            | otherwise = do
                let (function, b1) = namedFunction ("field:" ++ f) b
                    (i, b2) = fresh b1
                    local = negate i - 1
                    ref = localRef local
                pure (steps' ++ [step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [rootRef])]], refs ++ [ref], b2)
        projectNew newRef (steps', b) (f, argRef) = do
            let (function, b1) = namedFunction ("field:" ++ f) b
                (i, b2) = fresh b1
                local = negate i - 1
                ref = localRef local
            pure (steps' ++ [step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [newRef])], step "Assume" [("relation", MInt 0), ("left", ref), ("right", argRef)]], b2)
        invariantChecks ctor newRef argRefs fields b = do
            let base = maybe ctor fst (instanceOf ctor)
                clauses = Map.findWithDefault [] base invariants
            if null clauses then pure ([], b) else do
                env <- case traverse refOperand (zip fields argRefs) of Just pairs -> Just (Map.fromList pairs); Nothing -> Nothing
                (checks, b') <- contractSteps rules False env clauses b
                pure (checks, b')
          where
            refOperand (f, MData "ValueRef::Local" fields') = case lookup "local" fields' of Just (MInt n) -> Just (f, M.Copy (M.Local (fromInteger n))); _ -> Nothing
            refOperand _ = Nothing
    -- After a call, what an update argument is to gets the version the
    -- callee's contract gave it.
    versionArg borrows callee posts (steps, b) (param, arg) = case [name | p <- [param], Just d <- [Map.lookup p (M.fnLocals callee)], Just name <- [M.localName d]] of
        [name] -> case lookup name posts of
            Nothing -> pure (steps, b)
            Just postRef -> do
                (root, placeSteps) <- case arg of
                    M.Copy l -> Just (maybe (l, []) id (Map.lookup l borrows))
                    M.Move l -> Just (maybe (l, []) id (Map.lookup l borrows))
                    _ -> Nothing
                (updSteps, newRootRef, b1) <- updateRefOf (localRef (localNumber root)) placeSteps postRef b
                (rebindSteps, b2) <- rebindAfter borrows root b1
                pure (steps ++ updSteps ++ [step "Assign" [("local", MInt (localNumber root)), ("value", newRootRef)]] ++ rebindSteps, b2)
        _ -> pure (steps, b)
    -- After a root gets a new version, the references to places of it are
    -- bound again to the place in the new version.
    rebindAfter borrows root b0 = foldM add ([], b0) [(ref, steps) | (ref, (r, steps)) <- Map.toList borrows, r == root, ref /= root]
      where
        add (steps, b) (ref, placeSteps) = do
            (more, placeRef, b') <- placeRefOf False (localRef (localNumber root)) placeSteps b
            pure (steps ++ more ++ [step "Assign" [("local", MInt (localNumber ref)), ("value", placeRef)]], b')
    jump (M.BlockId target) = record "ExecutionEnd::Jump" [("target", MInt (toInteger target))]
    -- The join of a branch is the first block both successors reach by straight
    -- jumps alone, when neither the branch nor the join is inside a loop region:
    -- merging there is what the Tersus checker does at that block, and inside a
    -- loop the per-path walk is kept instead, since a merged state can drop the
    -- facts a loop invariant is checked against.
    joinFor yes no
        | any (Set.member blockId) regions = -1
        | otherwise = case [n | c@(M.BlockId n) <- path yes, c `elem` path no, c /= blockId, not (Map.member c (M.specLoops (M.fnSpec fn))), not (any (Set.member c) regions)] of
            n : _ -> toInteger n
            [] -> -1
      where
        regions = Map.elems (loopRegions fn)
        path start = go Set.empty start
          where
            go seen b
                | Set.member b seen = []
                | otherwise = b : case Map.lookup b (M.fnBlocks fn) of
                    Just (M.BasicBlock _ (M.Goto target)) -> go (Set.insert b seen) target
                    _ -> []
    variantTest :: M.Function -> M.Local -> Maybe (M.Operand, Name)
    variantTest f local = case [(src, name) | blk <- Map.elems (M.fnBlocks f), M.Assign dest (M.IsVariant src name) <- M.blockStatements blk, dest == local] of
        r : _ -> Just r
        [] -> Nothing
    constBoolTest f local = case [value | blk <- Map.elems (M.fnBlocks f), M.Assign dest (M.Use (M.Const (M.CBool value))) <- M.blockStatements blk, dest == local] of
        value : _ -> Just value
        [] -> Nothing
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

contextOf :: Build -> MirValue
contextOf b = record "ValidatorContext" [("equalities", MList []), ("applications", MList (literalApps b)), ("constants", MList (literalTerms b)), ("orders", MList []), ("different", MList []), ("variants", MList []), ("fieldFunctions", MList [MInt i | (name, i) <- namedFunctions b, "field:" `isPrefixOf` name]), ("constructorFunctions", MList [MInt i | (name, i) <- namedFunctions b, "ctor:" `isPrefixOf` name]), ("constructorFields", MList [record "ConstructorField" [("constructor", MInt c), ("field", MInt f), ("index", MInt i)] | (c, f, i) <- ctorFields b]), ("differences", MList [])]

-- A proof rule is checked once, generically: its input clauses are assumed
-- over fresh parameter terms, then its body and output clauses are checked.
-- An axiom has no body and is taken on trust, as `tersus assumptions` says.
encodeRule :: Rules -> (Variable, Rule) -> Maybe (MirValue, MirValue, Integer)
encodeRule rules (_, (params, ins, outs, Just body)) = do
    let indexed = zip params [0 ..]
        env0 = Map.fromList [(param, M.Copy (M.Local i)) | (param, i) <- indexed]
        alloc (bindings, b) (_, i) = let (term, b') = fresh b in (bindings ++ [record "LocalBinding" [("local", MInt (toInteger i)), ("term", MInt term)]], b')
        (paramBindings, b0) = foldl alloc ([], emptyBuild) indexed
    (inSteps, b1, env1, next1) <- genericClauses rules True env0 ins b0 (length params)
    (bodySteps, b2, env2, next2) <- genericClauses rules False env1 body b1 next1
    (outSteps, b3, _, _) <- genericClauses rules False env2 outs b2 next2
    let block' = record "ExecutionBlock" [("id", MInt 0), ("steps", MList (inSteps ++ bodySteps ++ outSteps)), ("end", record "ExecutionEnd::Done" [])]
        initial = record "ExecutionState" [("context", contextOf b3), ("locals", MList paramBindings)]
    pure (MList [block'], initial, 0)
encodeRule _ _ = Nothing

genericClauses :: Rules -> Bool -> M.Env -> [ValidationStatement] -> Build -> Int -> Maybe ([MirValue], Build, M.Env, Int)
genericClauses rules assumeMode env0 clauses b0 next0 = foldM go ([], b0, env0, next0) clauses
  where
    go (steps, b, env, next) (ProofAssert proof) = do
        (more, b') <- contractSteps rules assumeMode env [ProofAssert proof] b
        pure (steps ++ more, b', env, next)
    go (steps, b, env, next) (AssignProofVar var expr) = do
        (prefix, ref, b') <- proofOperand env (exprToProof expr) b
        let assign = step "Assign" [("local", MInt (toInteger next)), ("value", ref)]
        pure (steps ++ prefix ++ [assign], b', Map.insert var (M.Copy (M.Local next)) env, next + 1)
    go (steps, b, env, next) (Rewrite rule) = do
        (more, b') <- rewriteSteps rules env rule b
        pure (steps ++ more, b', env, next)
    go (steps, b, env, next) (Assume proof) = do
        (more, b') <- contractSteps rules True env [ProofAssert proof] b
        pure (steps ++ more, b', env, next)

encodeFunction :: Map.Map Name M.TypeDecl -> Map.Map Name [ValidationStatement] -> Map.Map Name M.Function -> Rules -> Bool -> M.Function -> Maybe (MirValue, MirValue, Integer)
encodeFunction types invariants functions rules allowCalls fn
    | any (\(M.Local n) -> n < 0) (Map.keys (M.fnLocals fn)) = Nothing
    | length (M.fnParams fn) /= length (nub (M.fnParams fn)) = Nothing
    | M.Local 0 `elem` M.fnParams fn = Nothing
    | length (M.fnSizeParams fn) > length (M.fnParams fn) = Nothing
    | length (M.fnSizeParams fn) /= length (nub (M.fnSizeParams fn)) = Nothing
    | any ambiguousSizeName (M.fnSizeParams fn) = Nothing
    | any parameterAssigned sizeParams = Nothing
    | any wrongSizeName (zip sizeParams (M.fnSizeParams fn)) = Nothing
    | Map.member (M.BlockId (-1)) (M.fnBlocks fn) = Nothing
    | otherwise = do
        let (params, start) = foldl addParam ([], emptyBuild{buildFunctions = functions, buildRules = rules}) (M.fnParams fn)
        (paramFacts, withTypes) <- foldM addType ([], start) (M.fnParams fn)
        (sizeFacts, withSizes) <- sizeParameterSteps True fn (M.fnParams fn) withTypes
        (requires, withRequires) <- contractSteps rules True (M.specEnv spec) (M.specRequires spec) withSizes
        let recursive = any (\name -> reachesName functions fn name (M.fnName fn)) (callNamesOf fn)
        (variantSteps, termInfo, withVariant) <- case M.specTermination spec of
            Just (Counting expr) -> do
                (steps, variantRef, b1) <- exprOperand (M.specEnv spec) expr withRequires
                (zero, b2) <- operand (M.Const (M.CInt 0)) b1
                pure (steps ++ [check 3 zero variantRef], if recursive then Just (False, variantRef) else Nothing, b2)
            Just (Parts expr) | recursive -> do
                (steps, variantRef, b1) <- exprOperand (M.specEnv spec) expr withRequires
                pure (steps, Just (True, variantRef), b1)
            _ -> pure ([], Nothing, withRequires)
        let addBlock (blocks, b) entry = do
                (v, b') <- block types invariants functions rules termInfo allowCalls fn entry b
                pure (blocks ++ [v], b')
        (blocks, b) <- foldM addBlock ([], withVariant) (Map.toList (M.fnBlocks fn))
        let context = contextOf b
            oldSteps = [step "Assign" [("local", MInt (-(1000000 + localNum p))), ("value", record "ValueRef::Local" [("local", MInt (localNum p))])] | p <- M.fnParams fn, Just d <- [Map.lookup p (M.fnLocals fn)], Just name <- [M.localName d], name `elem` M.specMutParams spec]
            entry = record "ExecutionBlock" [("id", MInt (-1)), ("steps", MList (paramFacts ++ sizeFacts ++ requires ++ variantSteps ++ oldSteps)), ("end", record "ExecutionEnd::Jump" [("target", MInt 0)])]
        pure (MList (entry : blocks), record "ExecutionState" [("context", context), ("locals", localsMap params)], -1)
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
         in (params ++ [(toInteger local, term)], b')
    -- A HashMap value with every entry in its single bucket: lookups hash to bucket 0 of one,
    -- and the first insert past four entries spreads it into the usual shape.
    localsMap bindings =
        record "HashMap"
            [ ("buckets", MList [MList [record "Entry" [("key", MInt local), ("value", MInt term)] | (local, term) <- bindings]])
            , ("count", MInt (toInteger (length bindings)))
            ]
    addType (steps, b) local = do
        (more, b') <- typeSteps rules types invariants fn local b
        pure (steps ++ more, b')

encode :: M.Program -> Either String [(Name, (MirValue, MirValue, Integer))]
-- Generic functions are checked as the copies a call decides (MirMono
-- makes them for native code after validation there; the validator
-- written in Tersus is given the same copies, so a call of a generic
-- function names the copy of it the call decides).
encode program0 = encodeMono withTemplates
  where
    mono = monomorphizeForValidation program0
    -- A contract can name a generic function nothing calls (a method
    -- the contract measures by, like size): monomorphisation keeps
    -- only the copies a call decides, so the templates stay beside
    -- them as the contracts' sources (they are not checked as
    -- functions, only where a call decides their types).
    withTemplates = mono { M.progFunctions = Map.union (M.progFunctions mono) (Map.filter (\fn -> not (null (M.fnTypeParams fn))) (M.progFunctions program0)), M.progTypes = Map.union (M.progTypes mono) (M.progTypes program0) }

encodeMono :: M.Program -> Either String [(Name, (MirValue, MirValue, Integer))]
encodeMono program
    | Just fn <- find unsupportedFunction allFunctions = Left ("a type of a local, the result or a reference result of " ++ M.fnName fn)
    | Just (name, _) <- find (unsupportedDecl . snd) (Map.toList (M.progTypes program)) = Left ("a field type of " ++ name)
    | not (null (M.fnParams (M.progMain program))) = Left "a main function with parameters"
    | not (null (M.specRequires mainSpec) && null (M.specEnsures mainSpec)) = Left "a contract on the program itself"
    | length names /= length (nub names) = Left "two functions with one name"
    | any (\name -> Map.member name (fst stdLibValCtx)) names = Left "a function named like a builtin"
    | length targets /= length (nub targets) = Left "two definitions of one function"
    | any (\name -> name `notElem` targets && not (isInstanceName name)) [name | name <- Map.keys (M.progFunctions program), not ("builtin::" `isPrefixOf` name)] = Left "a function with no definition"
    | any (\(_, called) -> Map.notMember called (M.progFunctions program)) functionCalls = Left "a definition of a function that is not there"
    | any (\(name, fn) -> name /= M.fnName fn) (Map.toList (M.progFunctions program)) = Left "a function filed under another name"
    | otherwise = do
        let functions = M.progFunctions program
            invariants = M.progInvariants program
            types = M.progTypes program
        rules' <- maybe (Left "an axiom or proof rule") Right (collectRules program)
        let encodeOne fn = maybe (Left ("an operation in " ++ M.fnName fn)) (\v -> Right (M.fnName fn, v)) (encodeFunction types invariants functions rules' True fn)
        -- A function with type parameters is a template: it is checked
        -- only where a call decides its types, as its instances in the
        -- program (the reference does the same). The one exception is a
        -- function that checks an impl against its trait (TypeCheck
        -- writes it beside the impl, and nothing calls it): it is
        -- checked as written, or a weaker impl would pass.
        checked <- traverse encodeOne [fn | fn <- Map.elems functions, not (externFunction fn), null (M.fnTypeParams fn) || isJust (parseImplCheckName (M.fnName fn))]
        main <- encodeOne (M.progMain program)
        let ruleEntries = [("rule " ++ name, v) | entry@(name, _) <- Map.toList rules', Just v <- [encodeRule rules' entry]]
        pure (checked ++ ruleEntries ++ [main])
  where
    allFunctions = M.progMain program : Map.elems (M.progFunctions program)
    externFunction fn = "extern " `isPrefixOf` M.fnName fn
    unsupportedFunction fn = any (unsupportedType . M.localType) (Map.elems (M.fnLocals fn)) || maybe False unsupportedType (M.fnReturns fn)
    unsupportedDecl (M.StructDecl fields) = any (unsupportedType . snd) fields
    unsupportedDecl (M.EnumDecl variants) = any (any (unsupportedType . snd) . snd) variants
    unsupportedType t = case t of
        TWord{} -> False
        TAddr{} -> False
        TBlock{} -> False
        TList element -> unsupportedType element
        TArrayOf element _ -> unsupportedType element
        TBox element -> unsupportedType element
        TFn args result -> any unsupportedType args || unsupportedType result
        TForall _ _ element -> unsupportedType element
        TUninit element -> unsupportedType element
        _ -> False
    isEnum M.EnumDecl{} = True
    isEnum _ = False
    mainSpec = M.fnSpec (M.progMain program)
    definitions = [(isMain, blockId, name, source, top) | (isMain, fn) <- (True, M.progMain program) : [(False, f) | f <- Map.elems (M.progFunctions program)],
        (blockId, block') <- Map.toList (M.fnBlocks fn), M.Ghost _ (M.GhostFunction name source top) <- M.blockStatements block']
    names = [source | (_, _, _, source, _) <- definitions]
    targets = [name | (_, _, name, _, _) <- definitions]
    -- The copies monomorphisation made (MirMono's instance names): they
    -- have no definition marker of their own, and are defined by the
    -- template's.
    instanceNames = [name | name <- Map.keys (M.progFunctions program), isInstanceName name]
    instanceBases = mapMaybe instanceBase instanceNames
    instanceBase name = case [take i name | (i, '<') <- zip [0 ..] name, balancedSuffix (drop i name)] of
        base : _ -> Just base
        [] -> Nothing
    isInstanceName name = or [balancedSuffix (drop i name) | (i, '<') <- zip [0 ..] name]
    balancedSuffix suffix = go suffix (0 :: Int)
      where
        go [] depth = depth == 0
        go ('<' : rest) depth = go rest (depth + 1)
        go ('>' : rest) depth = depth > 0 && go rest (depth - 1)
        go (_ : rest) depth = go rest depth
    definitionOrder = Map.fromList (zip targets [0 :: Int ..])
    functionCalls = [(name, called) | (name, fn) <- Map.toList (M.progFunctions program),
        block' <- Map.elems (M.fnBlocks fn), M.Call (M.Const (M.CFn called)) _ _ _ <- [M.blockTerminator block']]
    invalidCall (caller, called) = case (Map.lookup caller definitionOrder, Map.lookup called definitionOrder) of
        (Just callerIndex, Just calledIndex) -> calledIndex >= callerIndex
        _ -> True

-- The first argument is the validated lib/validation.tersus program. The
-- verdict says whether every obligation was proved, which one was not, or
-- what part of the MIR is outside this bridge's current subset (including
-- most loop shapes and function calls).
validateMirSubset :: M.Program -> M.Program -> Result Verdict String
validateMirSubset checker program = verifyProgram program `bindResult` \_ -> case encode program of
    Left what -> Ok (Unmodeled what)
    Right functions -> checkFunctions functions
  where
    checkFunctions [] = Ok Proved
    checkFunctions ((name, (blocks, initial, entry)) : rest) = runNamedFunction checker "validateExecution" [blocks, MInt entry, initial] `bindResult` \result -> case result of
        Just (MData "ExecutionFlowResult" fields) -> case (lookup "status" fields, lookup "block" fields, lookup "step" fields) of
            (Just (MInt 0), _, _) -> checkFunctions rest
            (Just (MInt 1), Just (MInt b), Just (MInt i)) -> Ok (Unproved (name ++ ", block " ++ show b ++ ", step " ++ show i))
            (Just (MInt 2), Just (MInt b), _) -> Ok (Unmodeled ("an operation in " ++ name ++ ", block " ++ show b))
            (Just (MInt 3), _, _) -> Ok (Unmodeled ("the control flow of " ++ name))
            (Just (MInt _), Just (MInt b), _) -> Ok (Unmodeled ("a loop of " ++ name ++ " at block " ++ show b))
            _ -> Error "Tersus validator returned an invalid status"
        _ -> Error "Tersus validator returned an invalid result"

-- What the validator said of a program: every obligation proved, one not proved (where), or a part of the program the
-- bridge or the validator does not model (what)
data Verdict = Proved | Unproved String | Unmodeled String

-- A verdict as a yes, a no, or no answer
verdictProved :: Verdict -> Maybe Bool
verdictProved verdict = case verdict of
    Proved -> Just True
    Unproved _ -> Just False
    Unmodeled _ -> Nothing

-- The validator written in Tersus, lowered once without passing through any
-- validator (it is the bootstrap: the Tersus validator's own test in
-- TestPipeline checks that it accepts its own MIR). Every program that is
-- validated is validated by this program and nothing else.
checkerProgram :: Result M.Program String
checkerProgram = case parseSourceWith True validationSource of
    Error err -> Error ("Could not parse lib/validation.tersus: " ++ err)
    Ok stmts -> elaborate stmts `bindResult` \elaborated -> lowerElaborated elaborated `bindResult` eraseGhosts

-- Validate a program with the Tersus validator. A program the bridge does not
-- model is refused, not waved through: there is no other validator to fall
-- back to.
validateByTersus :: M.Program -> Result () String
validateByTersus program = checkerProgram `bindResult` \checker -> validateMirSubset checker program `bindResult` \verdict -> case verdict of
    Proved -> Ok ()
    Unproved place -> Error ("Could not prove: an obligation could not be proved by the Tersus validator (in " ++ place ++ ")")
    Unmodeled what -> Error ("the program uses a feature the Tersus validator does not model yet: " ++ what)
