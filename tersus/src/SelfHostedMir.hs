-- A conservative bridge from the supported MIR subset to the Tersus checker.
-- Unsupported instructions or proof forms are reported as Nothing so the
-- production pipeline can delegate those cases to the reference validator.
module SelfHostedMir (checkerProgram, validateMir, validateMirSubset) where

import Control.Monad (foldM)
import Control.Applicative ((<|>))
import Data.List (find, intersect, minimumBy, nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, isNothing, mapMaybe)
import Data.Ord (comparing)
import qualified Data.Set as Set
import qualified Mir as M
import MirEval (MirValue (..), runNamedFunction)
import MirLower (lowerElaborated)
import MirVerify (verifyProgram)
import Parse (emptyDecls, locating, parseStatementBlockWith)
import PreludeSource (preludeSource, validationSource)
import ProofHelpers (proofVars)
import StdLib (builtinFunct, stdLibRuleCtx, stdLibValCtx)
import TersusTypes
import TypeCheck (elaborate)
import Utils (Result (..), bindResult, inIntRange)

data Build = Build
    { nextTerm :: Integer
    , literalIds :: [(M.Constant, Integer)]
    , literalTerms :: [MirValue]
    , literalApps :: [MirValue]
    , literalVariants :: [(Integer, Integer, Integer)]
    , namedFunctions :: [(String, Integer)]
    , enumTypes :: [(Name, [Name])]
    , proofRules :: RuleContext
    , proofFunctions :: Map.Map Name M.Function
    , proofCandidateFunctions :: Map.Map Name M.Function
    , proofTypes :: Map.Map Name M.TypeDecl
    , proofGenerics :: Map.Map Name ([Variable], [(Variable, Type)])
    , proofInvariants :: Map.Map Name [ValidationStatement]
    , proofWorldReaders :: Set.Set Name
    , proofCaller :: M.Function
    , proofBlockContext :: Maybe (M.BlockId, [M.Statement])
    , proofSizeValues :: Map.Map M.Local Size
    }

emptyBuild :: [(Name, [Name])] -> RuleContext -> Map.Map Name M.Function -> Map.Map Name M.TypeDecl -> Map.Map Name ([Variable], [(Variable, Type)]) -> Map.Map Name [ValidationStatement] -> Set.Set Name -> M.Function -> Build
emptyBuild enumInfo rules functions types generics invariants worldReaders caller =
    Build 0 [] [] [] [] [] enumInfo rules functions functions types generics invariants worldReaders caller Nothing Map.empty

record :: String -> [(String, MirValue)] -> MirValue
record = MData

constructorFieldTerms :: Map.Map Name M.TypeDecl -> [(String, Integer)] -> [MirValue]
constructorFieldTerms types functions = concatMap typeFields (Map.toList types)
  where
    typeFields (name, M.StructDecl fields) = fieldsFor name fields
    typeFields (_, M.EnumDecl variants) = concat [fieldsFor variant fields | (variant, fields) <- variants]
    fieldsFor constructor fields = case lookup ("ctor:" ++ constructor) functions of
        Nothing -> []
        Just constructorId ->
            [ record "ConstructorField" [("constructor", MInt constructorId), ("field", MInt fieldId), ("index", MInt index)]
            | (index, (field, _)) <- zip [0 ..] fields
            , fieldId <- catMaybes
                [ lookup ("field:" ++ field) functions
                , lookup ("project:" ++ constructor ++ ":" ++ field) functions
                ]
            ]

fresh :: Build -> (Integer, Build)
fresh b = (nextTerm b, b{nextTerm = nextTerm b + 1})

namedFunction :: String -> Build -> (Integer, Build)
namedFunction "within" b = (-20, b)
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
    Nothing | M.CData name fields <- c, Just familyName <- enumFamily (enumTypes b) name -> do
        (fieldIds, b1) <- foldM addFieldValue ([], b) fields
        let (family, b1a) = namedFunction ("enum:" ++ familyName) b1
            (constructor, b2) = namedFunction ("ctor:" ++ name) b1a
            (i, b3) = fresh b2
            made = record "ApplicationTerm" [("id", MInt i), ("function", MInt constructor), ("arguments", MList (map MInt fieldIds))]
            b4 = b3{literalIds = (c, i) : literalIds b3, literalApps = made : literalApps b3, literalVariants = (i, family, constructor) : literalVariants b3}
        b5 <- foldM (addProjection i) b4 (zip fields fieldIds)
        b6 <- addVariantConstants name i b5
        pure (i, b6)
    Nothing | M.CData name fields <- c -> do
        (fieldIds, b1) <- foldM addFieldValue ([], b) fields
        let (constructor, b2) = namedFunction ("ctor:" ++ name) b1
            (i, b3) = fresh b2
            made = record "ApplicationTerm" [("id", MInt i), ("function", MInt constructor), ("arguments", MList (map MInt fieldIds))]
            b4 = b3{literalIds = (c, i) : literalIds b3, literalApps = made : literalApps b3}
        b5 <- foldM (addProjection i) b4 (zip fields fieldIds)
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
    enumFamily enums variant = case [name | (name, variants) <- enums, variant `elem` variants] of
        name : _ -> Just name
        [] -> Nothing
    addLiteral (ids, current) value = do
        (i, next) <- literal value current
        pure (ids ++ [i], next)
    addElement listId current (index, valueId) = do
        (indexId, next) <- literal (M.CInt index) current
        let app = record "ApplicationTerm" [("id", MInt valueId), ("function", MInt (-14)), ("arguments", MList [MInt listId, MInt indexId])]
        pure next{literalApps = app : literalApps next}
    addFieldValue (ids, current) (_, value) = do
        (i, next) <- literal value current
        pure (ids ++ [i], next)
    addProjection object current ((field, _), value) =
        let (function, next) = namedFunction ("field:" ++ field) current
            projection = record "ApplicationTerm" [("id", MInt value), ("function", MInt function), ("arguments", MList [MInt object])]
         in Just next{literalApps = projection : literalApps next}
    addVariantConstants name object current = do
        case [variants | (_, variants) <- enumTypes current, name `elem` variants] of
            [variants] -> foldM (addVariant object name) current variants
            _ -> Just current
    addVariant object actual current tag = do
        let (predicate, b1) = namedFunction ("is-variant:" ++ tag) current
            (result, b2) = fresh b1
            application = record "ApplicationTerm" [("id", MInt result), ("function", MInt predicate), ("arguments", MList [MInt object])]
            value = if tag == actual then 1 else 0
            constant = record "ConstantTerm" [("id", MInt result), ("kind", MInt 1), ("value", MInt value)]
        pure b2{literalTerms = constant : literalTerms b2, literalApps = application : literalApps b2}

enumVariantFunctions :: Map.Map Name M.TypeDecl -> Name -> Build -> Maybe (Integer, Integer, Integer, Build)
enumVariantFunctions types variant b0 = case find isConstructor (Map.toList types) of
    Just (familyName, M.EnumDecl _) ->
        let (family, b1) = namedFunction ("enum:" ++ familyName) b0
            (constructor, b2) = namedFunction ("ctor:" ++ variant) b1
            (predicate, b3) = namedFunction ("is-variant:" ++ variant) b2
         in Just (family, constructor, predicate, b3)
    _ -> Nothing
  where
    isConstructor (_, M.EnumDecl constructors) = any ((== variant) . fst) constructors
    isConstructor _ = False

operand :: M.Operand -> Build -> Maybe (MirValue, Build)
operand (M.Copy (M.Local n)) b = Just (record "ValueRef::Local" [("local", MInt (toInteger n))], b)
operand (M.Const c) b = do
    (i, b') <- literal c b
    pure (record "ValueRef::Term" [("term", MInt i)], b')
operand _ _ = Nothing

step :: String -> [(String, MirValue)] -> MirValue
step name = record ("ExecutionStep::" ++ name)

-- Evaluate proof expressions into temporary symbolic terms. Division and
-- remainder checks for zero; division also checks minInt / -1 before its
-- application is introduced.
proofOperand :: M.Env -> VariableProof -> Build -> Maybe ([MirValue], MirValue, Build)
proofOperand env (ATerm name) b = do
    o <- Map.lookup name env
    (v, b') <- operand o b
    pure ([], v, b')
proofOperand env (BVar name) b = proofOperand env (ATerm name) b
proofOperand _ (CTerm (VInt n)) b = do
    (v, b') <- operand (M.Const (M.CInt n)) b
    pure ([], v, b')
proofOperand _ (CTerm (VBool x)) b = do
    (v, b') <- operand (M.Const (M.CBool x)) b
    pure ([], v, b')
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct operation) _)) [arg]) b
    | operation `elem` [FromByte, Unsize, ArrayFrom, NewBox, UnBox, CloneOf] = proofOperand env arg b
proofOperand env (FApp (ATerm "array") arguments) b
    | builtinProofName env "array" b = proofOperand env (FApp (CTerm (builtinFunct NewArray)) arguments) b
proofOperand env (FApp (ATerm "Array::boxed") arguments) b
    | builtinProofName env "Array::boxed" b = proofOperand env (FApp (CTerm (builtinFunct NewBoxedArray)) arguments) b
proofOperand env (FApp (ATerm "Array::empty") arguments) b
    | builtinProofName env "Array::empty" b = proofOperand env (FApp (CTerm (builtinFunct NewEmptyArray)) arguments) b
proofOperand env (FApp (ATerm "Box::new") [arg]) b
    | builtinProofName env "Box::new" b = proofOperand env arg b
proofOperand env (FApp (ATerm "Box::unbox") [arg]) b
    | builtinProofName env "Box::unbox" b = proofOperand env arg b
proofOperand env (FApp (ATerm "clone") [arg]) b
    | builtinProofName env "clone" b = proofOperand env arg b
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct ToByte) _)) [arg]) b0 = do
    (prefix, value, b1) <- proofOperand env arg b0
    (zero, b2) <- operand (M.Const (M.CInt 0)) b1
    (limit, b3) <- operand (M.Const (M.CInt 256)) b2
    pure (prefix ++ [check 3 zero value, check 2 value limit], value, b3)
proofOperand env (FApp (ATerm "toInt") [arg]) b
    | builtinProofName env "toInt" b = proofOperand env arg b
proofOperand env (FApp (ATerm "toByte") [arg]) b0
    | builtinProofName env "toByte" b0 = proofOperand env (FApp (CTerm (builtinFunct ToByte)) [arg]) b0
proofOperand env (FApp (ATerm "size") [arg]) b
    | builtinProofName env "size" b = proofOperand env (FApp (CTerm (builtinFunct Size)) [arg]) b
proofOperand env (FApp (ATerm "get") [list, index]) b
    | builtinProofName env "get" b = proofOperand env (FApp (CTerm (builtinFunct Get)) [list, index]) b
proofOperand env (FApp (ATerm "push") [list, value]) b
    | builtinProofName env "push" b = proofOperand env (FApp (CTerm (builtinFunct Push)) [list, value]) b
proofOperand env (FApp (ATerm "set") [list, index, value]) b
    | builtinProofName env "set" b = proofOperand env (FApp (CTerm (builtinFunct Set)) [list, index, value]) b
proofOperand env (FApp (ATerm "first") [list]) b
    | builtinProofName env "first" b = proofOperand env (FApp (CTerm (builtinFunct First)) [list]) b
proofOperand env (FApp (ATerm "last") [list]) b
    | builtinProofName env "last" b = proofOperand env (FApp (CTerm (builtinFunct Last)) [list]) b
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Cast variant)) _)) [object]) b0 = do
    (prefix, value, b1) <- proofOperand env object b0
    (family, constructor, _, b2) <- enumVariantFunctions (proofTypes b1) variant b1
    let checked = step "CheckVariant"
            [("value", value), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool True)]
    pure (prefix ++ [checked], value, b2)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel relation)) _)) [left, right]) b0 = do
    (leftSteps, leftRef, b1) <- proofOperand env left b0
    (rightSteps, rightRef, b2) <- proofOperand env right b1
    let (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [ ("local", MInt local)
                                   , ("function", MInt (functionId (M.Compare relation)))
                                   , ("arguments", MList [leftRef, rightRef])
                                   ]
    pure (leftSteps ++ rightSteps ++ [apply], ref, b3)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct operation) _)) arguments) b0
    | Just function <- booleanFunctionId operation
    , length arguments == arity operation = do
        (prefix, refs, b1) <- foldM addArgument ([], [], b0) arguments
        let (i, b2) = fresh b1
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [ ("local", MInt local)
                                       , ("function", MInt function)
                                       , ("arguments", MList refs)
                                       ]
        pure (prefix ++ [apply], ref, b2)
  where
    addArgument (steps, refs, current) argument = do
        (prefix, value, next) <- proofOperand env argument current
        pure (steps ++ prefix, refs ++ [value], next)
    arity And = 2
    arity Or = 2
    arity Not = 1
    arity _ = 0
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Within) _)) [inner, outer]) b0 = do
    (innerSteps, innerRef, b1) <- proofOperand env inner b0
    (outerSteps, outerRef, b2) <- proofOperand env outer b1
    let (function, b3) = namedFunction "within" b2
        (i, b4) = fresh b3
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [innerRef, outerRef])]
    pure (innerSteps ++ outerSteps ++ [apply], ref, b4)
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
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Project variant field)) _)) [arg]) b0 = do
    (prefix, value, b1) <- proofOperand env arg b0
    let (function, b2) = namedFunction ("project:" ++ variant ++ ":" ++ field) b1
        (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList [value])]
    pure (prefix ++ [apply], ref, b3)
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) arguments) b0
    | length fields == length arguments = do
        (prefix, values, b1) <- foldM addArgument ([], [], b0) arguments
        let (function, b2) = namedFunction ("ctor:" ++ name) b1
            (i, b3) = fresh b2
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList values)]
        pure (prefix ++ [apply], ref, b3)
  where
    addArgument (steps, values, current) argument = do
        (prefix, value, next) <- proofOperand env argument current
        pure (steps ++ prefix, values ++ [value], next)
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
proofOperand env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct NewBoxedArray) _)) [lengthExpr, valueExpr]) b0 = do
    (lengthSteps, lengthRef, b1) <- proofOperand env lengthExpr b0
    (valueSteps, valueRef, b2) <- proofOperand env valueExpr b1
    let (i, b3) = fresh b2
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
    (steps, b4) <- arraySteps local lengthRef valueRef b3
    pure (lengthSteps ++ valueSteps ++ steps, ref, b4)
proofOperand _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct NewEmptyArray) _)) []) b0 = do
    let (i, b1) = fresh b0
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
    (steps, b2) <- emptyArraySteps local b1
    pure (steps, ref, b2)
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
    | builtinProofName env "pop" b = proofOperand env (FApp (CTerm (builtinFunct Pop)) [list]) b
proofOperand env (FApp (ATerm name) arguments) b0
    | Just targets <- proofFunctionTargets env name b0 = case targets of
        [target] | Map.member target (proofFunctions b0) -> proofFunctionCall env target arguments b0
        _ -> proofFunctionCallCandidates env targets arguments b0
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
    (defined, b4) <- case op of
        M.Div -> divisionDefined x y b3
        _ -> Just ([], b3)
    let (i, b5) = fresh b4
        local = negate i - 1
        ref = record "ValueRef::Local" [("local", MInt local)]
        apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (functionId op)), ("arguments", MList [x, y])]
    pure (leftSteps ++ rightSteps ++ requires ++ defined ++ [apply], ref, b5)
  where
    nonzero y b' = do
        (zero, b'') <- operand (M.Const (M.CInt 0)) b'
        pure ([check 1 y zero], b'')

proofOperand _ (CTerm value) b = do
    constant <- proofConstant value
    (ref, b') <- operand (M.Const constant) b
    pure ([], ref, b')
proofOperand _ _ _ = Nothing

proofFunctionTargets :: M.Env -> Name -> Build -> Maybe [Name]
proofFunctionTargets env name b = case Map.lookup name env of
    Just (M.Const (M.CFn target)) | Map.member target (proofFunctions b) -> Just [target]
    Just (M.Copy local) ->
        let staticTargets = do
                (blockId, statements) <- proofBlockContext b
                targets <- staticFunctionTargets (proofCaller b) blockId statements (M.Copy local)
                if not (null targets) && all (`Map.member` proofFunctions b) targets then Just (nub targets) else Nothing
         in staticTargets <|> functionTargetsForType (proofCandidateFunctions b) (proofCaller b) (M.Copy local)
    Just _ -> Nothing
    Nothing | Map.member name (proofFunctions b) -> Just [name]
    Nothing -> Nothing

builtinProofName :: M.Env -> Name -> Build -> Bool
builtinProofName env name b = case Map.lookup name env of
    Nothing -> True
    Just (M.Const (M.CFn target)) -> Map.notMember target (proofFunctions b)
    _ -> False

-- Calls in a proof use already-defined pure functions. Their input contract
-- runs as a mandatory nested check, so an enclosing assumed contract cannot
-- turn a callee's preconditions into assumptions.
proofFunctionCall :: M.Env -> Name -> [VariableProof] -> Build -> Maybe ([MirValue], MirValue, Build)
proofFunctionCall callerEnv name arguments b0 = do
    callee <- Map.lookup name (proofFunctions b0)
    if Set.member name (proofWorldReaders b0) || mayDiverge callee then Nothing else Just ()
    if length arguments == length (M.fnParams callee) && length (M.fnSizeParams callee) <= length arguments then Just () else Nothing
    let sizeArguments = drop (length arguments - length (M.fnSizeParams callee)) arguments
    if all (validProofSizeArgument callerEnv (proofCaller b0) b0) sizeArguments then Just () else Nothing
    sizeSubstitutions <- proofSizeSubstitutions callerEnv (proofCaller b0) b0 callee arguments
    returnType <- M.fnReturns callee
    (argumentSteps, snapshots, b1) <- foldM addArgument ([], [], b0) arguments
    let sizeSnapshots = zip (map fst (drop (length snapshots - length sizeSubstitutions) snapshots)) (map snd sizeSubstitutions)
        b1s = b1{proofSizeValues = Map.union (Map.fromList sizeSnapshots) (proofSizeValues b1)}
    let params = M.fnParams callee
        bindings = Map.fromList (zip params [local | (local, _) <- snapshots])
        argumentRefs = [record "ValueRef::Local" [("local", MInt (toInteger number))] | (M.Local number, _) <- snapshots]
        remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
        remap constant@(M.Const _) = Just constant
        remap _ = Nothing
        sizeBindings = Map.fromList (mapMaybe (sizeBinding callerEnv) sizeSubstitutions)
        env = Map.union sizeBindings (Map.mapMaybe remap (M.specEnv (M.fnSpec callee)))
    (sizeChecks, b1a) <- sizeParameterSteps False callee (map fst snapshots) b1s
    (inputChecks, b2, definitions) <- contractStepsWith False env Map.empty (M.specRequires (M.fnSpec callee)) b1a
    (parameterResults, parameterSteps, b3) <- foldM (addReassignedParameter callee argumentRefs sizeSubstitutions)
        (Map.empty, [], b2) (reassignedParameterLocals callee)
    let (callFunction, b4) = namedFunction ("proof-call:" ++ name) b3
        (i, b5) = fresh b4
    if i <= toInteger (maxBound :: Int) then Just () else Nothing
    let resultLocal = M.Local (negate (fromInteger i) - 1)
        resultNumber = case resultLocal of M.Local number -> number
        resultRef = record "ValueRef::Local" [("local", MInt (toInteger resultNumber))]
        apply = step "ApplyFresh" [("local", MInt (toInteger resultNumber)), ("function", MInt callFunction), ("arguments", MList argumentRefs)]
    let instantiatedReturnType = substSizes sizeSubstitutions returnType
        caller = proofCaller b5
    (typeFacts, b6) <- if all (`elem` M.fnSizeParams caller) (sizeParametersInType instantiatedReturnType)
        then typeStepsFor (proofTypes b5) (proofGenerics b5) (proofInvariants b5) caller instantiatedReturnType resultLocal b5
        else Just ([], b5)
    let resultEnv = Map.insert "return" (M.Copy resultLocal) (Map.union parameterResults env)
    mandatoryChecks <- mandatoryCheckSteps (sizeChecks ++ inputChecks)
    (outputFacts, b7, _) <- contractStepsWith True resultEnv definitions (M.specEnsures (M.fnSpec callee)) b6
    pure (argumentSteps ++ [save | (_, save) <- snapshots] ++ mandatoryChecks ++ parameterSteps ++ [apply] ++ typeFacts ++ outputFacts, resultRef, b7)
  where
    sizeBinding currentEnv (sizeName, size) = case size of
        SizeConst value | inIntRange value -> Just (sizeName, M.Const (M.CInt value))
        SizeParam source -> fmap (\value -> (sizeName, value)) (Map.lookup source currentEnv)
        _ -> Nothing
    reassignedParameterLocals target =
        [ (local, sourceName)
        | local <- M.fnParams target
        , reassignsParameter target local
        , Just declaration <- [Map.lookup local (M.fnLocals target)]
        , Just sourceName <- [M.localName declaration]
        ]
    reassignsParameter target local =
        any (writesParameter local) (concatMap M.blockStatements (Map.elems (M.fnBlocks target)))
            || any (writesParameterTerminator local) (map M.blockTerminator (Map.elems (M.fnBlocks target)))
    writesParameter local (M.Assign written _) = local == written
    writesParameter local (M.Peek written _) = local == written
    writesParameter local (M.Drop written) = local == written
    writesParameter _ _ = False
    writesParameterTerminator local (M.Call _ _ written _) = local == written
    writesParameterTerminator _ _ = False
    addReassignedParameter target argumentsRefs sizeSubstitutions (results, steps, current) (parameter, sourceName) = do
        declaration <- Map.lookup parameter (M.fnLocals target)
        let (function, next) = namedFunction
                ("proof-call-result-param:" ++ name ++ ":" ++ sourceName ++ ":" ++ show (nextTerm current)) current
            (i, next') = fresh next
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            created = step "ApplyFresh" [("local", MInt (toInteger number)), ("function", MInt function), ("arguments", MList argumentsRefs)]
        let instantiatedType = substSizes sizeSubstitutions (M.localType declaration)
            caller = proofCaller next'
        (typeFacts, next'') <- if all (`elem` M.fnSizeParams caller) (sizeParametersInType instantiatedType)
            then typeStepsFor (proofTypes next') (proofGenerics next') (proofInvariants next') caller instantiatedType local next'
            else Just ([], next')
        pure (Map.insert sourceName (M.Copy local) results, steps ++ [created] ++ typeFacts, next'')
    addArgument (steps, saved, current) argument = do
        (prefix, value, next) <- proofOperand callerEnv argument current
        let (i, next') = fresh next
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            save = step "Assign" [("local", MInt (toInteger number)), ("value", value)]
        pure (steps ++ prefix, saved ++ [(local, save)], next')

-- A function value with several possible targets is usable only when every
-- candidate has the same callable signature. This includes targets recovered
-- from control-flow joins and the closed-world set for an unresolved parameter.
-- Preconditions are checked for every target; only the common output prefix is
-- retained, preserving any proof-variable definitions those steps depend on.
proofFunctionCallCandidates :: M.Env -> [Name] -> [VariableProof] -> Build -> Maybe ([MirValue], MirValue, Build)
proofFunctionCallCandidates callerEnv names arguments b0 = do
    if not (null names) then Just () else Nothing
    callees <- mapM (`Map.lookup` proofCandidateFunctions b0) names
    first <- case callees of
        fn : _ -> Just fn
        [] -> Nothing
    firstSignature <- signature first
    if all ((== Just firstSignature) . signature) (drop 1 callees) then Just () else Nothing
    if length arguments == length (M.fnParams first) then Just () else Nothing
    if any (\callee -> Set.member (M.fnName callee) (proofWorldReaders b0) || mayDiverge callee) callees then Nothing else Just ()
    if all (validProofSizeArguments callerEnv (proofCaller b0) b0 arguments) callees then Just () else Nothing
    sizeSubstitutions <- proofSizeSubstitutions callerEnv (proofCaller b0) b0 first arguments
    returnType <- M.fnReturns first
    (argumentSteps, snapshots, b1) <- foldM addArgument ([], [], b0) arguments
    let sizeSnapshots = zip (map fst (drop (length snapshots - length sizeSubstitutions) snapshots)) (map snd sizeSubstitutions)
        b1s = b1{proofSizeValues = Map.union (Map.fromList sizeSnapshots) (proofSizeValues b1)}
    let argumentRefs = [record "ValueRef::Local" [("local", MInt (toInteger number))] | (M.Local number, _) <- snapshots]
    (inputChecks, b2, hasInputDefinitions) <- foldM (checkCandidate snapshots)
        ([], b1s, False) callees
    let (callFunction, b3) = namedFunction
            ("proof-indirect-call:" ++ M.fnName (proofCaller b0) ++ ":" ++ show (nextTerm b2)) b2
        (i, b4) = fresh b3
    if i <= toInteger (maxBound :: Int) then Just () else Nothing
    let resultLocal = M.Local (negate (fromInteger i) - 1)
        M.Local resultNumber = resultLocal
        resultRef = record "ValueRef::Local" [("local", MInt (toInteger resultNumber))]
        apply = step "ApplyFresh" [("local", MInt (toInteger resultNumber)), ("function", MInt callFunction), ("arguments", MList argumentRefs)]
    let instantiatedReturnType = substSizes sizeSubstitutions returnType
        caller = proofCaller b4
    (typeFacts, b5) <- if all (`elem` M.fnSizeParams caller) (sizeParametersInType instantiatedReturnType)
        then typeStepsFor (proofTypes b4) (proofGenerics b4) (proofInvariants b4) caller instantiatedReturnType resultLocal b4
        else Just ([], b4)
    sharedOutputs <- if hasInputDefinitions || any hasReassignedParameters callees
        then Just ([], b5)
        else commonOutputs snapshots resultLocal b5 callees
    mandatoryChecks <- mandatoryCheckSteps inputChecks
    let (outputFacts, b6) = sharedOutputs
    pure (argumentSteps ++ [save | (_, save) <- snapshots] ++ mandatoryChecks ++ [apply] ++ typeFacts ++ outputFacts, resultRef, b6)
  where
    signature callee = do
        parameterTypes <- mapM (\local -> M.localType <$> Map.lookup local (M.fnLocals callee)) (M.fnParams callee)
        returnType <- M.fnReturns callee
        pure (parameterTypes, returnType, length (M.fnSizeParams callee))
    addArgument (steps, saved, current) argument = do
        (prefix, value, next) <- proofOperand callerEnv argument current
        let (i, next') = fresh next
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            save = step "Assign" [("local", MInt (toInteger number)), ("value", value)]
        pure (steps ++ prefix, saved ++ [(local, save)], next')
    checkCandidate snapshots (steps, current, hasDefinitions) callee = do
        let params = M.fnParams callee
            bindings = Map.fromList (zip params [local | (local, _) <- snapshots])
            remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
            remap constant@(M.Const _) = Just constant
            remap _ = Nothing
            env = Map.mapMaybe remap (M.specEnv (M.fnSpec callee))
            requires = M.specRequires (M.fnSpec callee)
        (sizeChecks, withSizes) <- sizeParameterSteps False callee (map fst snapshots) current
        (checks, next, _) <- contractStepsWith False env Map.empty requires withSizes
        pure (steps ++ sizeChecks ++ checks, next, hasDefinitions || any isDefinition requires)
    isDefinition (AssignProofVar _ _) = True
    isDefinition _ = False
    hasReassignedParameters callee = any (reassigns callee) (M.fnParams callee)
    reassigns callee local =
        any (writes local) (concatMap M.blockStatements (Map.elems (M.fnBlocks callee)))
            || any (writesTerminator local) (map M.blockTerminator (Map.elems (M.fnBlocks callee)))
    writes local (M.Assign written _) = local == written
    writes local (M.Peek written _) = local == written
    writes local (M.Drop written) = local == written
    writes _ _ = False
    writesTerminator local (M.Call _ _ written _) = local == written
    writesTerminator _ _ = False
    commonOutputs snapshots destination current callees = do
        candidates <- mapM (candidateOutputs snapshots destination current) callees
        case candidates of
            [] -> Just ([], current)
            (firstSteps, firstBuild) : rest ->
                Just (commonPrefix firstSteps (map fst rest), firstBuild)
      where
        commonPrefix [] _ = []
        commonPrefix (candidate : candidates') otherSteps
            | all (\steps -> take 1 steps == [candidate]) otherSteps =
                candidate : commonPrefix candidates' (map dropOne otherSteps)
            | otherwise = []
        dropOne (_ : rest) = rest
        dropOne [] = []
    candidateOutputs snapshots destination current callee = do
        let bindings = Map.fromList (zip (M.fnParams callee) [local | (local, _) <- snapshots])
            remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
            remap constant@(M.Const _) = Just constant
            remap _ = Nothing
            env = Map.mapMaybe remap (M.specEnv (M.fnSpec callee))
            resultEnv = Map.insert "return" (M.Copy destination) env
        (steps, next, _) <- contractStepsWith True resultEnv Map.empty (M.specEnsures (M.fnSpec callee)) current
        pure (steps, next)

validProofSizeArguments :: M.Env -> M.Function -> Build -> [VariableProof] -> M.Function -> Bool
validProofSizeArguments env caller build arguments callee =
    let sizeArguments = drop (length arguments - length (M.fnSizeParams callee)) arguments
     in length arguments >= length (M.fnSizeParams callee)
            && all (validProofSizeArgument env caller build) sizeArguments

mandatoryCheckSteps :: [MirValue] -> Maybe [MirValue]
mandatoryCheckSteps = fmap concat . mapM convert
  where
    convert step'@(MData "ExecutionStep::Assign" _) = Just [step']
    convert step'@(MData "ExecutionStep::ApplyFresh" _) = Just [step']
    convert (MData "ExecutionStep::Check" fields) = Just [MData "ExecutionStep::CheckMandatory" fields]
    convert step'@(MData "ExecutionStep::CheckMandatory" _) = Just [step']
    convert _ = Nothing

validProofSizeArgument :: M.Env -> M.Function -> Build -> VariableProof -> Bool
validProofSizeArgument env caller build argument = maybe False (const True) (proofSizeArgumentIn env caller build argument)

proofSizeArgument :: M.Env -> M.Function -> VariableProof -> Maybe Size
proofSizeArgument _ _ (CTerm (VInt value)) = Just (SizeConst value)
proofSizeArgument env caller (ATerm name) = case Map.lookup name env of
    Just (M.Const (M.CInt value)) -> Just (SizeConst value)
    Just (M.Copy local)
        | local `elem` sizeParams
        , Just localName <- M.localName =<< Map.lookup local (M.fnLocals caller)
        , localName `elem` M.fnSizeParams caller -> Just (SizeParam localName)
    _ -> Nothing
  where
    sizeParams = drop (length (M.fnParams caller) - length (M.fnSizeParams caller)) (M.fnParams caller)
proofSizeArgument env caller (BVar name) = proofSizeArgument env caller (ATerm name)
proofSizeArgument _ _ _ = Nothing

proofSizeArgumentIn :: M.Env -> M.Function -> Build -> VariableProof -> Maybe Size
proofSizeArgumentIn env caller build argument = proofSizeArgument env caller argument <|> tracked argument
  where
    tracked (ATerm name) = case Map.lookup name env of
        Just (M.Copy local) -> Map.lookup local (proofSizeValues build)
        _ -> Nothing
    tracked (BVar name) = tracked (ATerm name)
    tracked _ = Nothing

proofSizeSubstitutions :: M.Env -> M.Function -> Build -> M.Function -> [VariableProof] -> Maybe [(Variable, Size)]
proofSizeSubstitutions env caller build callee arguments =
    let sizeArguments = drop (length arguments - length (M.fnSizeParams callee)) arguments
     in if length arguments < length (M.fnSizeParams callee)
            then Nothing
            else mapM (substituteSize env caller build) (zip (M.fnSizeParams callee) sizeArguments)
  where
    substituteSize currentEnv currentCaller currentBuild (name, argument) = (,) name <$> proofSizeArgumentIn currentEnv currentCaller currentBuild argument

sizeParametersInType :: Type -> [Name]
sizeParametersInType valueType = case valueType of
    TList element -> sizeParametersInType element
    TArrayOf element (SizeParam name) -> name : sizeParametersInType element
    TArrayOf element _ -> sizeParametersInType element
    TBox inner -> sizeParametersInType inner
    TRef inner -> sizeParametersInType inner
    TFn arguments result -> concatMap sizeParametersInType (result : arguments)
    TForall sizes _ inner -> filter (`notElem` sizes) (sizeParametersInType inner)
    TNamed name -> case instanceOf name of
        Just (_, arguments) -> concatMap sizeArgumentParameters arguments
        Nothing -> []
    _ -> []
  where
    sizeArgumentParameters (ArgSize (SizeParam name)) = [name]
    sizeArgumentParameters (ArgType inner) = sizeParametersInType inner
    sizeArgumentParameters _ = []

proofConstant :: Value -> Maybe M.Constant
proofConstant (VInt value) = Just (M.CInt value)
proofConstant (VBool value) = Just (M.CBool value)
proofConstant (VList values) = M.CList <$> mapM proofConstant values
proofConstant (VData name fields) = M.CData name <$> mapM (\(field, value) -> (,) field <$> proofConstant value) fields
proofConstant _ = Nothing

check :: Integer -> MirValue -> MirValue -> MirValue
check relation a b = step "Check" [("relation", MInt relation), ("left", a), ("right", b)]

withinFact :: M.Local -> M.Local -> Build -> Maybe ([MirValue], Build)
withinFact (M.Local inner) (M.Local outer) b0 = do
    let (function, b1) = namedFunction "within" b0
        (i, b2) = fresh b1
        local = negate i - 1
        result = record "ValueRef::Local" [("local", MInt local)]
    (trueValue, b3) <- operand (M.Const (M.CBool True)) b2
    let application = step "ApplyFresh"
            [("local", MInt local), ("function", MInt function), ("arguments", MList [
                record "ValueRef::Local" [("local", MInt (toInteger inner))],
                record "ValueRef::Local" [("local", MInt (toInteger outer))]
                ])]
        known = step "Assume" [("relation", MInt 0), ("left", result), ("right", trueValue)]
    pure ([application, known], b3)

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

emptyArraySteps :: Integer -> Build -> Maybe ([MirValue], Build)
emptyArraySteps dest b0 = do
    (zero, b1) <- operand (M.Const (M.CInt 0)) b0
    let (i, b2) = fresh b1
        sizeLocal = negate i - 1
        resultRef = record "ValueRef::Local" [("local", MInt dest)]
        sizeRef = record "ValueRef::Local" [("local", MInt sizeLocal)]
        make = step "ApplyFresh" [("local", MInt dest), ("function", MInt (-15)), ("arguments", MList [])]
        size = step "ApplyFresh" [("local", MInt sizeLocal), ("function", MInt (-13)), ("arguments", MList [resultRef])]
        known = step "Assume" [("relation", MInt 0), ("left", sizeRef), ("right", zero)]
    pure ([make, size, known], b2)

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

-- LLVM division traps for zero and for minInt / -1. Keep both conditions in
-- the proof trace: callers must establish them, while a function contract can
-- assume the definedness of its precondition before using its quotient.
divisionDefined :: MirValue -> MirValue -> Build -> Maybe ([MirValue], Build)
divisionDefined dividend divisor b0 = do
    (minIntRef, b1) <- operand (M.Const (M.CInt (toInteger (minBound :: Int)))) b0
    (minusOne, b2) <- operand (M.Const (M.CInt (-1))) b1
    (trueValue, b3) <- operand (M.Const (M.CBool True)) b2
    let (dividendIsMinimum, dividendLocal, b4) = applyFresh (functionId (M.Compare Eq)) [dividend, minIntRef] b3
        (divisorIsMinusOne, divisorLocal, b5) = applyFresh (functionId (M.Compare Eq)) [divisor, minusOne] b4
    andFunction <- booleanFunctionId And
    notFunction <- booleanFunctionId Not
    let (overflows, overflowLocal, b6) = applyFresh andFunction [dividendIsMinimum, divisorIsMinusOne] b5
        (safe, safeLocal, b7) = applyFresh notFunction [overflows] b6
    pure
        ( [ dividendLocal
          , divisorLocal
          , overflowLocal
          , safeLocal
          , check 0 safe trueValue
          ]
        , b7
        )
  where
    applyFresh function arguments current =
        let (i, next) = fresh current
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            application = step "ApplyFresh" [("local", MInt local), ("function", MInt function), ("arguments", MList arguments)]
         in (ref, application, next)

proofCheck :: M.Env -> VariableProof -> Build -> Maybe ([MirValue], [MirValue], Build)
proofCheck env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct And) _)) [left, right]) b0 = do
    (leftPrefix, leftChecks, b1) <- proofCheck env left b0
    (rightPrefix, rightChecks, b2) <- proofCheck env right b1
    pure (leftPrefix ++ rightPrefix, leftChecks ++ rightChecks, b2)
proofCheck env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Not) _)) [value]) b0 =
    proofCheck env (negateBoolean value) b0
proofCheck env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variant)) _)) [object]) b0 =
    checkVariantProof env variant object True b0
proofCheck env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variant)) _)) [object],
    CTerm (VBool matches)]) b0 = checkVariantProof env variant object matches b0
proofCheck env (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [
    CTerm (VBool matches),
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variant)) _)) [object]]) b0 = checkVariantProof env variant object matches b0
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
    pure (leftSteps ++ rightSteps, [check kind left right], b2)
proofCheck env proof@(FApp (CTerm (VFunct _ _ _ (BuiltinFunct Within) _)) [_inner, _outer]) b0 = do
    (prefix, result, b1) <- proofOperand env proof b0
    (trueValue, b2) <- operand (M.Const (M.CBool True)) b1
    pure (prefix, [check 0 result trueValue], b2)

proofCheck env (Forall index guards conclusion) b0
    | forallBodyEntailed guards conclusion = Just ([], [], b0)
    | otherwise = case finiteForallValues index guards of
        Just values -> do
            (prefix, checks, b1) <- foldM checkInstance ([], [], b0) values
            pure (prefix, checks, b1)
        Nothing -> case dynamicForallBounds index guards of
            Just (lower, upper) -> do
                (lowerPrefix, lowerRef, b1) <- proofOperand env lower b0
                (upperPrefix, upperRef, b2) <- proofOperand env upper b1
                let (i, b3) = fresh b2
                    local = negate i - 1
                    binder = M.Local (fromInteger local)
                if local < toInteger (minBound :: Int) then Nothing else Just ()
                (bodyPrefix, bodyChecks, b4) <- proofCheck (Map.insert index (M.Copy binder) env) conclusion b3
                let forallStep = step "ValidateForall"
                        [ ("local", MInt local)
                        , ("lower", lowerRef)
                        , ("upper", upperRef)
                        , ("checks", MList (bodyPrefix ++ bodyChecks))
                        , ("assume", MBool False)
                        ]
                pure (lowerPrefix ++ upperPrefix, [forallStep], b4)
            Nothing -> symbolicForallCheck env index guards conclusion b0
  where
    checkInstance (prefix, checks, current) value = do
        (nextPrefix, nextChecks, next) <- proofCheck env (substituteBound index (CTerm (VInt value)) conclusion) current
        pure (prefix ++ nextPrefix, checks ++ nextChecks, next)
proofCheck env proof b0 = do
    (prefix, result, b1) <- proofOperand env proof b0
    (trueValue, b2) <- operand (M.Const (M.CBool True)) b1
    pure (prefix, [check 0 result trueValue], b2)

checkVariantProof :: M.Env -> Name -> VariableProof -> Bool -> Build -> Maybe ([MirValue], [MirValue], Build)
checkVariantProof env variant object matches b0 = do
    (prefix, value, b1) <- proofOperand env object b0
    (family, constructor, _, b2) <- enumVariantFunctions (proofTypes b1) variant b1
    let checked = step "CheckVariant"
            [ ("value", value)
            , ("family", MInt family)
            , ("constructor", MInt constructor)
            , ("matches", MBool matches)
            ]
    pure (prefix, [checked], b2)

negateBoolean :: VariableProof -> VariableProof
negateBoolean (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel relation)) _)) [left, right]) =
    FApp (CTerm (builtinFunct (Rel (negateRelation relation)))) [left, right]
negateBoolean proof = FApp (CTerm (builtinFunct (Rel Eq))) [proof, CTerm (VBool False)]

negateRelation :: Rel -> Rel
negateRelation relation = case relation of
    Eq -> NotEq
    NotEq -> Eq
    Lt -> GtEq
    Gt -> LtEq
    LtEq -> Gt
    GtEq -> Lt

-- The first-order engine has no quantifier node yet. For a small, fully
-- literal integer interval we can replace a forall with all of its instances;
-- open or unbounded ranges remain unsupported.
finiteForallValues :: Variable -> [VariableProof] -> Maybe [Integer]
finiteForallValues index guards = do
    comparisons <- mapM (boundComparison index) guards
    if null comparisons then Nothing else Just ()
    let lowerBounds = mapMaybe lowerBound comparisons
        upperBounds = mapMaybe upperBound comparisons
    if null lowerBounds || null upperBounds then Nothing else Just ()
    let lower = maximum lowerBounds
        upper = minimum upperBounds
    if not (inIntRange lower && inIntRange upper) || upper - lower > 256 then Nothing else Just ()
    pure [value | value <- [lower .. upper - 1], all (holdsAt value) comparisons]
  where
    lowerBound (relation, bound) = case relation of
        GtEq -> Just bound
        Gt | inIntRange (bound + 1) -> Just (bound + 1)
        Eq -> Just bound
        _ -> Nothing
    upperBound (relation, bound) = case relation of
        Lt -> Just bound
        LtEq | inIntRange (bound + 1) -> Just (bound + 1)
        Eq | inIntRange (bound + 1) -> Just (bound + 1)
        _ -> Nothing
    holdsAt value (relation, bound) = case relation of
        Eq -> value == bound
        NotEq -> value /= bound
        Lt -> value < bound
        LtEq -> value <= bound
        Gt -> value > bound
        GtEq -> value >= bound

boundComparison :: Variable -> VariableProof -> Maybe (Rel, Integer)
boundComparison index (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel relation)) _)) [left, right]) = case (left, right) of
    (BVar bound, CTerm (VInt value)) | bound == index -> Just (relation, value)
    (CTerm (VInt value), BVar bound) | bound == index -> Just (reverseRelation relation, value)
    _ -> Nothing
  where
    reverseRelation Lt = Gt
    reverseRelation Gt = Lt
    reverseRelation LtEq = GtEq
    reverseRelation GtEq = LtEq
    reverseRelation other = other
boundComparison _ _ = Nothing

-- A range can also be bounded by values computed in the current MIR state.
-- The checker resolves these values at the point the forall is validated and
-- enumerates only when the resulting interval is small and concrete.
dynamicForallBounds :: Variable -> [VariableProof] -> Maybe (VariableProof, VariableProof)
dynamicForallBounds index [lowerGuard, upperGuard] = do
    lower <- rangeLower index lowerGuard
    upper <- rangeUpper index upperGuard
    pure (lower, upper)
dynamicForallBounds _ _ = Nothing

forallWitnesses :: Variable -> [VariableProof] -> [VariableProof]
forallWitnesses index guards = nub (mapMaybe (rangeEquality index) guards ++ mapMaybe (rangeLower index) guards)

forallBoundRelation :: Variable -> VariableProof -> Maybe (Integer, VariableProof, VariableProof)
forallBoundRelation index (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel relation)) _)) [rawLeft, rawRight]) =
    let (code, left, right) = case relation of
            Eq -> (0, rawLeft, rawRight)
            NotEq -> (1, rawLeft, rawRight)
            Lt -> (2, rawLeft, rawRight)
            LtEq -> (3, rawLeft, rawRight)
            Gt -> (2, rawRight, rawLeft)
            GtEq -> (3, rawRight, rawLeft)
     in case (left, right) of
            (BVar bound, other) | bound == index && not (proofHasBound index other) -> Just (code, left, right)
            (other, BVar bound) | bound == index && not (proofHasBound index other) -> Just (code, left, right)
            _ -> Nothing
forallBoundRelation _ _ = Nothing

rangeEquality :: Variable -> VariableProof -> Maybe VariableProof
rangeEquality index (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [BVar bound, value])
    | bound == index && not (proofHasBound index value) = Just value
rangeEquality index (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Eq)) _)) [value, BVar bound])
    | bound == index && not (proofHasBound index value) = Just value
rangeEquality _ _ = Nothing

rangeLower :: Variable -> VariableProof -> Maybe VariableProof
rangeLower index (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel relation)) _)) [left, right]) = case (relation, left, right) of
    (GtEq, BVar bound, lower) | bound == index && not (proofHasBound index lower) -> Just lower
    (LtEq, lower, BVar bound) | bound == index && not (proofHasBound index lower) -> Just lower
    _ -> Nothing
rangeLower _ _ = Nothing

rangeUpper :: Variable -> VariableProof -> Maybe VariableProof
rangeUpper index (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Lt)) _)) [BVar bound, upper])
    | bound == index && not (proofHasBound index upper) = Just upper
rangeUpper _ _ = Nothing

proofHasBound :: Variable -> VariableProof -> Bool
proofHasBound index proof = case proof of
    BVar name -> name == index
    FApp function arguments -> proofHasBound index function || any (proofHasBound index) arguments
    Forall name guards conclusion -> name /= index && any (proofHasBound index) (guards ++ [conclusion])
    _ -> False

forallBodyEntailed :: [VariableProof] -> VariableProof -> Bool
forallBodyEntailed guards (FApp (CTerm (VFunct _ _ _ (BuiltinFunct And) _)) [left, right]) =
    forallBodyEntailed guards left && forallBodyEntailed guards right
forallBodyEntailed guards conclusion = any (`guardEntails` conclusion) guards

guardEntails :: VariableProof -> VariableProof -> Bool
guardEntails guard conclusion = case (relationProof guard, relationProof conclusion) of
    (Just (guardRelation, guardLeft, guardRight), Just (goalRelation, goalLeft, goalRight)) ->
        guardLeft == goalLeft && guardRight == goalRight && relationEntails guardRelation goalRelation
    _ -> guard == conclusion

relationProof :: VariableProof -> Maybe (Rel, VariableProof, VariableProof)
relationProof (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel relation)) _)) [left, right]) =
    let (normalized, normalizedLeft, normalizedRight) = case relation of
            Gt -> (Lt, right, left)
            GtEq -> (LtEq, right, left)
            _ -> (relation, left, right)
     in Just (normalized, normalizedLeft, normalizedRight)
relationProof _ = Nothing

relationEntails :: Rel -> Rel -> Bool
relationEntails given goal = given == goal
    || case (given, goal) of
        (Lt, LtEq) -> True
        (Eq, LtEq) -> True
        (Eq, GtEq) -> True
        _ -> False

symbolicForallCheck :: M.Env -> Variable -> [VariableProof] -> VariableProof -> Build -> Maybe ([MirValue], [MirValue], Build)
symbolicForallCheck env index guards conclusion b0 = do
    let (i, b1) = fresh b0
        local = negate i - 1
        binder = M.Local (fromInteger local)
        scoped = Map.insert index (M.Copy binder) env
    if local < toInteger (minBound :: Int) then Nothing else Just ()
    (assumptions, b2) <- foldM (addGuard scoped) ([], b1) guards
    (bodyPrefix, checks, b3) <- proofCheck scoped conclusion b2
    let forallStep = step "ValidateForallSymbolic"
            [ ("local", MInt local)
            , ("assumptions", MList assumptions)
            , ("checks", MList (bodyPrefix ++ checks))
            ]
    pure ([], [forallStep], b3)
  where
    addGuard scoped (steps, current) guard = do
        (prefix, checks, next) <- proofCheck scoped guard current
        if all safePrefix prefix then Just () else Nothing
        pure (steps ++ prefix ++ checks, next)
    safePrefix (MData "ExecutionStep::ApplyFresh" _) = True
    safePrefix _ = False

substituteBound :: Variable -> VariableProof -> VariableProof -> VariableProof
substituteBound index replacement proof = case proof of
    BVar name | name == index -> replacement
    FApp function arguments -> FApp (substituteBound index replacement function) (map (substituteBound index replacement) arguments)
    Forall name guards conclusion | name == index -> Forall name guards conclusion
    Forall name guards conclusion -> Forall name (map (substituteBound index replacement) guards) (substituteBound index replacement conclusion)
    _ -> proof

-- Evaluate total expressions before assuming a clause. The reference can
-- assume partial expressions without proving their safety, so decline those
-- rather than treating an unproved safety check as a validation failure.
contractSteps :: Bool -> M.Env -> [ValidationStatement] -> Build -> Maybe ([MirValue], Build)
contractSteps assume env clauses b0 = do
    (steps, b1, _) <- contractStepsWith assume env Map.empty clauses b0
    pure (steps, b1)

-- Keep proof-variable snapshots available to later contract phases, as the
-- reference validator carries them in its proof state from requires to ensures.
contractStepsWith :: Bool -> M.Env -> Map.Map Variable M.Operand -> [ValidationStatement] -> Build -> Maybe ([MirValue], Build, Map.Map Variable M.Operand)
contractStepsWith assume env initialDefinitions clauses b0 =
    foldM addTracked ([], b0, initialDefinitions) clauses
  where
    addTracked = add
    add (steps, b, definitions) (AssignProofVar name expression) = do
        (prefix, value, b1) <- proofOperand (Map.union definitions env) (exprToProof expression) b
        let (i, b2) = fresh b1
            local = negate i - 1
        if local < toInteger (minBound :: Int) then Nothing else Just ()
        let snapshot = step "Assign" [("local", MInt local), ("value", value)]
            definitions' = Map.insert name (M.Copy (M.Local (fromInteger local))) definitions
        pure (steps ++ prefix ++ [snapshot], b2, definitions')
    add (steps, b, definitions) (ProofAssert proof)
        | assume = do
            (assumptions, b') <- assumedProof (Map.union definitions env) proof b
            pure (steps ++ assumptions, b', definitions)
        | otherwise = do
            (prefix, checked, b') <- proofCheck (Map.union definitions env) proof b
            pure (steps ++ prefix ++ checked, b', definitions)
    -- Rewrites in an assumed contract are proof-search hints; the reference
    -- validator assumes its assertions but does not execute these rewrites.
    add (steps, b, definitions) (Rewrite _) | assume = Just (steps, b, definitions)
    add (steps, b, definitions) (Rewrite (UserRewrite name arguments)) = do
        (rewriteSteps, b') <- axiomRewrite (Map.union definitions env) name arguments b
        pure (steps ++ rewriteSteps, b', definitions)
    -- These primitive rewrites add consequences already handled by the
    -- validator's equality closure and builtin facts. Omitting the rewrite
    -- can make a proof less complete, but cannot introduce an assumption.
    add (steps, b, definitions) (Rewrite (Refl _)) = Just (steps, b, definitions)
    add (steps, b, definitions) (Rewrite (Eval _)) = Just (steps, b, definitions)
    add (steps, b, definitions) (Rewrite EvalAll) = Just (steps, b, definitions)
    add (steps, b, definitions) (Rewrite (CheckRel proof)) = do
        (prefix, checked, b') <- proofCheck (Map.union definitions env) proof b
        assumed <- mapM checkedAssumption checked
        pure (steps ++ prefix ++ checked ++ assumed, b', definitions)
    add (steps, b, definitions) (Rewrite (CheckGtZero proof)) = do
        (prefix, value, b1) <- proofOperand (Map.union definitions env) proof b
        (zero, b2) <- operand (M.Const (M.CInt 0)) b1
        let checked = check 2 zero value
        assumed <- checkedAssumption checked
        pure (steps ++ prefix ++ [checked, assumed], b2, definitions)
    assumeDefinedness checkStep@(MData "ExecutionStep::Check" _) = checkedAssumption checkStep
    assumeDefinedness checkStep@(MData "ExecutionStep::CheckVariant" _) = checkedAssumption checkStep
    assumeDefinedness step' = Just step'
    assumedProof proofEnv (Forall index guards conclusion) current = case finiteForallValues index guards of
        Just values -> foldM
            (\(accumulated, next) value -> do
                (more, after) <- assumedProof proofEnv (substituteBound index (CTerm (VInt value)) conclusion) next
                pure (accumulated ++ more, after))
            ([], current)
            values
        Nothing -> case (dynamicForallBounds index guards, forallBoundRelation index conclusion) of
            (Just (lower, upper), Just (relation, left, right)) ->
                encodeForallRelation proofEnv index lower upper relation left right current
            _ -> do
                witnesses <- case forallWitnesses index guards of
                    [] -> Nothing
                    candidates -> Just candidates
                (witnessRefs, afterWitnesses) <- foldM (encodeWitness proofEnv) ([], current) witnesses
                let (i, afterFresh) = fresh afterWitnesses
                    local = negate i - 1
                    binder = M.Local (fromInteger local)
                    scoped = Map.insert index (M.Copy binder) proofEnv
                if local < toInteger (minBound :: Int) then Nothing else Just ()
                (guardSteps, afterGuards) <- foldM (encodeWitnessGuard scoped) ([], afterFresh) guards
                if all supportedWitnessGuardStep guardSteps then Just () else Nothing
                (bodyPrefix, bodyChecks, afterBody) <- proofCheck scoped conclusion afterGuards
                if all supportedWitnessGuardStep (bodyPrefix ++ bodyChecks) then Just () else Nothing
                let conditional = step "AssumeForallWitness"
                        [ ("local", MInt local)
                        , ("witnesses", MList witnessRefs)
                        , ("guards", MList guardSteps)
                        , ("assumptions", MList (bodyPrefix ++ bodyChecks))
                        ]
                pure ([conditional], afterBody)
    assumedProof proofEnv (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variant)) _)) [object]) current = do
        (prefix, value, b1) <- proofOperand proofEnv object current
        (family, constructor, _, b2) <- enumVariantFunctions (proofTypes b1) variant b1
        encodedPrefix <- mapM assumeDefinedness prefix
        let known = step "AssumeVariant"
                [("value", value), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool True)]
        pure (encodedPrefix ++ [known], b2)
    assumedProof proofEnv proof current = do
        (prefix, checked, next) <- proofCheck proofEnv proof current
        encodedPrefix <- mapM assumeDefinedness prefix
        encoded <- mapM checkedAssumption checked
        pure (encodedPrefix ++ encoded, next)
    encodeWitnessGuard scoped (steps, current) guard = do
        (prefix, checks, next) <- proofCheck scoped guard current
        pure (steps ++ prefix ++ checks, next)
    encodeWitness proofEnv (refs, current) witness = do
        (prefix, ref, next) <- proofOperand proofEnv witness current
        if null prefix then Just () else Nothing
        pure (refs ++ [ref], next)
    supportedWitnessGuardStep (MData tag _) = tag `elem`
        ["ExecutionStep::ApplyFresh", "ExecutionStep::Assign", "ExecutionStep::Check", "ExecutionStep::CheckMandatory"]
    supportedWitnessGuardStep _ = False
    encodeForallRelation proofEnv index lower upper relation left right current = do
        let (i, afterFresh) = fresh current
            local = negate i - 1
        if local < toInteger (minBound :: Int) then Nothing else Just ()
        let scoped = Map.insert index (M.Copy (M.Local (fromInteger local))) proofEnv
        (lowerSteps, lowerRef, afterLower) <- proofOperand proofEnv lower afterFresh
        if null lowerSteps then Just () else Nothing
        (upperSteps, upperRef, afterUpper) <- proofOperand proofEnv upper afterLower
        if null upperSteps then Just () else Nothing
        (leftSteps, leftRef, afterLeft) <- proofOperand scoped left afterUpper
        if null leftSteps then Just () else Nothing
        (rightSteps, rightRef, afterRight) <- proofOperand scoped right afterLeft
        if null rightSteps then Just () else Nothing
        let assumption = step "AssumeForallRelation"
                [ ("local", MInt local), ("lower", lowerRef), ("upper", upperRef)
                , ("relation", MInt relation), ("left", leftRef), ("right", rightRef)
                ]
        pure ([assumption], afterRight)
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

booleanFunctionId :: BuiltinFunct -> Maybe Integer
booleanFunctionId And = Just (-20)
booleanFunctionId Or = Just (-21)
booleanFunctionId Not = Just (-22)
booleanFunctionId _ = Nothing


withContractDefinitions :: Map.Map Variable M.Operand -> M.Function -> M.Function
withContractDefinitions definitions fn = fn
    { M.fnBlocks = Map.map scopeBlock (M.fnBlocks fn)
    , M.fnSpec = scopedSpec
    }
  where
    scope env = Map.union definitions env
    scopeBlock basic = basic
        { M.blockStatements = map scopeStatement (M.blockStatements basic) }
    scopeStatement (M.Ghost env ghost) = M.Ghost (scope env) ghost
    scopeStatement other = other
    spec = M.fnSpec fn
    scopedSpec = spec
        { M.specEnv = scope (M.specEnv spec)
        , M.specLoops = Map.map (\loop -> loop{M.loopEnv = scope (M.loopEnv loop)}) (M.specLoops spec)
        }

statement :: M.Statement -> Build -> Maybe ([MirValue], Build)
-- Keep a function reference as an opaque term so it can be passed through a
-- function-valued parameter. Calls still use static target analysis.
statement (M.Assign (M.Local dest) (M.Use (M.Const (M.CFn name)))) b0 =
    let (function, b1) = namedFunction ("function-value:" ++ name) b0
        value = step "ApplyFresh" [
            ("local", MInt (toInteger dest)),
            ("function", MInt function),
            ("arguments", MList [])
            ]
     in Just ([value], b1)
statement (M.Assign (M.Local dest) (M.Use source)) b = do
    (v, b') <- operand source b
    pure ([step "Assign" [("local", MInt (toInteger dest)), ("value", v)]], b')
-- Boxes and unsizing preserve the proof value, as in the reference MIR
-- validator. Ownership and representation are handled by later passes.
statement (M.Assign dest (M.MakeBox source)) b = statement (M.Assign dest (M.Use source)) b
statement (M.Assign dest (M.Unbox source)) b = statement (M.Assign dest (M.Use source)) b
statement (M.Assign dest (M.Unsize source)) b = statement (M.Assign dest (M.Use source)) b
statement (M.Assign dest (M.Clone source)) b = statement (M.Assign dest (M.Use source)) b
statement (M.Assign dest (M.AsVariant source _)) b = statement (M.Assign dest (M.Use source)) b
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
statement (M.Assign (M.Local dest) (M.MakeList values)) b0 = do
    (snapshots, b1) <- foldM snapshot ([], b0) values
    let destination = record "ValueRef::Local" [("local", MInt (toInteger dest))]
        create = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (-12)), ("arguments", MList [ref | (_, ref, _) <- snapshots])]
    (lengthFacts, b2) <- knownLength destination (toInteger (length values)) b1
    (elementFacts, b3) <- foldM (knownElement destination) ([], b2) (zip [0 :: Integer ..] snapshots)
    pure ([saved | (_, _, saved) <- snapshots] ++ [create] ++ lengthFacts ++ elementFacts, b3)
  where
    snapshot (acc, b) source = do
        (value, b1) <- operand source b
        let (i, b2) = fresh b1
            local = negate i - 1
            ref = record "ValueRef::Local" [("local", MInt local)]
            save = step "Assign" [("local", MInt local), ("value", value)]
        pure (acc ++ [(value, ref, save)], b2)
    knownLength destination sizeValue currentBuild = do
        (expected, b1) <- operand (M.Const (M.CInt sizeValue)) currentBuild
        let (i, b2) = fresh b1
            local = negate i - 1
            result = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (-13)), ("arguments", MList [destination])]
            known = step "Assume" [("relation", MInt 0), ("left", result), ("right", expected)]
        pure ([apply, known], b2)
    knownElement destination (steps, currentBuild) (index, (original, _, _)) = do
        (indexRef, b1) <- operand (M.Const (M.CInt index)) currentBuild
        let (i, b2) = fresh b1
            local = negate i - 1
            result = record "ValueRef::Local" [("local", MInt local)]
            apply = step "ApplyFresh" [("local", MInt local), ("function", MInt (-14)), ("arguments", MList [destination, indexRef])]
            known = step "Assume" [("relation", MInt 0), ("left", result), ("right", original)]
        pure (steps ++ [apply, known], b2)
statement (M.Assign (M.Local dest) (M.ReadField source _ field)) b0 = do
    (value, b1) <- operand source b0
    let (function, b2) = namedFunction ("field:" ++ field) b1
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList [value])]], b2)
statement (M.Assign (M.Local dest) (M.IsVariant source variant)) b0 = do
    (value, b1) <- operand source b0
    let (predicate, b2) = namedFunction ("is-variant:" ++ variant) b1
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt predicate), ("arguments", MList [value])]], b2)
-- World-reading operations return a new symbolic value on every invocation.
-- Their stable result ranges are builtin contracts; a unique function symbol
-- avoids making repeated reads congruent by accident.
statement (M.Assign (M.Local dest) (M.ListOp operation args)) b0
    | operation `elem` [M.ReadByte, M.ArgCount, M.ArgByte, M.PathByte, M.FileLoad, M.FileByte, M.StoreByte, M.FileStore] = do
        (arguments, b1) <- foldM readArgument ([], b0) args
        let functionName = "world:" ++ show operation ++ ":" ++ show (nextTerm b1)
            (function, b2) = namedFunction functionName b1
            apply = step "ApplyFresh"
                [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList arguments)]
        (facts, b3) <- worldResultFacts operation dest b2
        pure (apply : facts, b3)
  where
    readArgument (values, current) arg = do
        (value, next) <- operand arg current
        pure (values ++ [value], next)
statement (M.Assign (M.Local dest) (M.ListOp M.Length [source])) b = do
    (value, b') <- operand source b
    pure ([step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (-13)), ("arguments", MList [value])]], b')
-- Byte conversions preserve the integer term. Constructing a Byte proves its
-- range, while converting it back to Int adds no new fact.
statement (M.Assign (M.Local dest) (M.ListOp M.ToByte [source])) b0 = do
    (value, b1) <- operand source b0
    (zero, b2) <- operand (M.Const (M.CInt 0)) b1
    (limit, b3) <- operand (M.Const (M.CInt 256)) b2
    pure
        ( [check 3 zero value, check 2 value limit,
           step "Assign" [("local", MInt (toInteger dest)), ("value", value)]]
        , b3
        )
statement (M.Assign dest (M.ListOp M.FromByte [source])) b =
    statement (M.Assign dest (M.Use source)) b
-- Output has no proof-visible effect; the builtin returns the byte it wrote.
statement (M.Assign dest (M.ListOp operation [source])) b
    | operation == M.WriteByte || operation == M.WriteError =
        statement (M.Assign dest (M.Use source)) b
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
    emptyArraySteps (toInteger dest) b0
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
    (defined, b4) <- case op of
        M.Div -> divisionDefined x y b3
        _ -> Just ([], b3)
    let apply = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt (functionId op)), ("arguments", MList [x, y])]
    pure (checks ++ defined ++ [apply], b4)
  where
    nonzero y b' = do
        (zero, b'') <- operand (M.Const (M.CInt 0)) b'
        pure ([check 1 y zero], b'')

statement (M.Ghost env (M.GhostValidation (ProofAssert proof))) b = do
    (prefix, checks, b') <- case unboundProofVariables env proof of
        [] -> proofCheck env proof b
        _ -> do
            (zero, b1) <- operand (M.Const (M.CInt 0)) b
            (one, b2) <- operand (M.Const (M.CInt 1)) b1
            Just ([], [check 0 zero one], b2)
    pure (prefix ++ checks, b')
statement (M.Ghost env (M.GhostValidation (Rewrite (CheckRel proof)))) b0 = do
    (prefix, checked, b1) <- proofCheck env proof b0
    assumed <- mapM checkedAssumption checked
    pure (prefix ++ checked ++ assumed, b1)
statement (M.Ghost env (M.GhostValidation (Rewrite (CheckGtZero proof)))) b0 = do
    (prefix, value, b1) <- proofOperand env proof b0
    (zero, b2) <- operand (M.Const (M.CInt 0)) b1
    let checked = check 2 zero value
    assumed <- checkedAssumption checked
    pure (prefix ++ [checked, assumed], b2)
statement (M.Ghost _ (M.GhostValidation (Rewrite (Refl _)))) b = Just ([], b)
statement (M.Ghost _ (M.GhostValidation (Rewrite (Eval _)))) b = Just ([], b)
statement (M.Ghost _ (M.GhostValidation (Rewrite EvalAll))) b = Just ([], b)
statement (M.Ghost env (M.GhostValidation (Rewrite (UserRewrite name arguments)))) b =
    axiomRewrite env name arguments b
statement (M.Ghost _ (M.GhostAxiom name parameters inputs outputs)) b =
    Just ([], b{proofRules = Map.insert name (AxiomRule parameters inputs outputs) (proofRules b)})
statement (M.Ghost _ (M.GhostProof name parameters inputs outputs body)) b =
    proofDeclaration name parameters inputs outputs body b
-- Function bodies are checked independently before the main graph. Function
-- definitions have already been checked for uniqueness and placement.
statement (M.Ghost _ M.GhostFunction{}) b = Just ([], b)
-- Ownership inserts these instructions after source validation. They preserve
-- proof values except that a dropped or partially moved local is no longer
-- available for later reads.
statement (M.Peek dest value) b = statement (M.Assign dest value) b
statement (M.Drop (M.Local local)) b = Just ([step "Forget" [("local", MInt (toInteger local))]], b)
statement (M.Assign dest (M.TakeField (M.Local source) name field)) b0 = do
    (steps, b1) <- statement (M.Assign dest (M.ReadField (M.Copy (M.Local source)) name field)) b0
    pure (steps ++ [step "Forget" [("local", MInt (toInteger source))]], b1)
statement _ _ = Nothing

-- A function-valued local can have more than one target after a branch. Keep
-- the full conservative set so calls can check every possible input contract.
staticFunctionTargets :: M.Function -> M.BlockId -> [M.Statement] -> M.Operand -> Maybe [Name]
staticFunctionTargets fn blockId statements callee = Set.toList <$> targetOperand Set.empty blockId statements callee
  where
    targetOperand _ _ _ (M.Const (M.CFn name)) = Just (Set.singleton name)
    targetOperand seen currentBlock currentStatements (M.Copy local) = resolveLocal seen currentBlock currentStatements local
    targetOperand _ _ _ _ = Nothing
    resolveLocal seen currentBlock currentStatements local =
        let key = (currentBlock, local, length currentStatements)
         in if Set.member key seen then Nothing
            else case find (writesLocal local . snd) (reverse (zip [0 :: Int ..] currentStatements)) of
                Just (index, M.Assign _ value) -> targetRvalue (Set.insert key seen) currentBlock (take index currentStatements) value
                Just (index, M.Peek _ value) -> targetRvalue (Set.insert key seen) currentBlock (take index currentStatements) value
                Just (_, M.Drop _) -> Nothing
                _ -> fromPredecessors (Set.insert key seen) currentBlock local
    targetRvalue _ _ _ (M.Use (M.Const (M.CFn name))) = Just (Set.singleton name)
    targetRvalue seen currentBlock before (M.Use (M.Copy local)) = resolveLocal seen currentBlock before local
    targetRvalue seen currentBlock before (M.MakeBox (M.Copy local)) = resolveLocal seen currentBlock before local
    targetRvalue seen currentBlock before (M.Unbox (M.Copy local)) = resolveLocal seen currentBlock before local
    targetRvalue seen currentBlock before (M.Unsize (M.Copy local)) = resolveLocal seen currentBlock before local
    targetRvalue seen currentBlock before (M.Clone (M.Copy local)) = resolveLocal seen currentBlock before local
    targetRvalue _ _ _ _ = Nothing
    fromPredecessors seen currentBlock local
        | currentBlock == M.BlockId 0 = Nothing
        | otherwise = do
            targets <- mapM (\predecessor -> resolveLocal seen predecessor (M.blockStatements (M.fnBlocks fn Map.! predecessor)) local) predecessors
            if null targets then Nothing else Just (Set.unions targets)
      where
        predecessors =
            [ predecessor
            | (predecessor, basicBlock) <- Map.toList (M.fnBlocks fn)
            , currentBlock `elem` M.successors (M.blockTerminator basicBlock)
            ]
    writesLocal local statement' = case statement' of
        M.Assign dest _ -> dest == local
        M.Peek dest _ -> dest == local
        M.Drop dest -> dest == local
        _ -> False

-- If dataflow cannot recover a function value's exact source, use every
-- function in the program with its declared callable type. This is a safe
-- over-approximation: indirectCall checks every candidate's preconditions and
-- retains only output facts shared by all candidates.
functionTargetsForType :: Map.Map Name M.Function -> M.Function -> M.Operand -> Maybe [Name]
functionTargetsForType functions caller (M.Copy local) = do
    TFn arguments result <- M.localType <$> Map.lookup local (M.fnLocals caller)
    let matches candidate =
            mapM (\parameter -> M.localType <$> Map.lookup parameter (M.fnLocals candidate)) (M.fnParams candidate) == Just arguments
                && M.fnReturns candidate == Just result
        names = [name | (name, candidate) <- Map.toAscList functions, matches candidate]
    if null names then Nothing else Just names
functionTargetsForType _ _ _ = Nothing

checkedAssumption :: MirValue -> Maybe MirValue
checkedAssumption (MData "ExecutionStep::Check" fields) = Just (MData "ExecutionStep::Assume" fields)
checkedAssumption (MData "ExecutionStep::CheckVariant" fields) = Just (MData "ExecutionStep::AssumeVariant" fields)
checkedAssumption (MData "ExecutionStep::ValidateForall" fields) =
    Just (MData "ExecutionStep::ValidateForall" (("assume", MBool True) : [(name, value) | (name, value) <- fields, name /= "assume"]))
checkedAssumption _ = Nothing

axiomRewrite :: M.Env -> Name -> [VariableProof] -> Build -> Maybe ([MirValue], Build)
axiomRewrite env name arguments b0 = case Map.lookup name (proofRules b0) of
    Just (AxiomRule parameters inputs outputs)
        | length parameters == length arguments
        , not (any proofHasForall arguments) -> do
            (argumentSteps, b1, argumentOperands) <- foldM (snapshot env) ([], b0, []) arguments
            let argumentEnv = Map.fromList (zip parameters argumentOperands) `Map.union` env
            (checks, b2, _) <- contractStepsWith False argumentEnv Map.empty inputs b1
            -- Applying an axiom checks its inputs and assumes its outputs in
            -- the caller's original proof state; input-local definitions do
            -- not cross that boundary in the reference validator.
            (assumptions, b3, _) <- contractStepsWith True argumentEnv Map.empty outputs b2
            pure (argumentSteps ++ checks ++ assumptions, b3)
    Just (ProofRule parameters inputs exported)
        | length parameters == length arguments
        , not (any proofHasForall arguments) -> do
            (argumentSteps, b1, argumentOperands) <- foldM (snapshot env) ([], b0, []) arguments
            let argumentEnv = Map.fromList (zip parameters argumentOperands) `Map.union` env
            (checks, b2, _) <- contractStepsWith False argumentEnv Map.empty inputs b1
            let promises = map ProofAssert exported
            (assumptions, b3) <- contractSteps True argumentEnv promises b2
            pure (argumentSteps ++ checks ++ assumptions, b3)
    _ -> Nothing
  where
    snapshot sourceEnv (steps, current, bindings) argument = do
        (prefix, value, next) <- proofOperand sourceEnv argument current
        let (i, b') = fresh next
            local = negate i - 1
        if local < toInteger (minBound :: Int) then Nothing else Just ()
        let saved = step "Assign" [("local", MInt local), ("value", value)]
            argumentOperand = M.Copy (M.Local (fromInteger local))
        pure (steps ++ prefix ++ [saved], b', bindings ++ [argumentOperand])

proofDeclaration :: Name -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> [ValidationStatement] -> Build -> Maybe ([MirValue], Build)
proofDeclaration name parameters inputs outputs body b0 = do
    if all supportedInput inputs && all supportedProof (body ++ outputs) then Just () else Nothing
    exported <- proofRuleExports (proofRules b0) inputs body outputs
    (locals, env, b1) <- foldM allocate ([], Map.empty, b0) parameters
    (assumptions, b2, definitions) <- contractStepsWith True env Map.empty inputs b1
    (checks, b3, _) <- contractStepsWith False env definitions (body ++ outputs) b2
    let validate = step "ValidateProof"
            [ ("parameters", MList locals)
            , ("constants", MList (literalTerms b3))
            , ("applications", MList (literalApps b3))
            , ("assumptions", MList assumptions)
            , ("checks", MList checks)
            ]
        rules = Map.insert name (ProofRule parameters inputs exported) (proofRules b3)
    pure ([validate], b3{proofRules = rules})
  where
    supportedInput (ProofAssert _) = True
    supportedInput (Rewrite _) = True
    supportedInput (AssignProofVar _ _) = True
    supportedProof (ProofAssert _) = True
    supportedProof (Rewrite (CheckRel _)) = True
    supportedProof (Rewrite (CheckGtZero _)) = True
    supportedProof (Rewrite (Refl _)) = True
    supportedProof (Rewrite (Eval _)) = True
    supportedProof (Rewrite EvalAll) = True
    supportedProof (Rewrite (UserRewrite _ _)) = True
    supportedProof (AssignProofVar _ _) = True
    allocate (locals, names, current) parameter = do
        let (i, next) = fresh current
            local = negate i - 1
        if local < toInteger (minBound :: Int) then Nothing else Just ()
        pure (locals ++ [MInt local], Map.insert parameter (M.Copy (M.Local (fromInteger local))) names, next)

-- Export the assertions established by a proof body, after expanding its
-- proof-variable snapshots. Input definitions are in scope in the body and
-- outputs; input assertions themselves remain obligations at each use.
proofRuleExports :: RuleContext -> [ValidationStatement] -> [ValidationStatement] -> [ValidationStatement] -> Maybe [VariableProof]
proofRuleExports rules inputs body outputs = do
    (inputDefinitions, _) <- expand Set.empty (Map.empty, []) inputs
    (_, exported) <- expand Set.empty (inputDefinitions, []) (body ++ outputs)
    pure exported
  where
    expand seen = foldM (add seen)
    add seen (definitions, exported) statement' = case statement' of
        AssignProofVar name expression ->
            let value = substituteProofDefinitions definitions (exprToProof expression)
             in Just (Map.insert name value definitions, exported)
        ProofAssert proof ->
            Just (definitions, exported ++ [substituteProofDefinitions definitions proof])
        Rewrite (CheckRel proof) ->
            Just (definitions, exported ++ [substituteProofDefinitions definitions proof])
        Rewrite (CheckGtZero proof) ->
            let value = substituteProofDefinitions definitions proof
                positive = FApp (CTerm (builtinFunct (Rel Gt))) [value, CTerm (VInt 0)]
             in Just (definitions, exported ++ [positive])
        Rewrite (UserRewrite name arguments) -> do
            facts <- ruleOutputs seen definitions name arguments
            pure (definitions, exported ++ facts)
        _ -> Just (definitions, exported)
    ruleOutputs seen definitions name arguments = do
        if Set.member name seen then Nothing else Just ()
        rule <- Map.lookup name rules
        case rule of
            ProofRule parameters _ assertions -> do
                if length parameters == length arguments then Just () else Nothing
                let actuals = map (substituteProofDefinitions definitions) arguments
                    bindings = Map.fromList (zip parameters actuals)
                pure (map (substituteProofDefinitions bindings) assertions)
            AxiomRule parameters _ clauses -> do
                if length parameters == length arguments then Just () else Nothing
                let actuals = map (substituteProofDefinitions definitions) arguments
                    bindings = Map.fromList (zip parameters actuals)
                substituted <- mapM (substituteValidationProofs bindings) clauses
                (_, facts) <- expand (Set.insert name seen) (Map.empty, []) substituted
                pure facts

substituteValidationProofs :: Map.Map Variable VariableProof -> ValidationStatement -> Maybe ValidationStatement
substituteValidationProofs bindings statement' = case statement' of
    ProofAssert proof -> Just (ProofAssert (substituteProofDefinitions bindings proof))
    AssignProofVar name expression -> AssignProofVar name <$> proofToExpressionMaybe (substituteProofDefinitions bindings (exprToProof expression))
    Rewrite (Refl proof) -> Just (Rewrite (Refl (substituteProofDefinitions bindings proof)))
    Rewrite (CheckGtZero proof) -> Just (Rewrite (CheckGtZero (substituteProofDefinitions bindings proof)))
    Rewrite (CheckRel proof) -> Just (Rewrite (CheckRel (substituteProofDefinitions bindings proof)))
    Rewrite (UserRewrite name arguments) -> Just (Rewrite (UserRewrite name (map (substituteProofDefinitions bindings) arguments)))
    other -> Just other

proofToExpressionMaybe :: VariableProof -> Maybe Expression
proofToExpressionMaybe (ATerm name) = Just (Var name)
proofToExpressionMaybe (BVar name) = Just (Var name)
proofToExpressionMaybe (CTerm value) = Just (Val value)
proofToExpressionMaybe (FApp function arguments) = F <$> proofToExpressionMaybe function <*> mapM proofToExpressionMaybe arguments
proofToExpressionMaybe Forall{} = Nothing

substituteProofDefinitions :: Map.Map Variable VariableProof -> VariableProof -> VariableProof
substituteProofDefinitions definitions proof = case proof of
    ATerm name -> Map.findWithDefault proof name definitions
    FApp function arguments -> FApp (substituteProofDefinitions definitions function) (map (substituteProofDefinitions definitions) arguments)
    Forall index guards conclusion ->
        let scoped = Map.delete index definitions
         in Forall index (map (substituteProofDefinitions scoped) guards) (substituteProofDefinitions scoped conclusion)
    _ -> proof

-- Read the output contracts directly from StdLib so this bridge cannot drift
-- from the semantics it is comparing against.
worldResultFacts :: M.ListOp -> Int -> Build -> Maybe ([MirValue], Build)
worldResultFacts operation dest b0 = do
    builtin <- worldBuiltin operation
    case builtinFunct builtin of
        VFunct _ _ _ _ promises ->
            contractSteps True (Map.singleton "return" (M.Copy (M.Local dest))) (map ProofAssert promises) b0
        _ -> Nothing
  where
    worldBuiltin M.ReadByte = Just ReadByte
    worldBuiltin M.ArgCount = Just ArgCount
    worldBuiltin M.ArgByte = Just ArgByte
    worldBuiltin M.PathByte = Just PathByte
    worldBuiltin M.FileLoad = Just FileLoad
    worldBuiltin M.FileByte = Just FileByte
    worldBuiltin M.StoreByte = Just StoreByte
    worldBuiltin M.FileStore = Just FileStore
    worldBuiltin _ = Nothing

-- A direct call uses contracts of bodies checked separately. Snapshot input
-- arguments and model reassigned integer parameters as fresh outputs constrained
-- by the callee's postcondition.
directCall :: Map.Map Name M.TypeDecl -> Map.Map Name ([Variable], [(Variable, Type)]) -> Map.Map Name [ValidationStatement] -> Set.Set Name -> Maybe M.Local -> M.Function -> M.Function -> [M.Operand] -> M.Local -> Build -> Maybe ([MirValue], Build)
directCall types generics invariants worldReaders entryVariant caller callee args (M.Local dest) b0 = do
    if length args == length params then Just () else Nothing
    if mayDiverge callee && not (mayDiverge caller) then Nothing else Just ()
    let sizeArgs = drop (length args - length (M.fnSizeParams callee)) args
    if all validSizeArg sizeArgs then Just () else Nothing
    case M.fnReturns callee of Just _ -> Just (); Nothing -> Nothing
    (snapshots, b1) <- foldM snapshot ([], b0) args
    let bindings = Map.fromList (zip params [local | (local, _) <- snapshots])
        argumentRefs = [record "ValueRef::Local" [("local", MInt (toInteger n))] | (M.Local n, _) <- snapshots]
        remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
        remap constant@(M.Const _) = Just constant
        remap _ = Nothing
        sizeBindings = Map.fromList (zip (M.fnSizeParams callee) sizeArgs)
        env = Map.union sizeBindings (Map.mapMaybe remap (M.specEnv (M.fnSpec callee)))
    (sizeChecks, withSizes) <- sizeParameterSteps False callee (map fst snapshots) b1
    (checks, b2, definitions) <- contractStepsWith False env Map.empty (M.specRequires (M.fnSpec callee)) withSizes
    (terminationChecks, withTermination) <- recursiveTerminationChecks env b2
    (parameterResults, parameterSteps, withParameterResults) <- foldM (snapshotReassignedParameter argumentRefs)
        (Map.empty, [], withTermination) reassignedParameterLocals
    let resultEnv = Map.insert "return" (M.Copy (M.Local dest)) (Map.union parameterResults env)
    (assumptions, b3, _) <- contractStepsWith True resultEnv definitions (M.specEnsures (M.fnSpec callee)) withParameterResults
    let callName
            | Set.member (M.fnName callee) worldReaders = "world-call:" ++ M.fnName callee ++ ":" ++ show (nextTerm b3)
            | otherwise = "call:" ++ M.fnName callee
        (function, b4) = namedFunction callName b3
        result = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList argumentRefs)]
    pure ([save | (_, save) <- snapshots] ++ sizeChecks ++ checks ++ terminationChecks ++ parameterSteps ++ [result] ++ assumptions, b4)
  where
    params = M.fnParams callee
    callerSizeParams = drop (length (M.fnParams caller) - length (M.fnSizeParams caller)) (M.fnParams caller)
    reassignedParameterLocals =
        [ (local, name)
        | local <- params
        , reassignsParameter local
        , Just decl <- [Map.lookup local (M.fnLocals callee)]
        , Just name <- [M.localName decl]
        ]
    validSizeArg (M.Const (M.CInt _)) = True
    validSizeArg (M.Copy local) = local `elem` callerSizeParams
    validSizeArg _ = False
    reassignsParameter local =
        any (writesParameter local) (concatMap M.blockStatements (Map.elems (M.fnBlocks callee)))
            || any (writesParameterTerminator local) (map M.blockTerminator (Map.elems (M.fnBlocks callee)))
    writesParameter local (M.Assign written _) = local == written
    writesParameter local (M.Peek written _) = local == written
    writesParameter local (M.Drop written) = local == written
    writesParameter _ _ = False
    writesParameterTerminator local (M.Call _ _ written _) = local == written
    writesParameterTerminator _ _ = False
    recursiveTerminationChecks env b
        | M.fnName caller /= M.fnName callee = Just ([], b)
        | otherwise = case M.specTermination (M.fnSpec callee) of
            Just (Counting expression) -> do
                entry <- entryVariant
                (prefix, variant, b1) <- proofOperand env (exprToProof expression) b
                (earlier, b2) <- operand (M.Copy entry) b1
                pure (prefix ++ [check 2 variant earlier], b2)
            Just (Parts expression) -> do
                entry <- entryVariant
                let variantEnv = Map.insert "variant at entry" (M.Copy entry) env
                    within = FApp (CTerm (builtinFunct Within)) [exprToProof expression, ATerm "variant at entry"]
                (prefix, [membership], b') <- proofCheck variantEnv within b
                pure (prefix ++ [membership], b')
            Just MayDiverge -> Just ([], b)
            _ -> Nothing
    snapshot (saved, b) (M.Const (M.CFn name)) = do
        let (function, b1) = namedFunction ("function-value:" ++ name) b
            (i, b2) = fresh b1
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            save = step "ApplyFresh"
                [("local", MInt (toInteger number)), ("function", MInt function), ("arguments", MList [])]
        pure (saved ++ [(local, save)], b2)
    snapshot (saved, b) arg = do
        (value, b1) <- operand arg b
        let (i, b2) = fresh b1
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            save = step "Assign" [("local", MInt (toInteger number)), ("value", value)]
        pure (saved ++ [(local, save)], b2)
    snapshotReassignedParameter arguments (bindings, steps, current) (parameter, name) = do
        decl <- Map.lookup parameter (M.fnLocals callee)
        let (function, b1) = namedFunction
                ("call-result-param:" ++ M.fnName callee ++ ":" ++ name ++ ":" ++ show (nextTerm current)) current
            (i, b2) = fresh b1
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            created = step "ApplyFresh" [("local", MInt (toInteger number)), ("function", MInt function), ("arguments", MList arguments)]
        (typeFacts, b3) <- typeStepsFor types generics invariants callee (M.localType decl) local b2
        pure (Map.insert name (M.Copy local) bindings, steps ++ [created] ++ typeFacts, b3)

-- At a join the callee may be any of several function values. Check every
-- candidate's input and size contracts, then assign one shared result. Retain
-- only output guarantees that translate to identical safe steps for every
-- candidate.
indirectCall :: Map.Map Name M.TypeDecl -> Map.Map Name ([Variable], [(Variable, Type)]) -> Map.Map Name [ValidationStatement] -> Maybe M.Local -> M.Function -> [M.Function] -> [M.Operand] -> M.Local -> Build -> Maybe ([MirValue], Build)
indirectCall types generics invariants entryVariant caller callees args (M.Local dest) b0 = do
    case callees of
        [] -> Nothing
        first : rest -> do
            firstSignature <- signature first
            if any ((/= length args) . length . M.fnParams) callees then Nothing else Just ()
            if all ((== Just firstSignature) . signature) rest then Just () else Nothing
            case M.fnReturns first of Just _ -> Just (); Nothing -> Nothing
            if any mayDiverge callees && not (mayDiverge caller) then Nothing else Just ()
            (snapshots, b1) <- foldM snapshot ([], b0) args
            let argumentRefs = [record "ValueRef::Local" [("local", MInt (toInteger local))] | (M.Local local, _) <- snapshots]
            (checks, b2) <- foldM (checkInputs snapshots) ([], b1) callees
            (commonOutputs, b3) <- commonOutputSteps snapshots (M.Local dest) callees b2
            let (function, b4) = namedFunction ("indirect-call:" ++ M.fnName caller ++ ":" ++ show (nextTerm b3)) b3
                result = step "ApplyFresh" [("local", MInt (toInteger dest)), ("function", MInt function), ("arguments", MList argumentRefs)]
            pure ([save | (_, save) <- snapshots] ++ checks ++ [result] ++ commonOutputs, b4)
  where
    signature fn = do
        parameters <- mapM (\local -> M.localType <$> Map.lookup local (M.fnLocals fn)) (M.fnParams fn)
        pure (parameters, M.fnReturns fn, length (M.fnSizeParams fn))
    callerSizeParams = drop (length (M.fnParams caller) - length (M.fnSizeParams caller)) (M.fnParams caller)
    validSizeArg (M.Const (M.CInt _)) = True
    validSizeArg (M.Copy local) = local `elem` callerSizeParams
    validSizeArg _ = False
    snapshot (saved, current) arg = do
        (value, b1) <- operand arg current
        let (i, b2) = fresh b1
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let local = M.Local (negate (fromInteger i) - 1)
            M.Local number = local
            save = step "Assign" [("local", MInt (toInteger number)), ("value", value)]
        pure (saved ++ [(local, save)], b2)
    checkInputs snapshots (steps, current) callee = do
        let sizeArgs = drop (length args - length (M.fnSizeParams callee)) args
        if all validSizeArg sizeArgs then Just () else Nothing
        let bindings = Map.fromList (zip (M.fnParams callee) [local | (local, _) <- snapshots])
            remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
            remap constant@(M.Const _) = Just constant
            remap _ = Nothing
            env = Map.mapMaybe remap (M.specEnv (M.fnSpec callee))
        (sizeChecks, withSizes) <- sizeParameterSteps False callee (map fst snapshots) current
        (contractChecks, withChecks, _) <- contractStepsWith False env Map.empty (M.specRequires (M.fnSpec callee)) withSizes
        (terminationChecks, withTermination) <- recursiveTerminationChecks callee env withChecks
        pure (steps ++ sizeChecks ++ contractChecks ++ terminationChecks, withTermination)
    recursiveTerminationChecks callee env current
        | M.fnName caller /= M.fnName callee = Just ([], current)
        | otherwise = case M.specTermination (M.fnSpec callee) of
            Just (Counting expression) -> do
                entry <- entryVariant
                (prefix, variant, b1) <- proofOperand env (exprToProof expression) current
                (earlier, b2) <- operand (M.Copy entry) b1
                pure (prefix ++ [check 2 variant earlier], b2)
            Just (Parts expression) -> do
                entry <- entryVariant
                let variantEnv = Map.insert "variant at entry" (M.Copy entry) env
                    within = FApp (CTerm (builtinFunct Within)) [exprToProof expression, ATerm "variant at entry"]
                (prefix, [membership], b') <- proofCheck variantEnv within current
                pure (prefix ++ [membership], b')
            Just MayDiverge -> Just ([], current)
            _ -> Nothing
    commonOutputSteps snapshots destination candidates current
        | any hasInputDefinitions candidates = Just ([], current)
        | not (all (sameReassignedParameters candidates) (drop 1 candidates)) = Just ([], current)
        | otherwise = case sharedParameterResults snapshots candidates current of
            Nothing -> Just ([], current)
            Just (parameterSteps, parameterResults, withParameters) ->
                case mapM (candidateOutputs snapshots destination parameterResults withParameters) candidates of
                    Nothing -> Just (parameterSteps, withParameters)
                    Just [] -> Just (parameterSteps, withParameters)
                    Just ((firstSteps, firstBuild) : rest) ->
                        let common = foldl intersect firstSteps (map fst rest)
                         in Just (parameterSteps ++ common, firstBuild)
    candidateOutputs snapshots destination parameterResults current callee = do
        let bindings = Map.fromList (zip (M.fnParams callee) [local | (local, _) <- snapshots])
            remap (M.Copy local) = M.Copy <$> Map.lookup local bindings
            remap constant@(M.Const _) = Just constant
            remap _ = Nothing
            env = Map.mapMaybe remap (M.specEnv (M.fnSpec callee))
            outputParameters = Map.fromList
                [ (name, value)
                | (index, local) <- zip [0 :: Int ..] (M.fnParams callee)
                , Just value <- [Map.lookup index parameterResults]
                , Just declaration <- [Map.lookup local (M.fnLocals callee)]
                , Just name <- [M.localName declaration]
                ]
            resultEnv = Map.insert "return" (M.Copy destination) (Map.union outputParameters env)
        (steps, next, _) <- contractStepsWith True resultEnv Map.empty (M.specEnsures (M.fnSpec callee)) current
        pure (steps, next)
    hasInputDefinitions callee = any isDefinition (M.specRequires (M.fnSpec callee))
    isDefinition (AssignProofVar _ _) = True
    isDefinition _ = False
    reassignedParameters callee =
        [ index
        | (index, local) <- zip [0 :: Int ..] (M.fnParams callee)
        , reassigned callee local
        ]
    sameReassignedParameters candidates callee =
        reassignedParameters callee == reassignedParameters (head candidates)
    sharedParameterResults snapshots candidates current = foldM add ([], Map.empty, current) indices
      where
        indices = reassignedParameters (head candidates)
        add (steps, results, build) index = do
            parameter <- case drop index (M.fnParams (head candidates)) of
                local : _ -> Just local
                [] -> Nothing
            declaration <- Map.lookup parameter (M.fnLocals (head candidates))
            let (function, next) = namedFunction
                    ("indirect-call-param:" ++ M.fnName caller ++ ":" ++ show (nextTerm build) ++ ":" ++ show index) build
                (freshId, afterFresh) = fresh next
                local = M.Local (negate (fromInteger freshId) - 1)
                M.Local number = local
                arguments = [record "ValueRef::Local" [("local", MInt (toInteger source))] | (M.Local source, _) <- snapshots]
                created = step "ApplyFresh" [("local", MInt (toInteger number)), ("function", MInt function), ("arguments", MList arguments)]
            if freshId <= toInteger (maxBound :: Int) then Just () else Nothing
            (typeFacts, afterTypeFacts) <- typeStepsFor types generics invariants (head candidates) (M.localType declaration) local afterFresh
            pure (steps ++ [created] ++ typeFacts, Map.insert index (M.Copy local) results, afterTypeFacts)
    reassigned callee local =
        any (writesLocal local) (concatMap M.blockStatements (Map.elems (M.fnBlocks callee)))
            || any (writesLocalTerminator local) (map M.blockTerminator (Map.elems (M.fnBlocks callee)))
    writesLocal local (M.Assign written _) = written == local
    writesLocal local (M.Peek written _) = written == local
    writesLocal local (M.Drop written) = written == local
    writesLocal _ _ = False
    writesLocalTerminator local (M.Call _ _ written _) = written == local
    writesLocalTerminator _ _ = False

mayDiverge :: M.Function -> Bool
mayDiverge fn = M.specTermination (M.fnSpec fn) == Just MayDiverge

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

-- Capture a counting variant before the body runs. Its checked value remains
-- in a hidden local so recursive calls can compare their argument variant to
-- the entry value even if the source parameter is reassigned.
functionVariantSteps :: M.Function -> Build -> Maybe ([MirValue], Maybe M.Local, Set.Set M.Local, Build)
functionVariantSteps fn b0 = case M.specTermination (M.fnSpec fn) of
    Just (Counting expression) -> do
        (prefix, value, b1) <- proofOperand (M.specEnv (M.fnSpec fn)) (exprToProof expression) b0
        (zero, b2) <- operand (M.Const (M.CInt 0)) b1
        let (i, b3) = fresh b2
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let localNumber = negate (fromInteger i) - 1
            local = M.Local localNumber
            localRef = record "ValueRef::Local" [("local", MInt (toInteger localNumber))]
            capture = step "Assign" [("local", MInt (toInteger localNumber)), ("value", value)]
        pure (prefix ++ [capture, check 3 zero localRef], Just local, Set.empty, b3)
    Just (Parts expression) -> do
        root <- partRootLocal (M.specEnv (M.fnSpec fn)) expression
        parts <- partLocals fn root
        (prefix, value, b1) <- proofOperand (M.specEnv (M.fnSpec fn)) (exprToProof expression) b0
        let (i, b2) = fresh b1
        if i <= toInteger (maxBound :: Int) then Just () else Nothing
        let localNumber = negate (fromInteger i) - 1
            local = M.Local localNumber
            capture = step "Assign" [("local", MInt (toInteger localNumber)), ("value", value)]
        pure (prefix ++ [capture], Just local, parts, b2)
    Nothing -> Just ([], Nothing, Set.empty, b0)
    Just MayDiverge -> Just ([], Nothing, Set.empty, b0)
    _ -> Nothing

-- Box and variant casts preserve the proof value. Accept them around the
-- structural root so `shrinks Box::unbox(tree)` tracks the same projections as
-- `shrinks tree`.
partRootLocal :: M.Env -> Expression -> Maybe M.Local
partRootLocal env (Var name) = case Map.lookup name env of
    Just (M.Copy local) -> Just local
    _ -> Nothing
partRootLocal env (F (Val (VFunct _ _ _ (BuiltinFunct operation) _)) [inner])
    | transparent operation = partRootLocal env inner
  where
    transparent (Cast _) = True
    transparent other = other `elem` [NewBox, UnBox, Unsize, CloneOf]
partRootLocal _ _ = Nothing

-- Keep only locals whose every definition preserves or projects a part of the
-- original variant parameter. A reassigned root is included only when every
-- write still comes from a tracked value, so later field reads cannot
-- manufacture a false decrease from an unrelated replacement.
partLocals :: M.Function -> M.Local -> Maybe (Set.Set M.Local)
partLocals fn root = do
    let known = grow (Set.singleton root)
        rootWrites = Map.findWithDefault [] root definitions
        preservesRoot source = maybe False (`Set.member` known) source
    if all preservesRoot rootWrites then Just known else Nothing
  where
    definitions = Map.fromListWith (++) (concatMap blockDefinitions (Map.elems (M.fnBlocks fn)))
    blockDefinitions (M.BasicBlock statements ending) = concatMap statementDefinitions statements ++ terminatorDefinitions ending
    statementDefinitions statement' = case statement' of
        M.Assign dest value -> [(dest, [partSource value])]
        M.Peek dest _ -> [(dest, [Nothing])]
        M.Drop dest -> [(dest, [Nothing])]
        _ -> []
    terminatorDefinitions ending = case ending of
        M.Call _ _ dest _ -> [(dest, [Nothing])]
        _ -> []
    partSource value = case value of
        M.Use (M.Copy source) -> Just source
        M.MakeBox (M.Copy source) -> Just source
        M.Unbox (M.Copy source) -> Just source
        M.Unsize (M.Copy source) -> Just source
        M.Clone (M.Copy source) -> Just source
        M.AsVariant (M.Copy source) _ -> Just source
        M.ReadField (M.Copy source) _ _ -> Just source
        _ -> Nothing
    grow known =
        let more = Set.fromList
                [ local
                | (local, sources) <- Map.toList definitions
                , not (Set.member local known)
                , not (null sources)
                , all (maybe False (`Set.member` known)) sources
                ]
            next = Set.union known more
         in if next == known then known else grow next

-- Loop variants may update their root once per iteration, but only from a
-- strict field projection of its value at the start of that iteration.
loopPartLocals :: M.Function -> Set.Set M.BlockId -> M.Local -> Maybe (Set.Set M.Local)
loopPartLocals fn region root = do
    let writes = concat
            [ [ (dest, Just value) | M.Assign dest value <- statements ]
                ++ [ (dest, Nothing) | M.Peek dest _ <- statements ]
                ++ [ (dest, Nothing) | M.Drop dest <- statements ]
                ++ case ending of
                    M.Call _ _ dest _ -> [(dest, Nothing)]
                    _ -> []
            | blockId <- Set.toList region
            , Just (M.BasicBlock statements ending) <- [Map.lookup blockId (M.fnBlocks fn)]
            ]
        definitions = Map.fromListWith (++) [(dest, [value]) | (dest, value) <- writes]
        derivations Nothing = Nothing
        derivations (Just value) = case value of
                M.Use (M.Copy source) -> Just (source, False)
                M.MakeBox (M.Copy source) -> Just (source, False)
                M.Unbox (M.Copy source) -> Just (source, False)
                M.Unsize (M.Copy source) -> Just (source, False)
                M.Clone (M.Copy source) -> Just (source, False)
                M.AsVariant (M.Copy source) _ -> Just (source, False)
                M.ReadField (M.Copy source) _ _ -> Just (source, True)
                _ -> Nothing
        close (knownLocals, strictLocals) =
            let derivationGroups =
                    [ (local, mapMaybe derivations values)
                    | (local, values) <- Map.toList definitions
                    , not (null values)
                    , all (\value -> maybe False (\(source, _) -> Set.member source knownLocals) (derivations value)) values
                    ]
                nextKnown = Set.union knownLocals (Set.fromList (map fst derivationGroups))
                isStrict (source, field) = field || Set.member source strictLocals
                nextStrict = Set.union strictLocals (Set.fromList
                    [ local
                    | (local, sources) <- derivationGroups
                    , all isStrict sources
                    ])
             in if nextKnown == knownLocals && nextStrict == strictLocals then (knownLocals, strictLocals) else close (nextKnown, nextStrict)
        (known, strict) = close (Set.singleton root, Set.empty)
        rootWrites = Map.findWithDefault [] root definitions
        strictWrite value = case derivations value of
            Just (source, _) -> Set.member source strict
            Nothing -> False
    if length rootWrites == 1 then Just () else Nothing
    if all strictWrite rootWrites then Just () else Nothing
    pure known

loopPartRootsForBlock :: M.Function -> M.BlockId -> Map.Map M.Local [M.Local]
loopPartRootsForBlock fn blockId = Map.fromListWith (++)
    [ (part, [loopSnapshotLocal header])
    | (header, spec) <- Map.toList (M.specLoops (M.fnSpec fn))
    , let region = Map.findWithDefault (Set.singleton header) header (loopRegions fn)
    , Set.member blockId region
    , Just (Parts expression) <- [M.loopTermination spec]
    , Just root <- [partRootLocal (M.loopEnv spec) expression]
    , Just parts <- [loopPartLocals fn region root]
    , part <- Set.toList parts
    ]

loopSnapshotLocal :: M.BlockId -> M.Local
loopSnapshotLocal (M.BlockId number) = M.Local (minBound + number)

-- Facts guaranteed by a value's type are trusted in the same places as in
-- the reference validator: parameters and values assigned to typed locals.
typeSteps :: Map.Map Name M.TypeDecl -> Map.Map Name ([Variable], [(Variable, Type)]) -> Map.Map Name [ValidationStatement] -> M.Function -> M.Local -> Build -> Maybe ([MirValue], Build)
typeSteps types generics invariants fn local b0 = do
    decl <- Map.lookup local (M.fnLocals fn)
    typeStepsFor types generics invariants fn (M.localType decl) local b0

typeStepsFor :: Map.Map Name M.TypeDecl -> Map.Map Name ([Variable], [(Variable, Type)]) -> Map.Map Name [ValidationStatement] -> M.Function -> Type -> M.Local -> Build -> Maybe ([MirValue], Build)
typeStepsFor types generics invariants fn valueType (M.Local number) b0 = facts valueType b0
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
            fields <- case Map.lookup base types of
                Just (M.StructDecl fs) -> Just (map fst fs)
                _ -> map fst . snd <$> Map.lookup base generics
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

-- Infer a small sound subset of the reference validator's loop invariants:
-- constant-initialized integer locals that only move in one direction during
-- the loop. The generated assertion is checked before the first iteration and
-- on every back edge, then assumed after the loop locals are havoced. Locals
-- with matching per-block constant deltas also retain their entry difference.
inferredLoopBounds :: M.Function -> M.BlockId -> Set.Set M.BlockId -> M.LoopSpec -> [M.Local] -> [ValidationStatement]
inferredLoopBounds fn header region spec assigned =
    mapMaybe candidate assigned ++ conditionBounds ++ listLengthCounters ++ pairwiseLoopRelations
  where
    blocks = M.fnBlocks fn
    predecessors target =
        [ source
        | (source, basicBlock) <- Map.toList blocks
        , target `elem` M.successors (M.blockTerminator basicBlock)
        ]
    candidate local = do
        decl <- Map.lookup local (M.fnLocals fn)
        if M.localType decl == TInt then Just () else Nothing
        if writtenByNestedLoop local then Nothing else Just ()
        name <- M.localName decl
        case Map.lookup name (M.loopEnv spec) of
            Just (M.Copy sameLocal) | sameLocal == local -> Just ()
            _ -> Nothing
        initial <- entryConstant local
        direction <- monotoneDirection local
        let relation = case direction of
                1 -> GtEq
                -1 -> LtEq
                _ -> Eq
            proof = FApp (CTerm (builtinFunct (Rel relation))) [ATerm name, CTerm (VInt initial)]
        pure (ProofAssert proof)
    conditionBounds = case Map.lookup header blocks of
        Nothing -> []
        Just (M.BasicBlock statements _) -> mapMaybe (conditionBound statements) (zip [0 :: Int ..] statements)
    conditionBound statements (index, M.Assign _ (M.BinaryOp (M.Compare Lt) (M.Copy counter) upper)) = do
        if counter `elem` assigned && not (writtenByNestedLoop counter) && unitIncrement counter then Just () else Nothing
        counterName <- loopName counter
        initial <- entryConstant counter
        upperProof <- upperBoundProof statements index initial upper
        pure (ProofAssert (FApp (CTerm (builtinFunct (Rel LtEq))) [ATerm counterName, upperProof]))
    conditionBound _ _ = Nothing
    listLengthCounters = mapMaybe listCounterCandidate assigned
    listCounterCandidate listLocal = do
        decl <- Map.lookup listLocal (M.fnLocals fn)
        case M.localType decl of
            TList _ -> Just ()
            _ -> Nothing
        if writtenByNestedLoop listLocal || not simpleLoopRegion then Nothing else Just ()
        listName <- loopName listLocal
        initialLength <- entryListLength listLocal
        counter <- find (\local -> local /= listLocal && unitIncrement local && not (writtenByNestedLoop local)) assigned
        counterName <- loopName counter
        initialCounter <- entryConstant counter
        if hasSinglePush listLocal then Just () else Nothing
        let offset = initialLength - initialCounter
            counterTerm = if offset == 0 then ATerm counterName else FApp (CTerm (builtinFunct Plus)) [ATerm counterName, CTerm (VInt offset)]
            lengthTerm = FApp (CTerm (builtinFunct Size)) [ATerm listName]
        pure (ProofAssert (FApp (CTerm (builtinFunct (Rel Eq))) [lengthTerm, counterTerm]))
    pairwiseLoopRelations = mapMaybe pairRelation pairs
      where
        pairs =
            [ (left, right)
            | (index, left) <- zip [0 :: Int ..] assigned
            , right <- drop (index + 1) assigned
            ]
        pairRelation (left, right) = do
            leftDecl <- Map.lookup left (M.fnLocals fn)
            rightDecl <- Map.lookup right (M.fnLocals fn)
            if M.localType leftDecl == TInt && M.localType rightDecl == TInt then Just () else Nothing
            if writtenByNestedLoop left || writtenByNestedLoop right then Nothing else Just ()
            leftName <- loopName left
            rightName <- loopName right
            leftInitial <- entryConstant left
            rightInitial <- entryConstant right
            leftWrites <- writeDeltas left
            rightWrites <- writeDeltas right
            if leftWrites == rightWrites then Just () else Nothing
            let offset = leftInitial - rightInitial
            if not (inIntRange offset) then Nothing else Just ()
            let rightTerm = if offset == 0 then ATerm rightName else
                    FApp (CTerm (builtinFunct Plus)) [ATerm rightName, CTerm (VInt offset)]
            pure (ProofAssert (FApp (CTerm (builtinFunct (Rel Eq))) [ATerm leftName, rightTerm]))
        writeDeltas local = do
            let statementWrites =
                    [ (blockId, statement')
                    | blockId <- Set.toList region
                    , Just (M.BasicBlock statements _) <- [Map.lookup blockId blocks]
                    , statement' <- statements
                    , writesLocal local statement'
                    ]
                callWrites =
                    [ blockId
                    | blockId <- Set.toList region
                    , Just (M.BasicBlock _ (M.Call _ _ dest _)) <- [Map.lookup blockId blocks]
                    , dest == local
                    ]
                blockIds = map fst statementWrites
            if null statementWrites || not (null callWrites) then Nothing else Just ()
            if length blockIds /= length (nub blockIds) then Nothing else Just ()
            deltas <- mapM (\(blockId, statement') -> (,) blockId <$> pairWriteDelta local statement') statementWrites
            pure (Map.fromList deltas)
        pairWriteDelta local (M.Assign written (M.Use (M.Copy source)))
            | written == local && source == local = Just 0
        pairWriteDelta local (M.Assign written (M.BinaryOp M.Add (M.Copy source) (M.Const (M.CInt delta))))
            | written == local && source == local = Just delta
        pairWriteDelta local (M.Assign written (M.BinaryOp M.Add (M.Const (M.CInt delta)) (M.Copy source)))
            | written == local && source == local = Just delta
        pairWriteDelta local (M.Assign written (M.BinaryOp M.Sub (M.Copy source) (M.Const (M.CInt delta))))
            | written == local && source == local = Just (negate delta)
        pairWriteDelta _ _ = Nothing
    simpleLoopRegion = case M.loopBody spec of
        body | region == Set.fromList [header, body] -> case Map.lookup body blocks of
            Just (M.BasicBlock _ (M.Goto target)) -> target == header
            _ -> False
        _ -> False
    hasSinglePush local = case
        [ (blockId, statement')
        | blockId <- Set.toList region
        , Just (M.BasicBlock statements _) <- [Map.lookup blockId blocks]
        , statement' <- statements
        , writesLocal local statement'
        ] of
        [(blockId, M.Assign dest (M.ListOp M.Push [M.Copy source, _]))] ->
            blockId == M.loopBody spec && dest == local && source == local && not (any (hasNonAssignWrite local) (Set.toList region))
        _ -> False
    entryListLength local = do
        let incoming = filter (`Set.notMember` region) (predecessors header)
        if null incoming then Nothing else Just ()
        lengths <- mapM (listLengthAtBlockEnd Set.empty local) incoming
        case nub lengths of
            [lengthValue] -> Just lengthValue
            _ -> Nothing
    listLengthAtBlockEnd seen local blockId = do
        M.BasicBlock statements ending <- Map.lookup blockId blocks
        case ending of
            M.Call _ _ written _ | written == local -> Nothing
            _ -> listLengthBefore seen local blockId (length statements) statements
    listLengthBefore seen local blockId cutoff statements =
        case find (writesLocal local . snd) (reverse (zip [0 :: Int ..] (take cutoff statements))) of
            Just (index, M.Assign _ rvalue) -> listLengthRvalue (Set.insert (blockId, index, local) seen) blockId index statements rvalue
            _ -> Nothing
    listLengthRvalue seen blockId index statements rvalue = case rvalue of
        M.MakeList values -> Just (fromIntegral (length values))
        M.Use (M.Const (M.CList values)) -> Just (fromIntegral (length values))
        M.Use (M.Copy source) -> listLengthLocal seen blockId index statements source
        M.ListOp M.Push [M.Copy source, _] -> (+ 1) <$> listLengthLocal seen blockId index statements source
        M.ListOp M.Pop [M.Copy source] -> do
            previous <- listLengthLocal seen blockId index statements source
            if previous > 0 then Just (previous - 1) else Nothing
        _ -> Nothing
    listLengthLocal seen blockId index statements local
        | Set.member (blockId, index, local) seen = Nothing
        | otherwise = listLengthBefore seen local blockId index statements
    upperBoundProof _ _ initial (M.Const (M.CInt upper))
        | initial <= upper = Just (CTerm (VInt upper))
    upperBoundProof statements index initial (M.Copy upperLocal) = upperBoundLocal Set.empty statements index initial upperLocal
    upperBoundProof _ _ _ _ = Nothing
    upperBoundLocal seen statements index initial local
        | local `Set.notMember` loopAssigned = do
            name <- loopName local
            lower <- entryLowerBound local
            if lower >= initial then Just (ATerm name) else Nothing
        | Set.member local seen = Nothing
        | otherwise = do
            (writeIndex, M.Assign _ rvalue) <- find (writesLocal local . snd) (reverse (zip [0 :: Int ..] (take index statements)))
            upperBoundFromRvalue (Set.insert local seen) statements writeIndex initial rvalue
    upperBoundFromRvalue _ _ _ initial (M.ListOp M.Length [M.Copy listLocal])
        | initial <= 0 = do
            name <- loopName listLocal
            if listLocal `Set.notMember` loopAssigned then Just (FApp (CTerm (builtinFunct Size)) [ATerm name]) else Nothing
    upperBoundFromRvalue seen statements index initial (M.Use (M.Copy source)) = upperBoundLocal seen statements index initial source
    upperBoundFromRvalue _ _ _ _ _ = Nothing
    loopAssigned = Set.fromList assigned
    loopName local = do
        name <- M.localName =<< Map.lookup local (M.fnLocals fn)
        case Map.lookup name (M.loopEnv spec) of
            Just (M.Copy sameLocal) | sameLocal == local -> Just name
            _ -> Nothing
    entryConstant local = do
        let incoming = filter (`Set.notMember` region) (predecessors header)
        if null incoming then Nothing else Just ()
        values <- mapM (constantAtBlockEnd Set.empty local) incoming
        case nub values of
            [value] -> Just value
            _ -> Nothing
    entryLowerBound local = do
        name <- loopName local
        let constants = maybe [] (: []) (entryConstant local)
            contractBounds = mapMaybe (proofLowerBound name) (M.specRequires (M.fnSpec fn))
        case constants ++ contractBounds of
            [] -> Nothing
            bounds -> Just (maximum bounds)
    proofLowerBound name (ProofAssert (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel relation)) _)) [left, right])) =
        case (relation, left, right) of
            (GtEq, ATerm variable, CTerm (VInt bound)) | variable == name -> Just bound
            (Eq, ATerm variable, CTerm (VInt bound)) | variable == name -> Just bound
            (Gt, ATerm variable, CTerm (VInt bound)) | variable == name && inIntRange (bound + 1) -> Just (bound + 1)
            (LtEq, CTerm (VInt bound), ATerm variable) | variable == name -> Just bound
            (Eq, CTerm (VInt bound), ATerm variable) | variable == name -> Just bound
            (Lt, CTerm (VInt bound), ATerm variable) | variable == name && inIntRange (bound + 1) -> Just (bound + 1)
            _ -> Nothing
    proofLowerBound _ _ = Nothing
    unitIncrement local = case
        [ rvalue
        | blockId <- Set.toList region
        , Just (M.BasicBlock statements _) <- [Map.lookup blockId blocks]
        , M.Assign dest rvalue <- statements
        , dest == local
        ] of
        [M.BinaryOp M.Add (M.Copy source) (M.Const (M.CInt 1))] ->
            source == local && not (any (hasNonAssignWrite local) (Set.toList region))
        _ -> False
    hasNonAssignWrite local blockId = case Map.lookup blockId blocks of
        Nothing -> False
        Just (M.BasicBlock statements ending) ->
            any (\statement' -> writesLocal local statement' && case statement' of M.Assign _ _ -> False; _ -> True) statements
                || case ending of M.Call _ _ dest _ -> dest == local; _ -> False
    constantAtBlockEnd seen local blockId = do
        (M.BasicBlock statements ending) <- Map.lookup blockId blocks
        case ending of
            M.Call _ _ written _ | written == local -> Nothing
            _ -> constantBefore seen local blockId (length statements) statements
    constantBefore seen local blockId cutoff statements =
        case find (writesLocal local . snd) (reverse (zip [0 :: Int ..] (take cutoff statements))) of
            Just (index, M.Assign _ value) -> constantRvalue (Set.insert (blockId, index, local) seen) blockId index statements value
            Just _ -> Nothing
            Nothing -> Nothing
    constantRvalue seen blockId index statements rvalue = case rvalue of
        M.Use (M.Const (M.CInt value)) -> Just value
        M.Use (M.Copy source) -> constantLocal seen blockId index statements source
        M.BinaryOp operation left right | operation `elem` [M.Add, M.Sub, M.Mul] -> do
            leftValue <- constantOperand seen blockId index statements left
            rightValue <- constantOperand seen blockId index statements right
            let result = case operation of
                    M.Add -> leftValue + rightValue
                    M.Sub -> leftValue - rightValue
                    M.Mul -> leftValue * rightValue
                    _ -> 0
            if inIntRange result then Just result else Nothing
        _ -> Nothing
    constantOperand seen blockId index statements operand' = case operand' of
        M.Const (M.CInt value) -> Just value
        M.Copy source -> constantLocal seen blockId index statements source
        _ -> Nothing
    constantLocal seen blockId index statements local
        | Set.member (blockId, index, local) seen = Nothing
        | otherwise = case find (writesLocal local . snd) (reverse (zip [0 :: Int ..] (take index statements))) of
            Just (writeIndex, M.Assign _ value) -> constantRvalue (Set.insert (blockId, writeIndex, local) seen) blockId writeIndex statements value
            Just _ -> Nothing
            Nothing -> Nothing
    writesLocal local statement' = case statement' of
        M.Assign dest _ -> dest == local
        M.Peek dest _ -> dest == local
        M.Drop dest -> dest == local
        _ -> False
    writtenByNestedLoop local = any writesInNested
        [ nestedRegion
        | (nestedHeader, _) <- Map.toList (M.specLoops (M.fnSpec fn))
        , nestedHeader /= header
        , Set.member nestedHeader region
        , Just nestedRegion <- [Map.lookup nestedHeader (loopRegions fn)]
        ]
      where
        writesInNested nestedRegion = any writesInBlock (Set.toList nestedRegion)
        writesInBlock blockId = case Map.lookup blockId blocks of
            Nothing -> False
            Just (M.BasicBlock statements ending) ->
                any (writesLocal local) statements || case ending of
                    M.Call _ _ dest _ -> dest == local
                    _ -> False
    monotoneDirection :: M.Local -> Maybe Int
    monotoneDirection local = do
        let writes =
                [ case statement' of
                    M.Assign _ rvalue -> writeDelta local rvalue
                    _ -> Nothing
                | blockId <- Set.toList region
                , Just (M.BasicBlock statements _) <- [Map.lookup blockId blocks]
                , statement' <- statements
                , writesLocal local statement'
                ] ++
                [Nothing | blockId <- Set.toList region, Just (M.BasicBlock _ (M.Call _ _ dest _)) <- [Map.lookup blockId blocks], dest == local]
        if null writes || any isNothing writes then Nothing else do
            let deltas = catMaybes writes
            if all (>= 0) deltas then Just (if all (== 0) deltas then 0 else 1)
            else if all (<= 0) deltas then Just (-1)
            else Nothing
    writeDelta local rvalue = case rvalue of
        M.Use (M.Copy source) | source == local -> Just 0
        M.BinaryOp M.Add (M.Copy source) (M.Const (M.CInt delta)) | source == local && delta >= 0 -> Just delta
        M.BinaryOp M.Add (M.Const (M.CInt delta)) (M.Copy source) | source == local && delta >= 0 -> Just delta
        M.BinaryOp M.Sub (M.Copy source) (M.Const (M.CInt delta)) | source == local && delta >= 0 -> Just (negate delta)
        _ -> Nothing

-- A freshly constructed enum variant determines its tag and contributes the
-- corresponding positive variant fact to the flow context.
variantSteps :: Map.Map Name M.TypeDecl -> Name -> M.Local -> Build -> Maybe ([MirValue], Build)
variantSteps types variant (M.Local number) b0 = case find isConstructor (Map.toList types) of
    Just (familyName, M.EnumDecl constructors) ->
        let (family, b1) = namedFunction ("enum:" ++ familyName) b0
            (constructor, b2) = namedFunction ("ctor:" ++ variant) b1
            assume = step "AssumeVariant" [("value", record "ValueRef::Local" [("local", MInt (toInteger number))]), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool True)]
         in foldM assumeVariant ([assume], b2) [(name, name == variant) | (name, _) <- constructors]
    _ -> Just ([], b0)
  where
    isConstructor (_, M.EnumDecl constructors) = any ((== variant) . fst) constructors
    isConstructor _ = False
    assumeVariant (steps, b) (tag, matches) = do
        let (predicate, b1) = namedFunction ("is-variant:" ++ tag) b
            (i, b2) = fresh b1
            resultLocal = negate i - 1
            result = record "ValueRef::Local" [("local", MInt resultLocal)]
            value = record "ValueRef::Local" [("local", MInt (toInteger number))]
            apply = step "ApplyFresh" [("local", MInt resultLocal), ("function", MInt predicate), ("arguments", MList [value])]
        (expected, b3) <- operand (M.Const (M.CBool matches)) b2
        let known = step "Assume" [("relation", MInt 0), ("left", result), ("right", expected)]
        pure (steps ++ [apply, known], b3)

block :: Map.Map Name M.TypeDecl -> Map.Map Name ([Variable], [(Variable, Type)]) -> Map.Map Name [ValidationStatement] -> Map.Map Name M.Function -> Set.Set Name -> Maybe M.Local -> Set.Set M.Local -> Map.Map M.Local [M.Local] -> Bool -> Map.Map Name M.Local -> Map.Map Name M.Local -> M.Function -> (M.BlockId, M.BasicBlock) -> Build -> Maybe (MirValue, Build)
block types generics invariants functions worldReaders entryVariant partOrigins loopPartRoots allowCalls proofDefinitionLocals entryDefinitions fn (blockId@(M.BlockId n), M.BasicBlock stmts end) b0 = do
    (steps, b1, conditions, _) <- foldM (addAt blockId stmts) ([], b0, Map.empty, Map.map M.Copy entryDefinitions) (zip [0 :: Int ..] stmts)
    (extra, ending, b2) <- case (Map.lookup blockId (M.specLoops (M.fnSpec fn)), end) of
        (Just spec, M.SwitchBool (M.Copy local) yes no) -> do
            (loopSteps, loopEnd, b') <- encodeLoop spec local yes no conditions b1
            pure (loopSteps, loopEnd, b')
        (Just _, _) -> Nothing
        (Nothing, M.Return) -> do
            let env = Map.insert "return" (M.Copy (M.Local 0)) (M.specEnv (M.fnSpec fn))
            (postconditions, b') <- contractSteps False env (M.specEnsures (M.fnSpec fn)) b1
            let resultCheck = case M.fnReturns fn of
                    Just _ -> [step "RequireDefined" [("value", localRef 0)]]
                    Nothing -> []
            Just (resultCheck ++ postconditions, record "ExecutionEnd::Done" [], b')
        (Nothing, M.Unreachable) -> do
            (zero, b') <- operand (M.Const (M.CInt 0)) b1
            Just ([], record "ExecutionEnd::DeadEnd" [("zero", zero)], b')
        (Nothing, M.Goto target) -> Just ([], jump target, b1)
        (Nothing, M.SwitchBool (M.Const (M.CBool choice)) yes no) -> Just ([], jump (if choice then yes else no), b1)
        (Nothing, M.SwitchBool (M.Copy local) yes no) -> do
            let ref = localRef (localNumber local)
                required = step "RequireDefined" [("value", ref)]
                M.BlockId yesId = yes
                M.BlockId noId = no
                joinId = maybe (-1) (\(M.BlockId number) -> toInteger number) (joinBlock fn yes no)
            case variantCondition local of
                Just (_, variant) -> do
                    (family, constructor, predicate, b2) <- enumVariantFunctions types variant b1
                    let ending = record "ExecutionEnd::VariantBranch"
                            [("yes", MInt (toInteger yesId)), ("no", MInt (toInteger noId)), ("join", MInt joinId),
                             ("value", ref), ("family", MInt family), ("constructor", MInt constructor), ("predicate", MInt predicate)]
                    Just ([required], ending, b2)
                Nothing | isComparisonCondition local -> do
                    (relation, left, right) <- Map.lookup local conditions
                    let (kind, normalizedLeft, normalizedRight) = normal relation left right
                        ending = record "ExecutionEnd::Condition"
                            [("yes", MInt (toInteger yesId)), ("no", MInt (toInteger noId)), ("join", MInt joinId),
                             ("relation", MInt kind), ("left", normalizedLeft), ("right", normalizedRight)]
                    Just ([required], ending, b1)
                Nothing -> do
                    (trueRef, b2) <- operand (M.Const (M.CBool True)) b1
                    (falseRef, b3) <- operand (M.Const (M.CBool False)) b2
                    let ending = record "ExecutionEnd::BooleanBranch"
                            [("yes", MInt (toInteger yesId)), ("no", MInt (toInteger noId)), ("join", MInt joinId),
                             ("value", ref), ("trueValue", trueRef), ("falseValue", falseRef)]
                    Just ([required], ending, b3)
        (Nothing, M.Call calleeOperand args dest target) | allowCalls -> do
            names <- case staticFunctionTargets fn blockId stmts calleeOperand of
                Just known -> Just known
                Nothing -> functionTargetsForType functions fn calleeOperand
            callees <- mapM (`Map.lookup` functions) names
            (callSteps, b') <- case callees of
                [callee] -> directCall types generics invariants worldReaders entryVariant fn callee args dest b1
                _ -> indirectCall types generics invariants entryVariant fn callees args dest b1
            (typeFacts, b'') <- typeSteps types generics invariants fn dest b'
            Just (callSteps ++ typeFacts, jump target, b'')
        _ -> Nothing
    pure (record "ExecutionBlock" [("id", MInt (toInteger n)), ("steps", MList (steps ++ extra)), ("end", ending)], b2)
  where
    addAt currentBlock statements (steps, current, conditions, definitions) (index, currentStatement) =
        case add (steps, current{proofBlockContext = Just (currentBlock, take index statements)}, conditions, definitions) currentStatement of
            Nothing -> Nothing
            result -> result
    addLoopPart inner (steps, current) outer = do
        (more, next) <- withinFact inner outer current
        pure (steps ++ more, next)
    -- A loop is checked by its invariant: its region is walked once, and every
    -- edge back to the header has to re-establish the invariant and shrink the
    -- variant. A block that leaves the loop (a return, or an exit from inside
    -- the body) is not in the region and is walked as an exit, as the reference
    -- validator does.
    encodeLoop spec local yes no conditions b = do
        let region = Map.findWithDefault (Set.singleton blockId) blockId (loopRegions fn)
        if Set.member yes region && Set.member (M.loopBody spec) region && not (Set.member no region)
                && yes /= blockId && no /= blockId && no /= yes
            then Just ()
            else Nothing
        (kind, left, right, conditionBuild) <- case Map.lookup local conditions of
            Just (relation, a, c) ->
                let (conditionKind, conditionLeft, conditionRight) = normal relation a c
                 in Just (conditionKind, conditionLeft, conditionRight, b)
            Nothing -> do
                decl <- Map.lookup local (M.fnLocals fn)
                if M.localType decl == TBool then do
                    (trueRef, next) <- operand (M.Const (M.CBool True)) b
                    Just (0, localRef (localNumber local), trueRef, next)
                else Nothing
        (mode, variant, variantLocal, upperSpec) <- case M.loopTermination spec of
            Just (Counting (Var name)) -> case Map.lookup name (M.loopEnv spec) of
                Just op@(M.Copy v) -> Just (0, op, v, Left (M.Const (M.CInt 0)))
                _ -> Nothing
            Just (Counting (F (Val (VFunct _ _ _ (BuiltinFunct Minus) _)) [upperExpr, Var name])) -> do
                counter <- Map.lookup name (M.loopEnv spec)
                case counter of M.Copy v -> Just (1, counter, v, Right upperExpr); _ -> Nothing
            Just (Parts expression) -> do
                counter <- M.Copy <$> partRootLocal (M.loopEnv spec) expression
                case counter of
                    op@(M.Copy v) -> do
                        _ <- loopPartLocals fn region v
                        Just (2, op, v, Left (M.Const (M.CBool True)))
                    _ -> Nothing
            Just MayDiverge | mayDiverge fn ->
                let zero = M.Const (M.CInt 0)
                 in Just (3, zero, M.Local 0, Left zero)
            _ -> Nothing
        if mode == 3 then Just () else do
            decl <- Map.lookup variantLocal (M.fnLocals fn)
            if mode == 2 || M.localType decl == TInt then Just () else Nothing
        let assigned = nub
                [ v
                | member <- Set.toList region
                , Just (M.BasicBlock blockStmts term) <- [Map.lookup member (M.fnBlocks fn)]
                , v <- [d | M.Assign d _ <- blockStmts] ++ (case term of M.Call _ _ d _ -> [d]; _ -> [])
                ]
        case upperSpec of
            Left (M.Copy v) -> do
                upperDecl <- Map.lookup v (M.fnLocals fn)
                if M.localType upperDecl == TInt then Just () else Nothing
            Left (M.Const (M.CInt _)) -> Just ()
            Left (M.Const (M.CBool True)) | mode == 2 -> Just ()
            Right _ | mode == 1 -> Just ()
            _ -> Nothing
        (variantRef, b1) <- operand variant conditionBuild
        (upperSteps, upperRef, b2) <- debugMaybe ("loop upper expression " ++ M.fnName fn) $ case upperSpec of
            Left upper -> do
                (ref, next) <- operand upper b1
                Just ([], ref, next)
            Right expression -> proofOperand (M.loopEnv spec) (exprToProof expression) b1
        (zeroRef, b3) <- operand (M.Const (M.CInt 0)) b2
        let (variantFunction, b3a) = if mode == 2 then namedFunction "within" b3 else (0, b3)
        (typeAssumptions, withTypes) <- debugMaybe ("loop assigned types " ++ M.fnName fn) (foldM (loopType fn) ([], b3a) assigned)
        (checks, b4, _) <- debugMaybe ("loop invariant checks " ++ M.fnName fn) (contractStepsWith False (M.loopEnv spec) Map.empty (M.loopInvariant spec) withTypes)
        let inferred = inferredLoopBounds fn blockId region spec assigned
        (inferredChecks, b4a) <- debugMaybe ("inferred loop checks " ++ M.fnName fn) (contractSteps False (M.loopEnv spec) inferred b4)
        (invariantAssumptions, b5, _) <- debugMaybe ("loop invariant assumptions " ++ M.fnName fn) (contractStepsWith True (M.loopEnv spec) Map.empty (M.loopInvariant spec) b4a)
        (inferredAssumptions, b6) <- debugMaybe ("inferred loop assumptions " ++ M.fnName fn) (contractSteps True (M.loopEnv spec) inferred b5)
        let assumptions = typeAssumptions ++ invariantAssumptions ++ inferredAssumptions
            allChecks = checks ++ inferredChecks
        let M.BlockId exitId = no
            M.BlockId bodyId = yes
        let snapshotLocal = loopSnapshotLocal blockId
            snapshot = step "Assign" [("local", MInt (localNumber snapshotLocal)), ("value", variantRef)]
        pure (upperSteps ++ [snapshot], record "ExecutionEnd::Loop" [("exit", MInt (toInteger exitId)), ("body", MInt (toInteger bodyId)),
             ("region", MList [MInt (toInteger number) | M.BlockId number <- Set.toList region]),
             ("checks", MList allChecks), ("assumptions", MList assumptions), ("havoc", MList (map (MInt . localNumber) assigned)),
             ("relation", MInt kind), ("left", left), ("right", right), ("variant", variantRef), ("variantMode", MInt mode),
             ("variantOther", upperRef), ("variantFunction", MInt variantFunction), ("zero", zeroRef)], b6)
    loopType current (steps, b) local = do
        (more, b') <- typeSteps types generics invariants current local b
        pure (steps ++ more, b')
    debugMaybe _ result = result
    add (steps, b, conditions, definitions) (M.Ghost env (M.GhostValidation (AssignProofVar name expression))) = do
        let currentEnv = Map.union definitions env
        (prefix, value, b1) <- proofOperand currentEnv (exprToProof expression) b
        let (local, b2) = case Map.lookup name proofDefinitionLocals of
                Just (M.Local number) -> (toInteger number, b1)
                Nothing -> let (i, next) = fresh b1 in (negate i - 1, next)
            snapshot = step "Assign" [("local", MInt local), ("value", value)]
        if local < toInteger (minBound :: Int) then Nothing else Just ()
        pure (steps ++ prefix ++ [snapshot], b2, conditions,
              Map.insert name (M.Copy (M.Local (fromInteger local))) definitions)
    add (steps, b, conditions, definitions) s =
      let currentDefinitions = clearProofDefinition fn s definitions
          currentStatement = withProofDefinitions currentDefinitions s
       in case s of
        M.Assign dest (M.BinaryOp (M.Compare r) a c) -> do
            (left, b1) <- operand a b
            (right, b2) <- operand c b1
            let (x, b3) = fresh b2
                (y, b4) = fresh b3
                leftLocal = negate x - 1
                rightLocal = negate y - 1
                save i v = step "Assign" [("local", MInt i), ("value", v)]
            (more, b5) <- statement s b4
            (typeFacts, b6) <- typeSteps types generics invariants fn dest b5
            pure (steps ++ [save leftLocal left, save rightLocal right] ++ more ++ typeFacts, b6,
                  Map.insert dest (r, localRef leftLocal, localRef rightLocal) conditions, currentDefinitions)
        M.Assign dest (M.IsVariant _ _) -> do
            (more, b1) <- statement s b
            (typeFacts, b2) <- typeSteps types generics invariants fn dest b1
            (trueValue, b3) <- operand (M.Const (M.CBool True)) b2
            let predicate = localRef (localNumber dest)
            pure (steps ++ more ++ typeFacts, b3,
                  Map.insert dest (Eq, predicate, trueValue) conditions, currentDefinitions)
        M.Assign dest@(M.Local _) (M.ReadField (M.Copy source) _ _) -> do
            (more, b1) <- statement s b
            (typeFacts, b2) <- typeSteps types generics invariants fn dest b1
            (functionPartFacts, b3) <- case entryVariant of
                Just outer | Set.member source partOrigins -> withinFact dest outer b2
                _ -> Just ([], b2)
            (loopPartFacts, b4) <- foldM (addLoopPart dest) ([], b3) (Map.findWithDefault [] source loopPartRoots)
            pure (steps ++ more ++ typeFacts ++ functionPartFacts ++ loopPartFacts, b4, Map.delete dest conditions, currentDefinitions)
        M.Assign dest (M.MakeData name fields) -> do
            let base = maybe name fst (instanceOf name)
                clauses = Map.findWithDefault [] base invariants
            (checks, b1) <- contractSteps False (Map.fromList fields) clauses b
            (more, b2) <- statement s b1
            (typeFacts, b3) <- typeSteps types generics invariants fn dest b2
            (variantFacts, b4) <- variantSteps types name dest b3
            pure (steps ++ checks ++ more ++ typeFacts ++ variantFacts, b4, Map.delete dest conditions, currentDefinitions)
        M.Assign dest (M.ListOp M.NewArray [lengthValue, _]) -> do
            decl <- Map.lookup dest (M.fnLocals fn)
            case M.localType decl of
                TArrayOf _ (SizeParam name) ->
                    case [p | p <- drop (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn), Just d <- [Map.lookup p (M.fnLocals fn)], M.localName d == Just name] of
                        p : _ | lengthValue == M.Copy p -> Just ()
                        _ -> Nothing
                _ -> Just ()
            (more, b1) <- statement s b
            (typeFacts, b2) <- typeSteps types generics invariants fn dest b1
            pure (steps ++ more ++ typeFacts, b2, Map.delete dest conditions, currentDefinitions)
        M.Assign dest _ | isFunctionLocal fn dest -> do
            (more, b') <- statement currentStatement b
            pure (steps ++ more, b', Map.delete dest conditions, currentDefinitions)
        M.Assign dest _ -> do
            (more, b') <- statement s b
            (typeFacts, b'') <- typeSteps types generics invariants fn dest b'
            pure (steps ++ more ++ typeFacts, b'', Map.delete dest conditions, currentDefinitions)
        _ -> do
            (more, b') <- statement currentStatement b
            pure (steps ++ more, b', conditions, currentDefinitions)

    clearProofDefinition current (M.Assign (M.Local local) _) definitions = case M.localName =<< Map.lookup (M.Local local) (M.fnLocals current) of
        Just name -> Map.delete name definitions
        Nothing -> definitions
    clearProofDefinition _ _ definitions = definitions
    withProofDefinitions definitions (M.Ghost env ghost) = M.Ghost (Map.union definitions env) ghost
    withProofDefinitions _ other = other

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

    isComparisonCondition (M.Local target) = inspect (reverse stmts)
      where
        inspect [] = False
        inspect (M.Assign (M.Local written) (M.BinaryOp (M.Compare _) _ _) : _) | written == target = True
        inspect (M.Assign (M.Local written) _ : _) | written == target = False
        inspect (M.Peek (M.Local written) (M.BinaryOp (M.Compare _) _ _) : _) | written == target = True
        inspect (M.Peek (M.Local written) _ : _) | written == target = False
        inspect (_ : rest) = inspect rest

    variantCondition (M.Local target) = inspect target (reverse stmts)
      where
        inspect _ [] = Nothing
        inspect local (M.Assign (M.Local written) (M.IsVariant (M.Copy source) variant) : _) | written == local = Just (source, variant)
        inspect local (M.Peek (M.Local written) (M.IsVariant (M.Copy source) variant) : _) | written == local = Just (source, variant)
        inspect local (M.Assign (M.Local written) (M.Use (M.Copy (M.Local source))) : rest) | written == local = inspect source rest
        inspect local (M.Peek (M.Local written) (M.Use (M.Copy (M.Local source))) : rest) | written == local = inspect source rest
        inspect local (M.Assign (M.Local written) _ : _) | written == local = Nothing
        inspect local (M.Peek (M.Local written) _ : _) | written == local = Nothing
        inspect local (M.Drop (M.Local written) : _) | written == local = Nothing
        inspect local (_ : rest) = inspect local rest

isFunctionLocal :: M.Function -> M.Local -> Bool
isFunctionLocal fn local = case M.localType <$> Map.lookup local (M.fnLocals fn) of
    Just TFn{} -> True
    _ -> False

-- Pick the nearest common reachable block for a boolean branch, excluding
-- loop headers because their back-edge checks belong to the loop walker.
joinBlock :: M.Function -> M.BlockId -> M.BlockId -> Maybe M.BlockId
joinBlock fn yes no = case candidates of
    [] -> Nothing
    _ -> Just (minimumBy (comparing score) candidates)
  where
    blocks = M.fnBlocks fn
    loopHeaders = Map.keysSet (M.specLoops (M.fnSpec fn))
    distances :: M.BlockId -> Map.Map M.BlockId Int
    distances start = visit [(start, 0)] Map.empty
    visit :: [(M.BlockId, Int)] -> Map.Map M.BlockId Int -> Map.Map M.BlockId Int
    visit [] seen = seen
    visit ((current, distance) : rest) seen
        | Map.member current seen = visit rest seen
        | otherwise =
            let next = maybe [] (M.successors . M.blockTerminator) (Map.lookup current blocks)
             in visit (rest ++ [(target, distance + 1) | target <- next, Map.notMember target seen]) (Map.insert current distance seen)
    fromYes = distances yes
    fromNo = distances no
    candidates =
        [ candidate
        | candidate <- Map.keys fromYes
        , Map.member candidate fromNo
        , candidate /= yes
        , candidate /= no
        , Set.notMember candidate loopHeaders
        ]
    score candidate =
        let a = fromYes Map.! candidate
            b = fromNo Map.! candidate
         in (max a b, a + b, candidate)

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

proofVariablesInStatement :: M.Statement -> [Name]
proofVariablesInStatement (M.Ghost _ (M.GhostValidation validation)) = case validation of
    ProofAssert proof -> proofVars proof
    AssignProofVar _ expression -> proofVars (exprToProof expression)
    Rewrite (Refl proof) -> proofVars proof
    Rewrite (CheckGtZero proof) -> proofVars proof
    Rewrite (CheckRel proof) -> proofVars proof
    Rewrite (UserRewrite _ arguments) -> concatMap proofVars arguments
    Rewrite (Eval name) -> [name]
    Rewrite EvalAll -> []
proofVariablesInStatement _ = []

unboundProofVariables :: M.Env -> VariableProof -> [Variable]
unboundProofVariables env proof = case proof of
    CTerm _ -> []
    ATerm name -> [name | Map.notMember name env]
    BVar _ -> []
    Forall index guards body ->
        let boundEnv = Map.insert index (M.Copy (M.Local 0)) env
         in concatMap (unboundProofVariables boundEnv) guards ++ unboundProofVariables boundEnv body
    -- ATerm functions such as toInt and size are builtin aliases, not proof
    -- variables. The operand encoder resolves (or rejects) unsupported calls.
    FApp _ arguments -> concatMap (unboundProofVariables env) arguments

proofDefinitionPlan :: M.Function -> Maybe (Map.Map Name M.Local, Map.Map M.BlockId (Map.Map Name M.Local))
proofDefinitionPlan fn = do
    let definitions =
            [ (name, blockId, index)
            | (blockId, basicBlock) <- Map.toList blocks
            , Set.member blockId reachable
            , (index, M.Ghost _ (M.GhostValidation (AssignProofVar name _))) <- zip [0 :: Int ..] (M.blockStatements basicBlock)
            ]
        uses =
            [ (blockId, index, name)
            | (blockId, basicBlock) <- Map.toList blocks
            , Set.member blockId reachable
            , (index, candidate) <- zip [0 :: Int ..] (M.blockStatements basicBlock)
            , name <- proofVariablesInStatement candidate
            ]
        specUses = concatMap validationVariables (M.specRequires spec ++ M.specEnsures spec)
            ++ concat [concatMap validationVariables (M.loopInvariant loop) | loop <- Map.elems (M.specLoops spec)]
        grouped = Map.fromListWith (++) [(name, [(blockId, index)]) | (name, blockId, index) <- definitions]
        reachable = reachableBlocks fn
        doms = dominators fn reachable
        sourceNames = Set.fromList [name | decl <- Map.elems (M.fnLocals fn), Just name <- [M.localName decl]]
        useAfter defBlock defIndex (useBlock, useIndex, _) =
            if useBlock == defBlock then defIndex < useIndex
            else Set.member defBlock (Map.findWithDefault Set.empty useBlock doms)
        validDefinition (name, sites) =
            name `notElem` specUses
                && case sites of
                    [(defBlock, defIndex)] ->
                        all (useAfter defBlock defIndex) [use | use@(_, _, usedName) <- uses, usedName == name]
                            && (name `Set.notMember` sourceNames || all ((== defBlock) . first3) [use | use@(_, _, usedName) <- uses, usedName == name])
                    _ -> case sites of
                        (defBlock, _) : more ->
                            let nameUses = [use | use@(_, _, usedName) <- uses, usedName == name]
                             in null nameUses || (all ((== defBlock) . fst) more && all ((== defBlock) . first3) nameUses)
                        [] -> True
        first3 (a, _, _) = a
    if all validDefinition (Map.toList grouped) then Just () else Nothing
    let crossBlockNames =
            [ name
            | (name, [(defBlock, _)]) <- Map.toList grouped
            , any (\(useBlock, _, usedName) -> usedName == name && useBlock /= defBlock) uses
            ]
        orderedNames = nub crossBlockNames
        maxLocal = maximum (0 : [toInteger number | M.Local number <- Map.keys (M.fnLocals fn)])
        firstLocal = maxLocal + 1
        lastLocal = firstLocal + toInteger (length orderedNames) - 1
    if not (null orderedNames) && lastLocal > toInteger (maxBound :: Int) then Nothing else Just ()
    let planned = Map.fromList (zip orderedNames [M.Local (fromInteger number) | number <- [firstLocal ..]])
        entries = Map.fromList
            [ (blockId, Map.fromList
                [ (name, local)
                | (name, [(defBlock, _)]) <- Map.toList grouped
                , Just local <- [Map.lookup name planned]
                , defBlock /= blockId
                , Set.member defBlock (Map.findWithDefault Set.empty blockId doms)
                ])
            | blockId <- Map.keys blocks
            ]
    pure (planned, entries)
  where
    blocks = M.fnBlocks fn
    spec = M.fnSpec fn
    validationVariables (ProofAssert proof) = proofVars proof
    validationVariables (AssignProofVar _ expression) = proofVars (exprToProof expression)
    validationVariables (Rewrite (Refl proof)) = proofVars proof
    validationVariables (Rewrite (CheckGtZero proof)) = proofVars proof
    validationVariables (Rewrite (CheckRel proof)) = proofVars proof
    validationVariables (Rewrite (UserRewrite _ arguments)) = concatMap proofVars arguments
    validationVariables (Rewrite (Eval name)) = [name]
    validationVariables (Rewrite EvalAll) = []
-- Proof-variable dominance may ignore an edge only when its condition is
-- statically known from constants copied along every predecessor path.
cfgSuccessors :: M.Function -> M.BlockId -> [M.BlockId]
cfgSuccessors fn blockId = case Map.lookup blockId (M.fnBlocks fn) of
    Nothing -> []
    Just basicBlock -> case M.blockTerminator basicBlock of
        M.SwitchBool condition yes no -> case resolveBoolean fn Set.empty blockId (M.blockStatements basicBlock) condition of
            Just True -> [yes]
            Just False -> [no]
            Nothing -> [yes, no]
        terminator -> M.successors terminator

resolveBoolean :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> M.Operand -> Maybe Bool
resolveBoolean _ _ _ _ (M.Const (M.CBool value)) = Just value
resolveBoolean fn seen blockId statements (M.Copy local) = resolveBooleanLocal fn seen blockId statements local
resolveBoolean _ _ _ _ _ = Nothing

resolveBooleanLocal :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> M.Local -> Maybe Bool
resolveBooleanLocal fn seen blockId statements local
    | Set.member key seen = Nothing
    | otherwise = case find (writes local . snd) (reverse (zip [0 :: Int ..] statements)) of
        Just (index, M.Assign _ (M.Use operand')) -> resolveBoolean fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Peek _ (M.Use operand')) -> resolveBoolean fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Assign _ (M.BinaryOp (M.Compare relation) left right)) ->
            resolveComparison fn (Set.insert key seen) blockId (take index statements) relation left right
        Just (index, M.Peek _ (M.BinaryOp (M.Compare relation) left right)) ->
            resolveComparison fn (Set.insert key seen) blockId (take index statements) relation left right
        Just (index, M.Assign _ (M.IsVariant source variant)) -> do
            actual <- resolveVariant fn (Set.insert key seen) blockId (take index statements) source
            Just (actual == variant)
        Just (index, M.Peek _ (M.IsVariant source variant)) -> do
            actual <- resolveVariant fn (Set.insert key seen) blockId (take index statements) source
            Just (actual == variant)
        Just _ -> Nothing
        Nothing -> fromPredecessors (Set.insert key seen)
  where
    key = (blockId, local, length statements)
    writes target (M.Assign dest _) = target == dest
    writes target (M.Peek dest _) = target == dest
    writes target (M.Drop dest) = target == dest
    writes _ _ = False
    fromPredecessors visited
        | blockId == M.BlockId 0 = Nothing
        | otherwise = case predecessors of
            [] -> Nothing
            first : rest -> do
                firstValue <- resolveBooleanLocal fn visited first (M.blockStatements (M.fnBlocks fn Map.! first)) local
                values <- mapM (\predecessor -> resolveBooleanLocal fn visited predecessor (M.blockStatements (M.fnBlocks fn Map.! predecessor)) local) rest
                if all (== firstValue) values then Just firstValue else Nothing
      where
        predecessors =
            [ predecessor
            | (predecessor, basicBlock) <- Map.toList (M.fnBlocks fn)
            , blockId `elem` M.successors (M.blockTerminator basicBlock)
            ]

resolveComparison :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> Rel -> M.Operand -> M.Operand -> Maybe Bool
resolveComparison fn seen blockId statements relation left right = do
    leftValue <- resolveInteger fn seen blockId statements left
    rightValue <- resolveInteger fn seen blockId statements right
    pure $ case relation of
        Eq -> leftValue == rightValue
        NotEq -> leftValue /= rightValue
        Lt -> leftValue < rightValue
        LtEq -> leftValue <= rightValue
        Gt -> leftValue > rightValue
        GtEq -> leftValue >= rightValue

resolveInteger :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> M.Operand -> Maybe Integer
resolveInteger _ _ _ _ (M.Const (M.CInt value)) = Just value
resolveInteger fn seen blockId statements (M.Copy local) = resolveIntegerLocal fn seen blockId statements local
resolveInteger _ _ _ _ _ = Nothing

resolveIntegerLocal :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> M.Local -> Maybe Integer
resolveIntegerLocal fn seen blockId statements local
    | Set.member key seen = Nothing
    | otherwise = case find (writes local . snd) (reverse (zip [0 :: Int ..] statements)) of
        Just (index, M.Assign _ (M.Use operand')) -> resolveInteger fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Peek _ (M.Use operand')) -> resolveInteger fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Assign _ (M.BinaryOp operation left right)) ->
            resolveArithmetic fn (Set.insert key seen) blockId (take index statements) operation left right
        Just (index, M.Peek _ (M.BinaryOp operation left right)) ->
            resolveArithmetic fn (Set.insert key seen) blockId (take index statements) operation left right
        Just _ -> Nothing
        Nothing -> fromPredecessors (Set.insert key seen)
  where
    key = (blockId, local, length statements)
    writes target (M.Assign dest _) = target == dest
    writes target (M.Peek dest _) = target == dest
    writes target (M.Drop dest) = target == dest
    writes _ _ = False
    fromPredecessors visited
        | blockId == M.BlockId 0 = Nothing
        | otherwise = case predecessors of
            [] -> Nothing
            first : rest -> do
                firstValue <- resolveIntegerLocal fn visited first (M.blockStatements (M.fnBlocks fn Map.! first)) local
                values <- mapM (\predecessor -> resolveIntegerLocal fn visited predecessor (M.blockStatements (M.fnBlocks fn Map.! predecessor)) local) rest
                if all (== firstValue) values then Just firstValue else Nothing
      where
        predecessors =
            [ predecessor
            | (predecessor, basicBlock) <- Map.toList (M.fnBlocks fn)
            , blockId `elem` M.successors (M.blockTerminator basicBlock)
            ]

resolveVariant :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> M.Operand -> Maybe Name
resolveVariant _ _ _ _ (M.Const (M.CData name _)) = Just name
resolveVariant fn seen blockId statements (M.Copy local) = resolveVariantLocal fn seen blockId statements local
resolveVariant _ _ _ _ _ = Nothing

resolveVariantLocal :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> M.Local -> Maybe Name
resolveVariantLocal fn seen blockId statements local
    | Set.member key seen = Nothing
    | otherwise = case find (writes local . snd) (reverse (zip [0 :: Int ..] statements)) of
        Just (_, M.Assign _ (M.MakeData name _)) -> Just name
        Just (index, M.Assign _ (M.Use operand')) -> resolveVariant fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Assign _ (M.MakeBox operand')) -> resolveVariant fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Assign _ (M.Unbox operand')) -> resolveVariant fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Assign _ (M.Unsize operand')) -> resolveVariant fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Assign _ (M.Clone operand')) -> resolveVariant fn (Set.insert key seen) blockId (take index statements) operand'
        Just (index, M.Assign _ (M.AsVariant operand' _)) -> resolveVariant fn (Set.insert key seen) blockId (take index statements) operand'
        Just (_, M.Peek _ (M.MakeData name _)) -> Just name
        Just (index, M.Peek _ (M.Use operand')) -> resolveVariant fn (Set.insert key seen) blockId (take index statements) operand'
        Just _ -> Nothing
        Nothing -> fromPredecessors (Set.insert key seen)
  where
    key = (blockId, local, length statements)
    writes target (M.Assign dest _) = target == dest
    writes target (M.Peek dest _) = target == dest
    writes target (M.Drop dest) = target == dest
    writes _ _ = False
    fromPredecessors visited
        | blockId == M.BlockId 0 = Nothing
        | otherwise = case predecessors of
            [] -> Nothing
            first : rest -> do
                firstValue <- resolveVariantLocal fn visited first (M.blockStatements (M.fnBlocks fn Map.! first)) local
                values <- mapM (\predecessor -> resolveVariantLocal fn visited predecessor (M.blockStatements (M.fnBlocks fn Map.! predecessor)) local) rest
                if all (== firstValue) values then Just firstValue else Nothing
      where
        predecessors =
            [ predecessor
            | (predecessor, basicBlock) <- Map.toList (M.fnBlocks fn)
            , blockId `elem` M.successors (M.blockTerminator basicBlock)
            ]

resolveArithmetic :: M.Function -> Set.Set (M.BlockId, M.Local, Int) -> M.BlockId -> [M.Statement] -> M.BinOp -> M.Operand -> M.Operand -> Maybe Integer
resolveArithmetic fn seen blockId statements operation left right = do
    leftValue <- resolveInteger fn seen blockId statements left
    rightValue <- resolveInteger fn seen blockId statements right
    result <- case operation of
        M.Add -> Just (leftValue + rightValue)
        M.Sub -> Just (leftValue - rightValue)
        M.Mul -> Just (leftValue * rightValue)
        M.Div | rightValue /= 0 -> Just (leftValue `div` rightValue)
        M.Mod | rightValue /= 0 -> Just (leftValue `mod` rightValue)
        _ -> Nothing
    if inIntRange result then Just result else Nothing

reachableBlocks :: M.Function -> Set.Set M.BlockId
reachableBlocks fn = visit Set.empty [M.BlockId 0]
  where
    visit seen [] = seen
    visit seen (blockId : rest)
        | Set.member blockId seen = visit seen rest
        | otherwise =
            let next = cfgSuccessors fn blockId
             in visit (Set.insert blockId seen) (rest ++ next)

dominators :: M.Function -> Set.Set M.BlockId -> Map.Map M.BlockId (Set.Set M.BlockId)
dominators fn reachable = fixedPoint initial
  where
    entry = M.BlockId 0
    blocks = M.fnBlocks fn
    predecessors = Map.fromListWith (++)
        [ (target, [source])
        | source <- Set.toList reachable
        , Map.member source blocks
        , target <- cfgSuccessors fn source
        , Set.member target reachable
        ]
    initial = Map.fromSet (\blockId -> if blockId == entry then Set.singleton entry else reachable) reachable
    updateDominators current = Map.mapWithKey update current
      where
        update blockId _
            | blockId == entry = Set.singleton entry
            | otherwise = Set.insert blockId (case Map.findWithDefault [] blockId predecessors of
                first : rest -> foldl Set.intersection (Map.findWithDefault Set.empty first current)
                    [Map.findWithDefault Set.empty predecessor current | predecessor <- rest]
                [] -> Set.empty)
    fixedPoint current =
        let next = updateDominators current
         in if next == current then current else fixedPoint next

encodeFunction :: Map.Map Name M.TypeDecl -> Map.Map Name ([Variable], [(Variable, Type)]) -> Map.Map Name [ValidationStatement] -> Map.Map Name M.Function -> Set.Set Name -> Map.Map Name M.Function -> RuleContext -> Bool -> M.Function -> Maybe (MirValue, MirValue, Integer)
encodeFunction types generics invariants functions worldReaders callableFunctions initialRules allowCalls fn
    | any (\(M.Local n) -> n < 0) (Map.keys (M.fnLocals fn)) = Nothing
    | length (M.fnParams fn) /= length (nub (M.fnParams fn)) = Nothing
    | M.Local 0 `elem` M.fnParams fn = Nothing
    | length (M.fnSizeParams fn) > length (M.fnParams fn) = Nothing
    | length (M.fnSizeParams fn) /= length (nub (M.fnSizeParams fn)) = Nothing
    | any ambiguousSizeName (M.fnSizeParams fn) = Nothing
    | any parameterAssigned sizeParams = Nothing
    | any wrongSizeName (zip sizeParams (M.fnSizeParams fn)) = Nothing
    | not (supportedTermination (M.specTermination spec)) = Nothing
    | Map.member (M.BlockId (-1)) (M.fnBlocks fn) = Nothing
    | otherwise = do
        (proofDefinitionLocals, proofDefinitionsAtEntry) <- proofDefinitionPlan fn
        let initialBuild = (emptyBuild enumInfo initialRules callableFunctions types generics invariants worldReaders fn)
                { proofCandidateFunctions = functions }
            (params, start) = foldl addParam ([], initialBuild) (M.fnParams fn)
        (paramFacts, withTypes) <- foldM addType ([], start) (M.fnParams fn)
        (sizeFacts, withSizes) <- sizeParameterSteps True fn (M.fnParams fn) withTypes
        (requires, withRequires, definitions) <- contractStepsWith True (M.specEnv spec) Map.empty (M.specRequires spec) withSizes
        (variantFacts, entryVariant, partOrigins, withVariant) <- functionVariantSteps fn withRequires
        let scopedFunction = withContractDefinitions definitions fn
        (blocks, b) <- foldM (add entryVariant partOrigins proofDefinitionLocals proofDefinitionsAtEntry scopedFunction) ([], withVariant) (Map.toList (M.fnBlocks scopedFunction))
        let context = record "ValidatorContext" [("equalities", MList []), ("applications", MList (literalApps b)), ("constants", MList (literalTerms b)), ("orders", MList []), ("different", MList []), ("variants", MList [record "VariantFact" [("object", MInt object), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool True)] | (object, family, constructor) <- literalVariants b]), ("fieldFunctions", MList [MInt i | (name, i) <- namedFunctions b, take 6 name == "field:" || take 8 name == "project:"]), ("constructorFunctions", MList [MInt i | (name, i) <- namedFunctions b, take 5 name == "ctor:"]), ("constructorFields", MList (constructorFieldTerms types (namedFunctions b))), ("differences", MList []), ("universals", MList [])]
            entry = record "ExecutionBlock" [("id", MInt (-1)), ("steps", MList (paramFacts ++ sizeFacts ++ requires ++ variantFacts)), ("end", record "ExecutionEnd::Jump" [("target", MInt 0)])]
        pure (MList (entry : blocks), record "ExecutionState" [("context", context), ("locals", MList params)], -1)
  where
    spec = M.fnSpec fn
    enumInfo = [(name, map fst variants) | (name, M.EnumDecl variants) <- Map.toList types]
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
    supportedTermination Nothing = True
    supportedTermination (Just MayDiverge) = True
    supportedTermination (Just (Counting _)) = True
    supportedTermination (Just (Parts _)) = True
    supportedTermination _ = False
    addParam (params, b) (M.Local local) =
        let (term, b') = fresh b
            binding = record "LocalBinding" [("local", MInt (toInteger local)), ("term", MInt term)]
         in (params ++ [binding], b')
    addType (steps, b) local = do
        (more, b') <- typeSteps types generics invariants fn local b
        pure (steps ++ more, b')
    add entryVariant partOrigins proofDefinitionLocals proofDefinitionsAtEntry scopedFunction (blocks, b) entry@(blockId, _) = do
        let entryDefinitions = Map.findWithDefault Map.empty blockId proofDefinitionsAtEntry
        (v, b') <- case block types generics invariants functions worldReaders entryVariant partOrigins (loopPartRootsForBlock fn blockId) allowCalls proofDefinitionLocals entryDefinitions scopedFunction entry b of
            Nothing -> Nothing
            result -> result
        pure (blocks ++ [v], b')

encode :: M.Program -> Maybe [(MirValue, MirValue, Integer)]
encode program
    -- Results of world-reading functions are not determined by arguments.
    | not (null (M.fnParams (M.progMain program))) = Nothing
    | not (null (M.specRequires mainSpec) && null (M.specEnsures mainSpec)) = Nothing
    | any invalidDefinition definitions = Nothing
    | any invalidRuleSite ruleSites = Nothing
    | length ruleNames /= length (nub ruleNames) = Nothing
    | any (`Map.member` stdLibRuleCtx) ruleNames = Nothing
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
            generics = M.progGenerics program
            worldReaders = M.readersOfInput program
            functionRules = rulesAtDefinitions (M.progMain program)
            functionOrder = Map.fromList (zip targets [0 :: Int ..])
            callableBefore fn = Map.filterWithKey (\name _ -> Map.findWithDefault maxBound name functionOrder < Map.findWithDefault maxBound (M.fnName fn) functionOrder) functions
        checked <- traverse (\fn -> case encodeFunction types generics invariants functions worldReaders (callableBefore fn) (Map.findWithDefault stdLibRuleCtx (M.fnName fn) functionRules) True fn of
                Nothing -> Nothing
                result -> result) (Map.elems functions)
        main <- encodeFunction types generics invariants functions worldReaders functions stdLibRuleCtx True (M.progMain program)
        pure (checked ++ [main])
  where
    mainSpec = M.fnSpec (M.progMain program)
    definitions = [(isMain, blockId, name, source, top) | (isMain, fn) <- (True, M.progMain program) : [(False, f) | f <- Map.elems (M.progFunctions program)],
        (blockId, block') <- Map.toList (M.fnBlocks fn), M.Ghost _ (M.GhostFunction name source top) <- M.blockStatements block']
    ruleSites = [(isMain, blockId, name) | (isMain, fn) <- (True, M.progMain program) : [(False, f) | f <- Map.elems (M.progFunctions program)],
        (blockId, block') <- Map.toList (M.fnBlocks fn), mirStatement <- M.blockStatements block',
        name <- case mirStatement of
            M.Ghost _ (M.GhostAxiom ruleName _ _ _) -> [ruleName]
            M.Ghost _ (M.GhostProof ruleName _ _ _ _) -> [ruleName]
            _ -> []]
    ruleNames = [name | (_, _, name) <- ruleSites]
    names = [source | (_, _, _, source, _) <- definitions]
    targets = [name | (_, _, name, _, _) <- definitions]
    invalidDefinition (isMain, blockId, _, _, top) = not top || not isMain || blockId /= M.BlockId 0
    invalidRuleSite (isMain, blockId, _) = not isMain || blockId /= M.BlockId 0
    rulesAtDefinitions main = case Map.lookup (M.BlockId 0) (M.fnBlocks main) of
        Nothing -> Map.empty
        Just basicBlock -> snd (foldl collect (stdLibRuleCtx, Map.empty) (M.blockStatements basicBlock))
    collect (rules, byFunction) (M.Ghost _ (M.GhostAxiom name parameters inputs outputs)) =
        (Map.insert name (AxiomRule parameters inputs outputs) rules, byFunction)
    collect (rules, byFunction) (M.Ghost _ (M.GhostProof name parameters inputs outputs body)) =
        let rule = case proofRuleExports rules inputs body outputs of
                Just exported -> ProofRule parameters inputs exported
                Nothing -> AxiomRule parameters inputs outputs
         in (Map.insert name rule rules, byFunction)
    collect (rules, byFunction) (M.Ghost _ (M.GhostFunction functionName _ True)) =
        (rules, Map.insert functionName rules byFunction)
    collect state _ = state
    definitionOrder = Map.fromList (zip targets [0 :: Int ..])
    functionCalls =
        [ (name, called)
        | (name, fn) <- Map.toList (M.progFunctions program)
        , (blockId, basicBlock) <- Map.toList (M.fnBlocks fn)
        , M.Call callee _ _ _ <- [M.blockTerminator basicBlock]
        , Just calledNames <- [staticFunctionTargets fn blockId (M.blockStatements basicBlock) callee]
        , called <- calledNames
        ]
    invalidCall (caller, called) | caller == called = False
    invalidCall (caller, called) = case (Map.lookup caller definitionOrder, Map.lookup called definitionOrder) of
        (Just callerIndex, Just calledIndex) -> calledIndex >= callerIndex
        _ -> True

-- The first argument is the validated lib/validation.tersus program. A false
-- result means a supported obligation failed or a known termination rule is
-- violated; Nothing means the MIR is outside this bridge's current subset.
validateMirSubset :: M.Program -> M.Program -> Result (Maybe Bool) String
validateMirSubset checker program = verifyProgram program `bindResult` \_ ->
    if hasUnannotatedRecursion program
        then Ok (Just False)
        else case encode program of
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

-- A recursive cycle without a termination clause is rejected by the
-- reference validator before any proof obligations in its body are useful.
-- Recognize statically resolved cycles here so they need not fall back.
hasUnannotatedRecursion :: M.Program -> Bool
hasUnannotatedRecursion program = any invalid (Map.elems functions)
  where
    functions = M.progFunctions program
    calls =
        [ (M.fnName fn, called)
        | fn <- Map.elems functions
        , (blockId, basicBlock) <- Map.toList (M.fnBlocks fn)
        , M.Call callee _ _ _ <- [M.blockTerminator basicBlock]
        , Just calledNames <- [staticFunctionTargets fn blockId (M.blockStatements basicBlock) callee]
        , called <- calledNames
        , Map.member called functions
        ]
    invalid fn =
        M.specTermination (M.fnSpec fn) == Nothing
            && reaches (M.fnName fn) (M.fnName fn) Set.empty
    reaches source target visited
        | Set.member source visited = False
        | otherwise = any next (successors source)
      where
        next destination = destination == target || reaches destination target (Set.insert source visited)
        successors name = [destination | (caller, destination) <- calls, caller == name]

-- Compile the checker without routing it through Pipeline (which calls this
-- fast path). The top-level Result is a shared thunk, so the embedded source
-- is parsed and lowered once per process.
checkerProgram :: Result M.Program String
checkerProgram = case parseStatementBlockWith (locating emptyDecls) preludeSource of
    Left err -> Error ("Could not parse the Tersus validator prelude: " ++ show err)
    Right (prelude, declarations) -> case parseStatementBlockWith declarations validationSource of
        Left err -> Error ("Could not parse the Tersus validator: " ++ show err)
        Right (statements, _) ->
            elaborate (prelude ++ statements) `bindResult` lowerElaborated `bindResult` \program ->
                verifyProgram program `bindResult` \_ -> Ok program

-- The production pipeline uses this for programs the self-hosted checker can
-- encode. Nothing means the caller must use the reference implementation.
validateMir :: M.Program -> Result (Maybe Bool) String
validateMir program = checkerProgram `bindResult` \checker -> validateMirSubset checker program
