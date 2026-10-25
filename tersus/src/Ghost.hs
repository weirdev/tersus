module Ghost
    ( checkStatements
    , runStatements
    , assumeStatements
    , defineAxiom
    , defineProofRule
    , exportOutputs
    , exportContract
    , applyCall
    , builtinInfo
    , rvalueCall
    , wrapperInfo
    , resolveFunction
    , unreachable
    , noteDivergence
    , variantOf
    , entryVariantName
    , boundedBelow
    , variantStatements
    , smallerThan
    , variantFailure
    , prefixError
    , maxJoinCandidates
    , checkInvariant
    , invariantFacts
    ) where

import Control.Monad (foldM, when)
import Data.Containers.ListUtils (nubOrd)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (mapMaybe)

import qualified ProofEngine as Engine
import Pretty (renderVarProof)
import ProofHelpers
    ( iotaProofToVarProof
    , namedIotaMap
    , proofOnlyOfNamedIotasOrConst
    , proofVars
    , valStmtDefinedVars
    )
import qualified Mir as M
import ProofState
import StdLib
import TersusTypes
import Utils

-- Statements for the validator: affirm, define and rewrite, which the program writes, and the rules it defines

-- Checks each statement in turn, in the state: an affirm has to be proved
runStatements :: PState -> [ValidationStatement] -> V PState
runStatements = foldM runStatement

-- As runStatements, for a check whose result is only whether it passed
checkStatements :: PState -> [ValidationStatement] -> V ()
checkStatements st stmts = () <$ runStatements st stmts

runStatement :: PState -> ValidationStatement -> V PState
runStatement st (Rewrite rule) = rewrite st rule
runStatement st (ProofAssert varProof) = do
    proof <- liftR (toIotaProof st varProof)
    -- (a call of a function in the proof has to meet the function's contract, and gives what it promises)
    st' <- evaluateCalls st [proof]
    if Engine.entails proof (proofContext st')
        then return (addFacts st' [proof])
        else throwV ("Could not prove: " ++ renderVarProof varProof)
runStatement st (AssignProofVar var expr) = assignProofVar st var expr

-- Takes each statement as true: what a function or loop starts out with
assumeStatements :: PState -> [ValidationStatement] -> V PState
assumeStatements = foldM assumeStatement

assumeStatement :: PState -> ValidationStatement -> V PState
-- (a rewrite is only a way to prove something)
assumeStatement st (Rewrite _) = return st
assumeStatement st (ProofAssert varProof) = do
    proof <- liftR (toIotaProof st varProof)
    st' <- evaluateCalls st [proof]
    return (addFacts st' [proof])
assumeStatement st (AssignProofVar var expr) = assignProofVar st var expr

-- A variable of a proof stands for the value of an expression
assignProofVar :: PState -> Variable -> Expression -> V PState
assignProofVar st var expr = do
    (st', term) <- exprTerm st expr
    case term of
        ATerm iota -> return st'{psVars = Map.insert var iota (psVars st')}
        _ -> do
            iota <- fresh
            let defined = addFacts st' [FApp eqProof [ATerm iota, term], FApp eqProof [term, ATerm iota]]
            return defined{psVars = Map.insert var iota (psVars defined)}

-- The term for the value of an expression, with the facts its calls give. A call has its own result iota and has to meet
-- the contract of the function it calls.
exprTerm :: PState -> Expression -> V (PState, IotaProof)
exprTerm st (Val val@(VFunct _ _ _ BuiltinFunct{} _)) = return (st, CTerm val)
exprTerm _ (Val VFunct{}) = throwV "A function is defined by a statement, not written in an expression"
exprTerm st (Val val) = return (st, CTerm val)
exprTerm st (Var var) =
    case lookupName st var of
        Just term -> return (st, term)
        Nothing -> throwV ("Undefined variable: " ++ var ++ " (a function must be defined before the functions that call it)")
exprTerm st (F funct args) = do
    (st1, functTerm) <- exprTerm st funct
    (st2, argTerms) <- foldM (\(s, ts) a -> (\(s', t) -> (s', ts ++ [t])) <$> exprTerm s a) (st1, []) args
    info <- liftR (resolveFunction st2 functTerm)
    result <- fresh
    st3 <- applyCall st2 info argTerms result
    return (st3, ATerm result)

-- The function that a term stands for
resolveFunction :: PState -> IotaProof -> Result FnInfo String
resolveFunction st term =
    case term of
        CTerm (VFunct _ _ _ (BuiltinFunct b) _) -> Ok (builtinInfo b)
        CTerm (VFnRef name) -> byName name
        CTerm _ -> Error "Non-function value called"
        ATerm iota -> case functionFact iota of
            Just value -> resolveFunction st (CTerm value)
            Nothing -> Error ("Function object not validated. Function iota: " ++ show term)
        _ -> Error "Object being called must be a function"
  where
    functionFact iota =
        case [value | FApp eq [ATerm lhs, CTerm value] <- allFacts st, eq == eqProof, lhs == iota, isFunction value] of
            value : _ -> Just value
            [] -> Nothing
    isFunction VFunct{} = True
    isFunction VFnRef{} = True
    isFunction _ = False
    byName name = maybe (Error ("Undefined variable: " ++ name ++ " (a function must be defined before the functions that call it)")) Ok (maybe (wrapperInfo st name) Just (Map.lookup name (psFns st)))

builtinInfo :: BuiltinFunct -> FnInfo
builtinInfo b =
    case builtinFunct b of
        VFunct params requires _ _ exported -> FnInfo params requires exported Nothing (CTerm (builtinFunct b)) True (KBuiltin b) (b == ReadByte)
        _ -> FnInfo [] [] [] Nothing (CTerm (builtinFunct b)) True (KBuiltin b) (b == ReadByte)

-- The builtin function that an operation is
rvalueCall :: M.Rvalue -> Maybe (BuiltinFunct, [M.Operand])
rvalueCall rv =
    case rv of
        M.BinaryOp op a b -> Just (binary op, [a, b])
        M.ListOp op os -> Just (list op, os)
        M.MakeData name fields -> Just (Ctor name (map fst fields), map snd fields)
        M.ReadField o _ field -> Just (Field Nothing field, [o])
        M.IsVariant o name -> Just (Is name, [o])
        M.AsVariant o name -> Just (Cast name, [o])
        M.Use _ -> Nothing
        M.MakeList _ -> Nothing
        M.MakeBox _ -> Nothing
        M.Unbox _ -> Nothing
        M.Unsize _ -> Nothing
  where
    binary op = case op of
        M.Add -> Plus
        M.Sub -> Minus
        M.Mul -> Times
        M.Div -> Div
        M.Mod -> Mod
        M.Compare rel -> Rel rel
    list op = case op of
        M.Length -> Size
        M.First -> First
        M.Last -> Last
        M.Get -> Get
        M.Push -> Push
        M.Pop -> Pop
        M.Set -> Set
        M.NewArray -> NewArray
        M.NewBoxed -> NewBoxedArray
        M.NewEmptyBoxed -> NewEmptyArray
        M.WriteByte -> WriteByte
        M.ReadByte -> ReadByte
        M.ToByte -> ToByte
        M.FromByte -> FromByte

-- A builtin used as a value is a function of the program that applies it, which promises what the builtin does
wrapperInfo :: PState -> Name -> Maybe FnInfo
wrapperInfo st name = do
    fn <- Map.lookup name (M.progFunctions (psProgram st))
    [M.BasicBlock [M.Assign (M.Local 0) rv] M.Return] <- Just (Map.elems (M.fnBlocks fn))
    (builtin, _) <- rvalueCall rv
    let info = builtinInfo builtin
    return info{fnTerm = ATerm (fnIota name)}

-- Calling a function: the arguments have to meet its input contract and the call has to end, and the call then gives
-- the facts the function promises about its result, and the result itself when everything is known.
applyCall :: PState -> FnInfo -> [IotaProof] -> Iota -> V PState
applyCall st info args result = do
    let params = fnParamNames info
    when (length params /= length args) (throwV ("Function expected " ++ show (length params) ++ " arguments, got " ++ show (length args)))
    checkInputs st params args (fnRequires info)
    callTermination st info args
    (st', instantiated) <- instantiateOutputs st params args result (fnExported info)
    -- (a function that reads the input is not a function of its arguments: its result is only what it promises)
    let call = [FApp eqProof [ATerm result, FApp (fnTerm info) args] | not (fnReads info)]
        known = case concreteResult st info args of
            Just value | not (fnReads info) -> [FApp eqProof [ATerm result, CTerm value]]
            _ -> []
    evaluateCalls (addFacts st' (call ++ known ++ instantiated)) instantiated

-- Functions in proofs. `affirm i < size(v);` with a `size` that the program defines calls it: the call has to meet the input contract of
-- the function, exactly as a call in the code does, and the term `size(v)` then has the facts the function promises about its result.
-- A function that may not end promises nothing about a value it does not give, so a proof does not call one.
evaluateCalls :: PState -> [IotaProof] -> V PState
evaluateCalls st0 proofs = go (200 :: Int) st0 (concatMap (callTerms st0) proofs)
  where
    go _ st [] = return st
    go budget st (term : rest)
        | budget <= 0 || evaluated st term = go budget st rest
        | otherwise = case term of
            FApp (ATerm (Iota "readByte")) _ -> throwV "A proof calls readByte, which reads the input: it has no value in a proof"
            FApp (ATerm iota) args | Just (name, info) <- calledFunction st iota -> do
                st' <- evaluateCall st name info args term
                -- (what it promises may call functions too)
                new <- return (concatMap (callTerms st') (newFacts st st'))
                go (budget - 1) st' (rest ++ new)
            _ -> go budget st rest
    newFacts before after = filter (`notElem` psFacts before) (psFacts after)

-- The function a term in a proof is the head of the calls of, if it is one of the program
calledFunction :: PState -> Iota -> Maybe (Name, FnInfo)
calledFunction st (Iota ('$' : name)) = (,) name <$> Map.lookup name (psFns st)
calledFunction _ _ = Nothing

-- The calls of functions of the program in a proof, those inside the arguments of another first
callTerms :: PState -> IotaProof -> [IotaProof]
callTerms st proof = case proof of
    -- (readByte is a name of the standard library, which a program cannot declare again)
    FApp (ATerm (Iota "readByte")) args -> concatMap (callTerms st) args ++ [proof]
    FApp (ATerm iota) args
        | Just _ <- calledFunction st iota -> concatMap (callTerms st) args ++ [proof]
        | otherwise -> concatMap (callTerms st) args
    FApp funct args -> concatMap (callTerms st) (funct : args)
    Forall _ guards body -> concatMap (callTerms st) (guards ++ [body])
    _ -> []

evaluated :: PState -> IotaProof -> Bool
evaluated st term = evaluatedFact term `elem` allFacts st

-- (the fact that says a call was looked at, so that it is only looked at once on a path)
evaluatedFact :: IotaProof -> IotaProof
evaluatedFact term = FApp (ATerm (Iota "$evaluated")) [term]

evaluateCall :: PState -> Name -> FnInfo -> [IotaProof] -> IotaProof -> V PState
evaluateCall st name info args term = do
    let params = fnParamNames info
    when (length params /= length args) (throwV ("Function " ++ name ++ " expected " ++ show (length params) ++ " arguments, got " ++ show (length args)))
    case fnTermination info of
        Just MayDiverge -> throwV ("A proof calls " ++ name ++ ", which is declared ~ and may not end")
        Just (Recursing _) -> throwV ("A proof calls " ++ name ++ " from its own contract or body")
        _ -> return ()
    when (fnReads info) (throwV ("A proof calls " ++ name ++ ", which reads the input: what it gives is not determined by its arguments"))
    checkInputs st params args (fnRequires info)
    (st', instantiated) <- instantiateOutputsWith st params args term (fnExported info)
    return (addFacts st' (evaluatedFact term : instantiated))

-- The contract is checked in a state of its own: the names it uses are the parameters
checkInputs :: PState -> [Variable] -> [IotaProof] -> [ValidationStatement] -> V ()
checkInputs _ _ _ [] = return ()
checkInputs st params args stmts = do
    result <- tryV (checkStatements (calleeView st (zip params args)) stmts)
    case result of
        Error e -> throwV ("Funct input validation failed: " ++ e)
        Ok () -> return ()

calleeView :: PState -> [(Variable, IotaProof)] -> PState
calleeView st bindings = st{psVars = Map.empty, psView = Map.fromList bindings}

-- Whether the function is known to end, if it was called here
callTermination :: PState -> FnInfo -> [IotaProof] -> V ()
callTermination st info args =
    case fnTermination info of
        Just term -> case term of
            MayDiverge -> liftR (noteDivergence st "it calls a function that is declared ~")
            Recursing Nothing -> liftR (noteDivergence st "it calls itself and does not say what shrinks")
            -- Inside the function itself this is not an error, as the function is declared ~ too. From a function defined inside it, it is.
            Recursing (Just MayDiverge) -> liftR (noteDivergence st "it calls a function that is declared ~")
            Recursing (Just clause)
                | Just variant <- variantOf (Just clause) ->
                    case Map.lookup entryVariantName (psVars st) of
                        Just entry ->
                            let smaller = smallerThan "variant of the call" entryVariantName clause variant
                             in variantFailure "Recursive call does not shrink the variant" smaller (checkStatements (calleeView st (zip (fnParamNames info ++ [entryVariantName]) (args ++ [ATerm entry]))) smaller)
                        Nothing -> throwV "A function can only call itself from its own body, not from a function defined inside it, unless both are declared ~"
            _ -> return ()
        Nothing -> return ()

-- Code that may not terminate, in a function that was not declared ~, is an error if it can be reached. The code is also
-- not guaranteed to terminate in the program or a function that is declared ~, but they do not mind.
noteDivergence :: PState -> String -> Result () String
noteDivergence st why
    | psTerminates st && not (unreachable st) = Error ("Not guaranteed to terminate: " ++ why ++ ". Declare the function ~ if that is intended")
    | otherwise = Ok ()

-- Whether the facts known at this point contradict each other, so that nothing here can run
unreachable :: PState -> Bool
unreachable st =
    let context = proofContext st
        impossible = FApp (CTerm (builtinFunct (Rel Lt))) [CTerm (VInt 0), CTerm (VInt 0)]
     in Engine.entails (CTerm (VBool False)) context || Engine.entails impossible context

-- What the function promises, for these arguments and this result. A name the promise defines gets a value of its own.
instantiateOutputs :: PState -> [Variable] -> [IotaProof] -> Iota -> [VariableProof] -> V (PState, [IotaProof])
instantiateOutputs st params args result = instantiateOutputsWith st params args (ATerm result)

-- (the result is a term: a value, or a call of the function that a proof makes)
instantiateOutputsWith :: PState -> [Variable] -> [IotaProof] -> IotaProof -> [VariableProof] -> V (PState, [IotaProof])
instantiateOutputsWith st _ _ _ [] = return (st, [])
instantiateOutputsWith st params args result exported = do
    let defined = filter (\var -> var /= "return" && var `notElem` params && Map.notMember var (psGlobals st)) (nubOrd (concatMap proofVars exported))
    iotas <- freshN (length defined)
    let bound = zip defined iotas
        view = (calleeView st (zip params args ++ [("return", result)])){psVars = Map.fromList bound}
    proofs <- liftR (flatResultMap (toIotaProof view) exported)
    return (st{psVars = Map.union (Map.fromList bound) (psVars st)}, proofs)

-- The value of a term when the facts say what it is
termValue :: PState -> IotaProof -> Maybe Value
termValue _ (CTerm value) = Just value
termValue st term@(ATerm _) = case Engine.constantValues [term] (proofContext st) of
    [Just value] -> Just value
    _ -> Nothing
termValue _ _ = Nothing

-- The result of the call when its arguments are known. A function of the program runs on a budget, so that validating a
-- program does not depend on a long or endless computation; one that is not finished gives no result.
concreteResult :: PState -> FnInfo -> [IotaProof] -> Maybe Value
concreteResult st info args = do
    values <- mapM (termValue st) args
    case fnKind info of
        KBuiltin b -> case evalBuiltinFunct b values of
            Ok value -> Just value
            Error _ -> Nothing
        -- (what a function of the program does is not looked at: a caller knows its contracts and nothing else)
        KUser _ -> Nothing

-- The variant of a loop or function is an integer that has to be at least 0 where it starts, and smaller
-- each time round. Its value at the start is kept in a variable that has a name no program can write, and
-- the statements below check the value later on against it.
--
-- `shrinks e` is resolved by the type checker. An integer variant (Counting) has to be at least 0 and smaller. An enum or
-- struct (Parts) needs no bound and is smaller when it is a part of the earlier value.
variantStatements :: Variable -> Expression -> [ValidationStatement]
variantStatements name variant = [AssignProofVar name variant]

-- The expression of a clause that has a variant
variantOf :: Maybe Termination -> Maybe Expression
variantOf (Just (Counting variant)) = Just variant
variantOf (Just (Parts variant)) = Just variant
variantOf _ = Nothing

-- What a recursive call compares its variant with: the variant's value when the function was called
entryVariantName :: Variable
entryVariantName = "variant at entry"

boundedBelow :: Variable -> Termination -> Expression -> [ValidationStatement]
boundedBelow name (Counting _) variant = variantStatements name variant ++ [ProofAssert (FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm name, CTerm (VInt 0)])]
boundedBelow name _ variant = variantStatements name variant

smallerThan :: Variable -> Variable -> Termination -> Expression -> [ValidationStatement]
smallerThan name earlier (Counting _) variant = variantStatements name variant ++ [ProofAssert (FApp (CTerm (builtinFunct (Rel Lt))) [ATerm name, ATerm earlier])]
smallerThan name earlier _ variant = variantStatements name variant ++ [ProofAssert (FApp (CTerm (builtinFunct Within)) [ATerm name, ATerm earlier])]

-- Says which variant it was that could not be shown to be fine
variantFailure :: String -> [ValidationStatement] -> V a -> V a
variantFailure what stmts action = do
    result <- tryV action
    case result of
        Ok a -> return a
        Error e -> case stmts of
            AssignProofVar _ variant : _ -> throwV (what ++ ": " ++ renderVarProof (exprToProof variant))
            _ -> throwV (what ++ ": " ++ e)

prefixError :: String -> V a -> V a
prefixError prefix action = do
    result <- tryV action
    case result of
        Ok a -> return a
        Error e -> throwV (prefix ++ e)

maxJoinCandidates :: Int
maxJoinCandidates = 40

-- Rewrites

rewrite :: PState -> RwRule -> V PState
rewrite st (Refl varProof) = do
    _ <- liftR (toIotaProof st varProof)
    engineRewrite st Engine.EngineRefl
rewrite st (Eval var) =
    case lookupName st var of
        Just (ATerm iota) -> engineRewrite st (Engine.EngineEval iota)
        _ -> throwV ("(Eval) Undefined variable: " ++ var)
rewrite st EvalAll = engineRewrite st Engine.EngineEvalAll
rewrite st (CheckGtZero varProof) = do
    proof <- liftR (toIotaProof st varProof)
    engineRewrite st (Engine.EngineCheckGtZero proof)
rewrite st (CheckRel varProof) = do
    proof <- liftR (toIotaProof st varProof)
    engineRewrite st (Engine.EngineCheckRel proof)
rewrite st (UserRewrite name args) = rewriteUserRule st name args

engineRewrite :: PState -> Engine.EngineRewriteRule -> V PState
engineRewrite st rule =
    let oldContext = proofContext st
     in case Engine.applyRewrite evalBuiltinFunct rule oldContext of
            Ok newContext -> return (addFacts st (Engine.proofContextDelta oldContext newContext))
            Error e -> throwV e

rewriteUserRule :: PState -> Variable -> [VariableProof] -> V PState
rewriteUserRule st name actualArgs =
    case Map.lookup name (psRules st) of
        Nothing -> throwV ("Unknown rewrite rule: " ++ name)
        Just (AxiomRule formals inputs outputs) -> applyAxiom st name formals inputs outputs actualArgs
        Just (ProofRule formals inputs exported) -> applyProofRule st name formals inputs exported actualArgs

applyAxiom :: PState -> Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> [VariableProof] -> V PState
applyAxiom st name formals inputs outputs actualArgs
    | length formals /= length actualArgs =
        throwV ("Rewrite rule " ++ name ++ " expected " ++ show (length formals) ++ " arguments, got " ++ show (length actualArgs))
    | any proofHasForall actualArgs = throwV ("Rewrite rule " ++ name ++ " cannot take a forall as an argument")
    | otherwise = do
        let bindings = Map.fromList (zip formals actualArgs)
        checked <- tryV (checkStatements st (map (substituteValidationStatement bindings) inputs))
        case checked of
            Error e -> throwV ("Rewrite rule " ++ name ++ " input validation failed: " ++ e)
            Ok () -> do
                assumed <- tryV (assumeStatements st (map (substituteValidationStatement bindings) outputs))
                case assumed of
                    Error e -> throwV ("Rewrite rule " ++ name ++ " output instantiation failed: " ++ e)
                    Ok st' -> return st'

applyProofRule :: PState -> Variable -> [Variable] -> [ValidationStatement] -> [VariableProof] -> [VariableProof] -> V PState
applyProofRule st name formals inputs exported actualArgs
    | length formals /= length actualArgs =
        throwV ("Rewrite rule " ++ name ++ " expected " ++ show (length formals) ++ " arguments, got " ++ show (length actualArgs))
    | any proofHasForall actualArgs = throwV ("Rewrite rule " ++ name ++ " cannot take a forall as an argument")
    | otherwise = do
        let bindings = Map.fromList (zip formals actualArgs)
        checked <- tryV (checkStatements st (map (substituteValidationStatement bindings) inputs))
        case checked of
            Error e -> throwV ("Rewrite rule " ++ name ++ " input validation failed: " ++ e)
            Ok () -> case flatResultMap (toIotaProof st . substituteVariableProof bindings) exported of
                Error e -> throwV ("Rewrite rule " ++ name ++ " output instantiation failed: " ++ e)
                Ok proofs -> return (addFacts st proofs)

substituteValidationStatement :: Map Variable VariableProof -> ValidationStatement -> ValidationStatement
substituteValidationStatement bindings (Rewrite rule) = Rewrite (substituteRwRule bindings rule)
substituteValidationStatement bindings (ProofAssert varProof) = ProofAssert (substituteVariableProof bindings varProof)
substituteValidationStatement bindings (AssignProofVar var expr) = AssignProofVar var (substituteExpression bindings expr)

substituteRwRule :: Map Variable VariableProof -> RwRule -> RwRule
substituteRwRule bindings (Refl varProof) = Refl (substituteVariableProof bindings varProof)
substituteRwRule _ (Eval var) = Eval var
substituteRwRule _ EvalAll = EvalAll
substituteRwRule bindings (CheckGtZero varProof) = CheckGtZero (substituteVariableProof bindings varProof)
substituteRwRule bindings (CheckRel varProof) = CheckRel (substituteVariableProof bindings varProof)
substituteRwRule bindings (UserRewrite name args) = UserRewrite name (map (substituteVariableProof bindings) args)

substituteVariableProof :: Map Variable VariableProof -> VariableProof -> VariableProof
substituteVariableProof bindings (ATerm var) = Map.findWithDefault (ATerm var) var bindings
substituteVariableProof _ cterm@CTerm{} = cterm
substituteVariableProof _ bvar@BVar{} = bvar
substituteVariableProof bindings (Forall index guards body) =
    Forall index (map (substituteVariableProof bindings) guards) (substituteVariableProof bindings body)
substituteVariableProof bindings (FApp funct args) =
    FApp (substituteVariableProof bindings funct) (map (substituteVariableProof bindings) args)

substituteExpression :: Map Variable VariableProof -> Expression -> Expression
substituteExpression bindings (Var var) =
    case Map.lookup var bindings of
        Just replacement -> proofToExpression replacement
        _ -> Var var
substituteExpression _ val@Val{} = val
substituteExpression bindings (F funct args) =
    F (substituteExpression bindings funct) (map (substituteExpression bindings) args)

proofToExpression :: VariableProof -> Expression
proofToExpression (ATerm var) = Var var
-- A forall cannot be an expression: applyAxiom and applyProofRule reject forall arguments
proofToExpression (BVar index) = Var index
proofToExpression Forall{} = error "proofToExpression: forall is not an expression"
proofToExpression (CTerm val) = Val val
proofToExpression (FApp funct args) = F (proofToExpression funct) (map proofToExpression args)

-- Rules

defineAxiom :: PState -> Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> V PState
defineAxiom st name args inputs outputs = insertRule st name (AxiomRule args inputs outputs)

insertRule :: PState -> Variable -> UserRule -> V PState
insertRule st name rule
    | Map.member name (psRules st) = throwV ("Duplicate rule definition: " ++ name)
    | otherwise = return st{psRules = Map.insert name rule (psRules st)}

-- A proof is checked once, for any arguments that meet its input contract, and then gives what it exports
defineProofRule :: PState -> Variable -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> [ValidationStatement] -> V PState
defineProofRule st name args inputs outputs body = do
    let inner = bodyState st
    iotas <- freshN (length args)
    let bindings = zip args iotas
        start = (calleeView inner [(a, ATerm i) | (a, i) <- bindings]){psInBody = True}
    assumed <- assumeStatements start inputs
    done <- runStatements assumed body
    exported <- exportOutputs done bindings inputs outputs
    insertRule st name (ProofRule args inputs exported)

-- What a function or rule promises, as facts over the names it gives its parameters and result: the outputs are checked
-- once more, and then the facts about those values are what is left.
exportOutputs :: PState -> [(Variable, Iota)] -> [ValidationStatement] -> [ValidationStatement] -> V [VariableProof]
exportOutputs st bindings inputs outputs = do
    let named = st{psView = Map.fromList [(name, ATerm iota) | (name, iota) <- bindings]}
    checked <- if null outputs then return named else runStatements named outputs
    exportFacts checked bindings inputs outputs

-- What a function promises is what its contracts say, and nothing the body happens to establish: the contracts are
-- assumed in a state that knows nothing else, and the facts about the parameters, the result and the names the contracts
-- define are what callers get. A caller therefore depends on the contracts alone, and the body can change without
-- changing which callers are valid.
exportContract :: PState -> [IotaProof] -> [(Variable, Iota)] -> [ValidationStatement] -> [ValidationStatement] -> V [VariableProof]
exportContract st known bindings inputs outputs = do
    -- (what the types of the values say, such as the invariant of a struct, holds for any caller's values: a contract may speak of it)
    let named = addFacts ((refreshCache st{psFacts = [], psVars = Map.empty}){psView = Map.fromList [(name, ATerm iota) | (name, iota) <- bindings]}) known
    contract <- assumeStatements named (inputs ++ outputs)
    exportFacts contract bindings inputs outputs

exportFacts :: PState -> [(Variable, Iota)] -> [ValidationStatement] -> [ValidationStatement] -> V [VariableProof]
exportFacts checked bindings inputs outputs = do
    let allowed = nubOrd (map fst bindings ++ concatMap valStmtDefinedVars inputs ++ concatMap valStmtDefinedVars outputs)
        nameIotas = [(name, iota) | name <- allowed, Just (ATerm iota) <- [lookupName checked name]]
        -- (the functions of the program are the same in every state)
        functions = [(source, iota) | (source, iota@(Iota ('$' : fnName))) <- Map.toList (psGlobals checked), Just info <- [Map.lookup fnName (psFns checked)], fnGlobal info]
        byIota = namedIotaMap (reverse nameIotas ++ functions)
        -- (names that are the same value are said to be equal, since a fact is said once about one of them)
        aliases = [FApp eqVarProof [ATerm canonical, ATerm name] | (name, iota) <- nameIotas, Just canonical <- [lookup iota [(i, n) | (n, i) <- nameIotas]], canonical /= name]
        -- (what holds everywhere is not part of a promise: the function iotas are named for the calls in the facts, not for these)
        facts = filter (proofOnlyOfNamedIotasOrConst byIota) (filter (`notElem` psGlobalFacts checked) (allFacts checked))
    return (nubOrd (mapMaybe (iotaProofToVarProof byIota) facts ++ aliases))

-- Invariants of structs

-- What every value of a struct meets, if it says: the struct is the one the name is of, or an instance of it
invariantOf :: PState -> Name -> Maybe (Name, [ValidationStatement])
invariantOf st name =
    let base = maybe name fst (instanceOf name)
     in (,) base <$> Map.lookup base (M.progInvariants (psProgram st))

-- The names of the fields of a struct
fieldNames :: PState -> Name -> [Variable]
fieldNames st base =
    case (Map.lookup base (M.progGenerics (psProgram st)), Map.lookup base (M.progTypes (psProgram st))) of
        (Just (_, fields), _) -> map fst fields
        (_, Just (M.StructDecl fields)) -> map fst fields
        _ -> []

-- A value that is made has to meet the invariant of its struct, with the names of the fields standing for what it is made of
checkInvariant :: PState -> Name -> [(Variable, IotaProof)] -> V ()
checkInvariant st name fields =
    case invariantOf st name of
        Nothing -> return ()
        Just (base, invariant) -> do
            result <- tryV (checkStatements (calleeView st fields) invariant)
            case result of
                Error e -> throwV ("A " ++ base ++ " is made that does not meet its invariant: " ++ e)
                Ok () -> return ()

-- What the invariant says of a value of the struct, as facts about the value: the names of the fields stand for the fields of it
invariantFacts :: PState -> Name -> IotaProof -> [IotaProof]
invariantFacts st name value =
    case invariantOf st name of
        Nothing -> []
        Just (base, invariant) ->
            let view = calleeView st [(f, FApp (CTerm (builtinFunct (Field Nothing f))) [value]) | f <- fieldNames st base]
             in [fact | ProofAssert proof <- invariant, Ok fact <- [toIotaProof view proof]]
