module Proof where

import Data.Map (
    Map,
    empty,
    fromList,
    insert,
    toList,
 )

import Data.Maybe (mapMaybe)

import ProofHelpers
import StdLib
import TersusTypes
import Utils

-- Given an iota proof and a list of proofs as context,
-- return a list of new proofs
evalIotaProof :: IotaProof -> [IotaProof] -> (Map Variable Iota, [IotaProof]) -> [IotaProof]
evalIotaProof
    ( FApp
            eqFunct
            [ ATerm iota
                , FApp (CTerm (VFunct _ _ (BuiltinFunct funct) _)) args
                ]
        )
    proofs
    ctx | eqFunct == eqProof =
        -- TODO: Make recursive
        case flatMaybeMap maybeATermProofToIota args of
            Just iotas -> case iotasToValues iotas proofs of
                -- TODO: Produce FApp with CTerm
                Just values ->
                    let (iotaCtx, proofCtx) = ctx
                     in [FApp eqFunct [ATerm iota, CTerm $ evalFunct (builtinFunct funct) (iotaMapToConcreteMap iotaCtx proofCtx) values]]
                _ -> []
            _ -> []
evalIotaProof _ _ _ = []

evalIota :: Iota -> [IotaProof] -> (Map Variable Iota, [IotaProof]) -> [IotaProof]
evalIota iota proofs ctx =
    concatMap (\proof -> evalIotaProofIfForIota iota proof proofs ctx) proofs

evalIotaProofIfForIota :: Iota -> IotaProof -> [IotaProof] -> (Map Variable Iota, [IotaProof]) -> [IotaProof]
evalIotaProofIfForIota iota proof proofs ctx =
    case proof of
        -- TODO: Support other functions
        (FApp funct [ATerm fiota, FApp _ _])
            | funct == eqProof ->
                if fiota == iota
                    then evalIotaProof proof proofs ctx
                    else []
        _ -> []

-- Public fns
evaluate :: [Statement] -> State
evaluate [] = initState
evaluate l = evalBlock $ initStateWStatements l

validate :: [Statement] -> Result VState String
validate [] = Ok $ VState emptyVScopeState empty [] []
validate l = case valBlock $ initVStateWStatements l of
    Ok (VState vScopeState iotaCtx proofCtx remainingIotas) ->
        Ok $ VState vScopeState iotaCtx proofCtx [head remainingIotas]
    Error e -> Error e

-- Private fns
evalBlock :: State -> State
evalBlock state = case state of
    State (ScopeState _ (Continuations []) _) _ -> state
    State (ScopeState _ (Continuations (_ : _)) _) _ ->
        let nState = evalNextStatement state
         in evalBlock nState

evalReturningBlock :: State -> (State, Maybe Value)
evalReturningBlock state =
    let rState = evalBlock state
     in (rState, getReturn rState)

valBlock :: VState -> Result VState String
valBlock state = case state of
    VState (VScopeState _ _ (Continuations []) _) _ _ _ -> Ok state
    VState (VScopeState _ _ (Continuations (_ : _)) _) _ _ _ ->
        case valNextStatement state of
            Ok state' -> valBlock state'
            e -> e

valReturningBlock :: VState -> Result (VState, Maybe Iota) String
valReturningBlock state =
    let result = valBlock state
     in case result of
            Ok rstate -> Ok (rstate, vGetReturn rstate)
            Error e -> Error e

evalNextStatement :: State -> State
evalNextStatement state = case state of
    State (ScopeState _ (Continuations (Assign var expr : _)) _) _ ->
        let (mval, rState) = evalExpression (advanceStatement state) expr
         in case mval of
                Just val -> insertVar rState var val
                -- TODO: Is this an error case?
                Nothing -> rState
    State (ScopeState _ (Continuations (Return expr : _)) _) _ ->
        let (mval, rState) = evalExpression (advanceStatement state) expr
         in -- Break out of the current block and return the value
            let prState = topLevelScope rState
             in case mval of
                    Just val -> setReturn prState val
                    -- TODO: Allow this for functions returning nothing
                    Nothing -> error "Return expression must return a value"
    State (ScopeState _ (Continuations (ValidationStatement{} : _)) _) _ -> advanceStatement state
    State (ScopeState _ (Continuations (Block statements : _)) _) _ ->
        let State scope ctxVals = state
         in evalBlock $
                State
                    (ScopeState empty (Continuations (statements ++ [EndBlock])) (Just $ scopeAdvanceStatement scope))
                    ctxVals
    -- TODO: Could we just match on Continuations [] insead of inserting EndBlock?
    State (ScopeState _ (Continuations (EndBlock : _)) pScope) ctxVals ->
        -- Any vars declared in the block are not exported,
        -- but any vars updated in the parent scope must be exported
        case pScope of
            Just rpScope -> State rpScope ctxVals
            _ -> error "EndBlock must have a parent scope"

valNextStatement :: VState -> Result VState String
valNextStatement state =
    let VState scope iotaCtx proofCtx iotaseq = state
     in let VScopeState _ _ (Continuations stmts) pscope = scope
         in case stmts of
                (Assign var expr : _) ->
                    let (niota, state') = doTrace "assign" (popIotaFromSeq (vAdvanceStatement state))
                     in case valExpression state' niota expr of
                            -- TODO: Partition nproofs into 1) those that only use niota and iotas
                            -- from scopes higher than where niota is declared and 2) the inverse
                            Ok nproofs -> Ok $ vInsertVar state' var niota nproofs
                            Error e -> Error e
                (Return expr : _) ->
                    let (VState (VScopeState _ proofs c _) _ _ _) = state
                     in let (niota, state') = doTrace ("return: " ++ show c) (popIotaFromSeq (vAdvanceStatement state))
                         in case valExpression state' niota expr of
                                Ok nproofs ->
                                    -- TODO: Break out of the current block and return the value
                                    -- TODO: Shoud vSetReturn also pass up the nproofs?
                                    let refledNProofs = reflProofsByProofs nproofs proofs
                                     in let state'' = vTopLevelScope state'
                                         in Ok $ vSetReturn state'' niota (filter (proofOnlyOfIotasOrConst [niota]) (nproofs ++ refledNProofs))
                                Error e -> Error e
                (ValidationStatement valStmt : _) -> valValidationStatement state valStmt
                (Block bstmts : _) ->
                    valBlock $ VState (VScopeState empty [] (Continuations $ bstmts ++ [EndBlock]) (Just $ vScopeAdvanceStatement scope)) iotaCtx proofCtx iotaseq
                (EndBlock : _) -> case pscope of
                    Just ps -> Ok $ VState ps iotaCtx proofCtx iotaseq
                    _ -> error "EndBlock must have a parent state"

-- Rewrite proofs using eq relation
-- proofs to change -> eq relations -> updated proofs
reflProofsByProofs :: [IotaProof] -> [IotaProof] -> [IotaProof]
reflProofsByProofs lproofs = concatMap (reflProofsByProof lproofs)

valValidationStatement :: VState -> ValidationStatement -> Result VState String
valValidationStatement state (Rewrite rwrule) = doTrace "rewrite" (valRewrite (vAdvanceStatement (doTrace "starting rewrite" state)) rwrule)
valValidationStatement state (ProofAssert varproof) =
    let (VState (VScopeState _ proofs _ _) _ _ _) = state
     in let state' = doTrace "proofAssert" (vAdvanceStatement state)
         in let iotaProof = varProofToIotaProof varproof state'
             in if iotaProof `elem` proofs
                    then Ok state'
                    else doTrace2 ("Had proofs: " ++ show proofs) (Error $ "Assertion failed: " ++ show varproof)
valValidationStatement state (AssignProofVar var expr) =
    let VState scope _ _ _ = state
     in let VScopeState _ _ c _ = scope
         in let (niota, state') = doTrace ("assignProofVar: " ++ show c) (popIotaFromSeq (vAdvanceStatement state))
             in case doTrace "apv1" (valExpression state' niota expr) of
                    -- TODO: Convert expression to iota proof p1, and add additional proof (niota == p1)
                    Ok nproofs ->
                        -- TODO: Should we be doing this in the ordinary valExpression?
                        let nonEvalProof =
                                let exprAsProof = varProofToIotaProof (exprToProof expr) state'
                                 in FApp eqProof [ATerm niota, exprAsProof]
                         in doTrace2 ("New assign proof var proofs: " ++ show (nonEvalProof : nproofs)) (Ok $ doTrace "apv2" (vInsertVar state' var niota (nonEvalProof : nproofs)))
                    Error e -> Error e

valRewrite :: VState -> RwRule -> Result VState String
valRewrite state (Refl varProof) =
    let (VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx iotaseq) = state
     in let iotaProof = varProofToIotaProof varProof state
         in let newProofs = reflProofsByProofs proofs proofs -- TODO: limit to proofs with iotaProof
             in Ok $ VState (VScopeState iotas (proofs ++ newProofs) c pscope) iotaCtx proofCtx iotaseq
valRewrite state (Eval var) =
    let (VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx iotaseq) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "Undefined variable: " ++ var
                Just iota ->
                    Ok $
                        VState
                            (VScopeState iotas (evalIota iota proofs (iotaCtx, proofCtx) ++ proofs) c pscope)
                            iotaCtx
                            proofCtx
                            iotaseq
valRewrite (VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx iotaseq) EvalAll =
    let newProofs = concatMap (\p -> evalIotaProof p proofs (iotaCtx, proofCtx)) proofs
     in Ok $ VState (VScopeState iotas (proofs ++ newProofs) c pscope) iotaCtx proofCtx iotaseq
valRewrite state (EqToLtPlus1 var) =
    let (VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx (niota : c1iota : iotaseq)) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "Undefined variable: " ++ var
                Just iota ->
                    let withNewProofs =
                            proofs
                                ++ [ FApp (CTerm (builtinFunct (Rel Lt))) [ATerm iota, ATerm niota]
                                   , FApp eqProof [ATerm niota, FApp (CTerm (builtinFunct Plus)) [ATerm iota, ATerm c1iota]]
                                   , -- TODO: Squish this into above
                                     FApp eqProof [ATerm c1iota, CTerm $ VInt 1]
                                   ]
                     in let withEvaledProofs = withNewProofs ++ evalIota niota withNewProofs (iotaCtx, proofCtx)
                         in let withRefledNewProofs =
                                    withEvaledProofs
                                        ++ reflProofsByProofs withEvaledProofs withEvaledProofs -- TODO: Maybe limit to new proofs
                             in Ok $ VState (VScopeState iotas withRefledNewProofs c pscope) iotaCtx proofCtx iotaseq
-- TODO: Make this EqToGtTarget with two arguments, the var and the target number
valRewrite state (EqToGtZero var) =
    case vLookupVar state var of
        Nothing -> Error $ "Undefined variable: " ++ var
        Just iota -> case iotaToValue iota (vGetProofs state) of
            Nothing -> Error $ "Var lacks concrete definition: " ++ var
            Just (VInt num) ->
                if num > 0
                    then
                        let gtZeroProof = FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iota, CTerm (VInt 0)]
                         in let refledNewProof = reflProofsByProofs [gtZeroProof] (vGetProofs state)
                             in Ok $ vInsertProofs state (gtZeroProof : refledNewProof)
                    else Error $ "Var is not greater than 0: " ++ var
            Just _ -> Error $ "Var is not an int: " ++ var

evalExpressionList :: State -> [Expression] -> (State, [Value])
evalExpressionList state [] = (state, [])
evalExpressionList sstate (expr : exprs) =
    let (mval, estate) = evalExpression sstate expr
     in case mval of
            Just val ->
                let (state, vals) = evalExpressionList estate exprs
                 in (state, val : vals)
            Nothing -> error "Expression must return a value to be passed to a function"

evalExpression :: State -> Expression -> (Maybe Value, State)
evalExpression state (Val val) = (Just val, state)
evalExpression state (Var var) =
    let mval = lookupVar state var
     in case mval of
            Just _ -> (mval, state)
            Nothing -> error ("Undefined variable: " ++ var)
evalExpression sstate (F fnExpr argExprs) =
    let (State scope valCtx, fval : argVals) = evalExpressionList sstate (fnExpr : argExprs)
     in (Just $ evalFunct fval valCtx argVals, State scope valCtx)

-- State -> iota of result -> expression -> Result [proofs about result iota] String
valExpression :: VState -> Iota -> Expression -> Result [IotaProof] String -- produces only the new proofs
valExpression _ iota (Val val) = Ok [FApp eqProof [ATerm iota, CTerm val]]
-- foldr (\iota _ -> [C iota Eq val]) [] miota
valExpression state iota (Var var) =
    let omiota = vLookupVar state var
     in case omiota of
            Nothing -> Error $ "Undefined variable: " ++ var
            Just oiota -> Ok [FApp eqProof [ATerm iota, ATerm oiota]]
valExpression (VState scope iotaCtx proofCtx iotaseq) iota (F fnexpr argexprs) =
    let VScopeState _ proofs _ _ = scope
     in let functResults = valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq) fnexpr argexprs iota
         in case functResults of
                -- TODO: Return updated iotaseq
                Ok (flatfinputproofs, functProofs, niotas, iotaseq') ->
                    Ok
                        -- TODO: Add back
                        -- (
                        -- reflProofsByProofs
                        -- [ FApp
                        --     eqProof
                        --     [ ATerm iota
                        --     , FApp funct (map ATerm niotas)
                        --     ]
                        -- ]
                        -- flatfinputproofs
                        -- ++
                        functProofs
                -- )
                -- TODO: If cannot get concrete value use proof IO
                Error e -> Error e
valExpression _ _ e = Error $ "Unsupported expression: " ++ show e

-- Given expression evaluating to a function object, expressions evaluating to
-- the function's arguments, and the iota corresponding to the function return value,
-- validate and return:
-- 1) proofs of input expressions 2) proofs of the evaluated fn result 3) the new iotas used
-- state -> fnexpr -> argexprs -> (argProofs, functresultproofs, new iotas)
valFunctExprHelper :: VState -> Expression -> [Expression] -> Iota -> Result ([IotaProof], [IotaProof], [Iota], [Iota]) String
valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq) fnexpr exprargs riota =
    let VScopeState _ proofs _ _ = scope
     in -- Get proofs from the function and arg expressions
        let exprsToVal = fnexpr : exprargs
         in let (niotas, iotaseq') = splitAt (length exprsToVal) iotaseq
             in let (fInputProofResults, _) =
                        zipMap
                            exprsToVal
                            niotas
                            -- TODO: Update iotaseq with any used iotas
                            (flip (valExpression $ VState scope iotaCtx proofCtx iotaseq')) -- proofs of input expression in terms of new iotas
                 in case flatResultMap id fInputProofResults of
                        Error e -> Error e
                        Ok finputproofs ->
                            -- Simplify proofs of function and arg expressions
                            let flatfinputproofs = concat finputproofs
                             in let refloncefiproofs =
                                        reflProofsByProofs flatfinputproofs (proofs ++ proofCtx)
                                 in -- Extract out concrete values from the produced proofs
                                    let ps = refloncefiproofs ++ flatfinputproofs
                                     in -- Iota of the function object is first of the new iotas, rest are iotas of the args
                                        let (fniota : argiotas) = niotas
                                         in -- Finally validate the function with the processed proofs
                                            -- TODO: Update iotaseq with iotas consumed in valFunct
                                            case valFunct (VState (VScopeState empty [] (Continuations []) (Just scope)) iotaCtx proofCtx iotaseq') fniota argiotas ps riota of
                                                Ok functProofs -> Ok (flatfinputproofs, functProofs, niotas, iotaseq')
                                                Error e -> Error e

evalFunct :: Value -> Map Variable Value -> [Value] -> Value
evalFunct (VFunct _ _ (BuiltinFunct builtin) _) valCtx args =
    evalBuiltinFunct builtin args
evalFunct (VFunct vars _ (NativeFunct block) _) valCtx args =
    let (argVals, _) = zipMap vars args (,)
     in -- Give args the function parameter names
        let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
         in let scope = ScopeState varMap (Continuations block) (Just emptyScopeState)
             in case evalReturningBlock (State scope valCtx) of
                    (_, Just val) -> val
                    _ -> error "Function did not return a value"
evalFunct _ _ _ = error "Object being called must be a function"

evalBuiltinFunct :: BuiltinFunct -> [Value] -> Value
evalBuiltinFunct Size [VIntList l] = VInt (fromIntegral (length l))
evalBuiltinFunct Size _ = error "Size only valid for IntList"
evalBuiltinFunct First [VIntList l] = VInt (head l)
evalBuiltinFunct First _ = error "First only valid for IntList"
evalBuiltinFunct Last [VIntList l] = VInt (last l)
evalBuiltinFunct Last _ = error "Last only valid for IntList"
evalBuiltinFunct Minus [VInt v1, VInt v2] = VInt (v1 - v2)
evalBuiltinFunct Minus _ = error "Plus only valid for two ints"
evalBuiltinFunct Plus [VInt v1, VInt v2] = VInt (v1 + v2)
evalBuiltinFunct Plus _ = error "Plus only valid for two ints"
evalBuiltinFunct (Rel Eq) [VInt v1, VInt v2] = VBool (v1 == v2)
evalBuiltinFunct (Rel Eq) _ = error "Eq only valid for two ints"
evalBuiltinFunct (Rel Lt) [VInt v1, VInt v2] = VBool (v1 < v2)
evalBuiltinFunct (Rel Lt) _ = error "Lt only valid for two ints"
evalBuiltinFunct (Rel Gt) [VInt v1, VInt v2] = VBool (v1 > v2)
evalBuiltinFunct (Rel Gt) _ = error "Rt only valid for two ints"
evalBuiltinFunct (Rel LtEq) [VInt v1, VInt v2] = VBool (v1 <= v2)
evalBuiltinFunct (Rel LtEq) _ = error "LtEq only valid for two ints"
evalBuiltinFunct (Rel GtEq) [VInt v1, VInt v2] = VBool (v1 >= v2)
evalBuiltinFunct (Rel GtEq) _ = error "GtEq only valid for two ints"

iotaMapToConcreteMap :: (Ord a) => Map a Iota -> [IotaProof] -> Map a Value
iotaMapToConcreteMap imap proofs =
    Data.Map.fromList $
        mapMaybe
            ( \(k, i) -> case iotaToValue i proofs of
                Just val -> Just (k, val)
                Nothing -> Nothing
            )
            (Data.Map.toList imap)

concreteValOfIotaMaybe :: Iota -> [IotaProof] -> Maybe Value
concreteValOfIotaMaybe _ [] = Nothing
concreteValOfIotaMaybe iota (proof : ptail) = case concreteValOfIotaFromProofMaybe iota proof of
    Just val -> Just val
    Nothing -> concreteValOfIotaMaybe iota ptail

concreteValOfIotaFromProofMaybe :: Iota -> IotaProof -> Maybe Value
concreteValOfIotaFromProofMaybe iota proof = case proof of
    FApp funct [ATerm piota, CTerm val] | funct == eqProof && piota == iota -> Just val
    _ -> Nothing

-- Takes: Funct iota, funct input iotas, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunct :: VState -> Iota -> [Iota] -> [IotaProof] -> Iota -> Result [IotaProof] String
valFunct state fniota iiotas iproofs retiota =
    let mFnIota = findIotaEqToFn ["list"] iproofs
     in -- Get the concrete function object
        -- TODO: Support function proof evaluation with less than the full concrete function
        case concreteValOfIotaMaybe fniota iproofs of
            Just fnVal -> case fnVal of
                VFunct varArgs inputValStmts _ _ ->
                    -- Validate the inputs are valid wrt the function signature
                    case valFunctInput state varArgs iiotas iproofs inputValStmts of
                        Error e -> Error $ "Funct input validation failed: " ++ e
                        Ok state' ->
                            let argvalsMaybe = flatMaybeMap (`concreteValOfIotaMaybe` iproofs) iiotas
                             in case argvalsMaybe of
                                    Just argVals ->
                                        -- Concrete values of function args
                                        let (VState _ iotaCtx proofCtx _) = state' -- Evaluate the function using the concrete values of the function and args
                                         in let functResult = evalFunct fnVal (iotaMapToConcreteMap iotaCtx proofCtx) argVals
                                             in Ok [FApp eqProof [ATerm retiota, CTerm functResult]]
                                    Nothing ->
                                        Error
                                            ( "Funct agrs not validated. Input iotas: "
                                                ++ show iiotas
                                                ++ ". Input Proofs: "
                                                ++ show iproofs
                                            )
                _ -> Error "Non-function value called"
            Nothing ->
                Error $
                    "Function object not validated. Function iota: "
                        ++ show fniota
                        ++ ". Input proofs: "
                        ++ show iproofs

valFunctInput :: VState -> [Variable] -> [Iota] -> [IotaProof] -> [ValidationStatement] -> Result VState String
valFunctInput state _ _ _ [] = Ok state
valFunctInput
    (VState scope iotaCtx proofCtx iotaseq)
    varArgs
    argIotas
    argProofs
    valStmts =
        let (argIotasMap, _) = doTrace2 ("Arg iotas: " ++ show argIotas) (doTrace2 ("Arg proofs: " ++ show argProofs) (zipMap varArgs argIotas (,)))
         in let stmts = map ValidationStatement valStmts
             in case valBlock $ VState (VScopeState (Data.Map.fromList argIotasMap) argProofs (Continuations $ stmts ++ [EndBlock]) (Just scope)) iotaCtx proofCtx iotaseq of
                    -- TODO: Export validation vars from this into the function body?
                    Ok (VState _ _ _ iotaseq') -> Ok $ VState scope iotaCtx proofCtx iotaseq'
                    Error e -> Error e

iotaLhsEq :: Iota -> [IotaProof] -> [IotaProof]
iotaLhsEq _ [] = []
iotaLhsEq iota (proof : tail) =
    case proof of
        FApp funct [ATerm liota, rhsProof]
            | funct == eqProof && liota == iota ->
                rhsProof : iotaLhsEq iota tail
        _ -> iotaLhsEq iota tail

findIotaEqToFn :: [Variable] -> [IotaProof] -> Maybe Iota
findIotaEqToFn _ [] = Nothing
findIotaEqToFn varList (proof : tail) =
    case proof of
        FApp funct [ATerm iota, CTerm (VFunct argList _ _ _)]
            | funct == eqProof && argList == varList ->
                Just iota
        _ -> findIotaEqToFn varList tail
