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
validate [] = Ok $ VState (emptyVScopeState, empty, [], [])
validate l = case valBlock $ initVStateWStatements l of
    Ok (VState (vScopeState, iotaCtx, proofCtx, remainingIotas)) ->
        Ok $ VState (vScopeState, iotaCtx, proofCtx, [head remainingIotas])
    Error e -> Error e

-- Private fns
evalBlock :: State -> State
evalBlock state = case state of
    State (ScopeState (_, Continuations [], _), _) -> state
    State (ScopeState (_, Continuations (_ : _), _), _) ->
        let nState = evalNextStatement state
         in evalBlock nState

evalReturningBlock :: State -> (State, Maybe Value)
evalReturningBlock state =
    let rState = evalBlock state
     in (rState, getReturn rState)

valBlock :: VState -> Result VState String
valBlock state = case state of
    VState (VScopeState (_, _, Continuations [], _), _, _, _) -> Ok state
    VState (VScopeState (_, _, Continuations (_ : _), _), _, _, _) ->
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
    State (ScopeState (_, Continuations (Assign var expr : _), _), _) ->
        let (mval, rState) = evalExpression (advanceStatement state) expr
         in case mval of
                Just val -> insertVar rState var val
                -- TODO: Is this an error case?
                Nothing -> rState
    State (ScopeState (_, Continuations (Return expr : _), _), _) ->
        let (mval, rState) = evalExpression (advanceStatement state) expr
         in -- Break out of the current block and return the value
            let prState = topLevelScope rState
             in case mval of
                    Just val -> setReturn prState val
                    -- TODO: Allow this for functions returning nothing
                    Nothing -> error "Return expression must return a value"
    State (ScopeState (_, Continuations (ValidationStatement{} : _), _), _) -> advanceStatement state
    State (ScopeState (_, Continuations (Block statements : _), _), _) ->
        let State (scope, ctxVals) = state
         in evalBlock (State (ScopeState (empty, Continuations (statements ++ [EndBlock]), Just (scopeAdvanceStatement scope)), ctxVals))
    -- TODO: Could we just match on Continuations [] insead of inserting EndBlock?
    State (ScopeState (_, Continuations (EndBlock : _), pScope), ctxVals) ->
        -- Any vars declared in the block are not exported,
        -- but any vars updated in the parent scope must be exported
        case pScope of
            Just rpScope -> State (rpScope, ctxVals)
            _ -> error "EndBlock must have a parent scope"

valNextStatement :: VState -> Result VState String
valNextStatement state =
    let VState (scope, iotaCtx, proofCtx, iotaseq) = state
     in let VScopeState (_, _, Continuations stmts, pscope) = scope
         in case stmts of
                (Assign var expr : _) ->
                    let (niota, state') = popIotaFromSeq (vAdvanceStatement state)
                     in case valExpression state' niota expr of
                            -- TODO: Partition nproofs into 1) those that only use niota and iotas
                            -- from scopes higher than where niota is declared and 2) the inverse
                            Ok nproofs -> Ok $ vInsertVar state' var niota nproofs
                            Error e -> Error e
                (Return expr : _) ->
                    let (VState (VScopeState (_, proofs, _, _), _, _, _)) = state
                     in let (niota, state') = popIotaFromSeq (vAdvanceStatement state)
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
                    valBlock $ VState (VScopeState (empty, [], Continuations (bstmts ++ [EndBlock]), Just (vScopeAdvanceStatement scope)), iotaCtx, proofCtx, iotaseq)
                (EndBlock : _) -> case pscope of
                    Just ps -> Ok $ VState (ps, iotaCtx, proofCtx, iotaseq)
                    _ -> error "EndBlock must have a parent state"

reflProofsByProofs :: [IotaProof] -> [IotaProof] -> [IotaProof]
reflProofsByProofs lproofs = concatMap (reflProofsByProof lproofs)

valValidationStatement :: VState -> ValidationStatement -> Result VState String
valValidationStatement state (Rewrite rwrule) = valRewrite (vAdvanceStatement state) rwrule
valValidationStatement state (ProofAssert varproof) =
    let (VState (VScopeState (_, proofs, _, _), _, _, _)) = state
     in let state' = vAdvanceStatement state
         in let iotaProof = varProofToIotaProof varproof state'
             in if iotaProof `elem` proofs
                    then Ok state'
                    else Error $ "Assertion failed: " ++ show varproof
valValidationStatement state (AssignProofVar var expr) =
    let (niota, state') = popIotaFromSeq (vAdvanceStatement state)
     in case valExpression state' niota expr of
            Ok nproofs -> Ok $ vInsertVar state' var niota nproofs
            Error e -> Error e

valRewrite :: VState -> RwRule -> Result VState String
valRewrite state (Refl varProof) =
    let (VState (VScopeState (iotas, proofs, c, pscope), iotaCtx, proofCtx, iotaseq)) = state
     in let iotaProof = varProofToIotaProof varProof state
         in let newProofs = reflProofsByProofs proofs proofs -- TODO: limit to proofs with iotaProof
             in Ok $ VState (VScopeState (iotas, proofs ++ newProofs, c, pscope), iotaCtx, proofCtx, iotaseq)
valRewrite state (Eval var) =
    let (VState (VScopeState (iotas, proofs, c, pscope), iotaCtx, proofCtx, iotaseq)) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "Undefined variable: " ++ var
                Just iota -> Ok $ VState (VScopeState (iotas, evalIota iota proofs (iotaCtx, proofCtx) ++ proofs, c, pscope), iotaCtx, proofCtx, iotaseq)
valRewrite (VState (VScopeState (iotas, proofs, c, pscope), iotaCtx, proofCtx, iotaseq)) EvalAll =
    let newProofs = concatMap (\p -> evalIotaProof p proofs (iotaCtx, proofCtx)) proofs
     in Ok $ VState (VScopeState (iotas, proofs ++ newProofs, c, pscope), iotaCtx, proofCtx, iotaseq)
valRewrite state (EqToLtPlus1 var) =
    let (VState (VScopeState (iotas, proofs, c, pscope), iotaCtx, proofCtx, niota : c1iota : iotaseq)) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "Undefined variable: " ++ var
                Just iota ->
                    let withNewProofs =
                            proofs
                                ++ [ FApp (CTerm (builtinFunct (Rel Lt))) [ATerm iota, ATerm niota]
                                   , FApp eqProof [ATerm niota, FApp (CTerm (builtinFunct Plus)) [ATerm iota, ATerm c1iota]]
                                   , FApp eqProof [ATerm c1iota, CTerm $ VInt 1]
                                   ]
                     in let withEvaledProofs = withNewProofs ++ evalIota niota withNewProofs (iotaCtx, proofCtx)
                         in let withRefledNewProofs =
                                    withEvaledProofs
                                        ++ reflProofsByProofs withEvaledProofs withEvaledProofs -- TODO: Maybe limit to new proofs
                             in Ok $ VState (VScopeState (iotas, withRefledNewProofs, c, pscope), iotaCtx, proofCtx, iotaseq)

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
    let (State (scope, valCtx), fval : argVals) = evalExpressionList sstate (fnExpr : argExprs)
     in (Just $ evalFunct fval valCtx argVals, State (scope, valCtx))

-- State -> iota of result -> expression -> Result [proofs about result iota] String
valExpression :: VState -> Iota -> Expression -> Result [IotaProof] String -- produces only the new proofs
valExpression _ iota (Val val) = Ok [FApp eqProof [ATerm iota, CTerm val]]
-- foldr (\iota _ -> [C iota Eq val]) [] miota
valExpression state iota (Var var) =
    let omiota = vLookupVar state var
     in case omiota of
            Nothing -> Error $ "Undefined variable: " ++ var
            Just oiota -> Ok [FApp eqProof [ATerm iota, ATerm oiota]]
valExpression (VState (scope, iotaCtx, proofCtx, iotaseq)) iota (F fnexpr argexprs) =
    let VScopeState (_, proofs, _, _) = scope
     in let tiotalist = iotaseq
         in let functResults =
                    let (niota : tiotalist') = tiotalist
                     in let fnProofResult = valExpression (VState (scope, iotaCtx, proofCtx, tiotalist)) niota fnexpr
                         in case fnProofResult of
                                Error e -> Error e
                                Ok fnProofs ->
                                    let reflOnceFnProofs = reflProofsByProofs fnProofs (proofs ++ proofCtx)
                                     in case concreteValOfIotaMaybe niota (reflOnceFnProofs ++ fnProofs) of
                                            Just _ -> valFunctExprHelper (VState (scope, iotaCtx, proofCtx, tiotalist')) iota fnexpr argexprs
                                            Nothing -> Error "Not able to determine function object for validation"
             in case functResults of
                    Ok (flatfinputproofs, functProofs, niotas) ->
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

-- -> (argProofs, functresultproofs, new iotas)
valFunctExprHelper :: VState -> Iota -> Expression -> [Expression] -> Result ([IotaProof], [IotaProof], [Iota]) String
valFunctExprHelper (VState (scope, iotaCtx, proofCtx, iotaseq)) iota fnexpr exprargs =
    let VScopeState (_, proofs, _, _) = scope
     in let (fInputProofResults, niotas) =
                zipMap
                    (fnexpr : exprargs)
                    iotaseq
                    -- TODO: remove new iotas from iotaseq before using below
                    (flip (valExpression $ VState (scope, iotaCtx, proofCtx, iotaseq))) -- proofs of input expression in terms of new iotas
                    -- If finputproofs = [A niota rel oi] where oi is already defined, replace with the definition of oi
         in case flatResultMap id fInputProofResults of
                Error e -> Error e
                Ok finputproofs ->
                    let flatfinputproofs = concat finputproofs
                     in let refloncefiproofs =
                                reflProofsByProofs flatfinputproofs (proofs ++ proofCtx)
                         in let concreteProofs = filter abstractLhsEqConcreteRhs flatfinputproofs -- C niota rel val
                             in let ps = refloncefiproofs ++ concreteProofs
                                 in let (fniota : argiotas) = niotas
                                     in case valFunct fniota (iotaCtx, proofCtx) argiotas ps iota of
                                            Ok functProofs -> Ok (flatfinputproofs, functProofs, niotas)
                                            Error e -> Error e

evalFunct :: Value -> Map Variable Value -> [Value] -> Value
evalFunct (VFunct _ _ (BuiltinFunct builtin) _) valCtx args =
    evalBuiltinFunct builtin args
evalFunct (VFunct vars _ (NativeFunct block) _) valCtx args =
    let (argVals, _) = zipMap vars args (,)
     in -- Give args the function parameter names
        let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
         in let scope = ScopeState (varMap, Continuations block, Just emptyScopeState)
             in case evalReturningBlock (State (scope, valCtx)) of
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

-- Takes: Funct, funct input iotas, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunct :: Iota -> (Map Variable Iota, [IotaProof]) -> [Iota] -> [IotaProof] -> Iota -> Result [IotaProof] String
valFunct fniota ctx iiotas iproofs retiota =
    let vals =
            flatMaybeMap (`concreteValOfIotaMaybe` iproofs) (fniota : iiotas)
     in case vals of
            Just (fnVal : argVals) ->
                let (iotaCtx, proofCtx) = ctx
                 in Ok [FApp eqProof [ATerm retiota, CTerm (evalFunct fnVal (iotaMapToConcreteMap iotaCtx proofCtx) argVals)]]
            Nothing ->
                Error
                    ( "Funct agrs not validated. Input Iotas: "
                        ++ show iiotas
                        ++ ". Input Proofs: "
                        ++ show iproofs
                    )
