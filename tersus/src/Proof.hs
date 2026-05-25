module Proof where

import Data.Map (
    Map,
    empty,
    fromList,
    insert,
    toList,
  )

import Data.List (nub)
import Data.Maybe (mapMaybe)

import qualified ProofEngine as Engine
import ProofHelpers
import StdLib
import TersusTypes
import Utils

-- Public fns
evaluate :: [Statement] -> Result State String
evaluate [] = Ok initState
evaluate l = evalBlock $ initStateWStatements l

validate :: [Statement] -> Result VState String
validate [] = Ok $ VState emptyVScopeState empty [] []
validate l = case valBlock $ initVStateWStatements l of
    Ok (VState vScopeState iotaCtx proofCtx remainingIotas) ->
        case remainingIotas of
            nextIota : _ -> Ok $ VState vScopeState iotaCtx proofCtx [nextIota]
            [] -> Error "Validation exhausted the available iota sequence"
    Error e -> Error e

-- Private fns
evalBlock :: State -> Result State String
evalBlock state = case state of
    State (ScopeState _ (Continuations []) _) _ -> Ok state
    State (ScopeState _ (Continuations (_ : _)) _) _ ->
        case evalNextStatement state of
            Ok nState -> evalBlock nState
            Error e -> Error e

evalReturningBlock :: State -> Result (State, Maybe Value) String
evalReturningBlock state =
    case evalBlock state of
        Ok rState -> Ok (rState, getReturn rState)
        Error e -> Error e

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
            Ok rstate ->
                case vGetReturn rstate of
                    Ok ret -> Ok (rstate, Just ret)
                    Error e -> Error e
            Error e -> Error e

evalNextStatement :: State -> Result State String
evalNextStatement state = case nextStatement state of
    Ok (Assign var expr) -> evalAssignStatement state var expr
    Ok (Return expr) -> evalReturnStatement state expr
    Ok ValidationStatement{} -> advanceStatement state
    Ok (Block statements) -> evalBlockStatement state statements
    Ok EndBlock -> evalEndBlockStatement state
    Error e -> Error e

nextStatement :: State -> Result Statement String
nextStatement (State (ScopeState _ (Continuations (stmt : _)) _) _) = Ok stmt
nextStatement _ = Error "No next statement available"

evalAssignStatement :: State -> Variable -> Expression -> Result State String
evalAssignStatement state var expr =
    case advanceStatement state of
        Ok advancedState ->
            case evalExpression advancedState expr of
                Ok (val, rState) -> Ok $ insertVar rState var val
                Error e -> Error e
        Error e -> Error e

evalReturnStatement :: State -> Expression -> Result State String
evalReturnStatement state expr =
    case advanceStatement state of
        Ok advancedState ->
            case evalExpression advancedState expr of
                Ok (val, rState) -> Ok $ setReturn (topLevelScope rState) val
                Error e -> Error e
        Error e -> Error e

evalBlockStatement :: State -> [Statement] -> Result State String
evalBlockStatement (State scope ctxVals) statements =
    case scopeAdvanceStatement scope of
        Ok advancedScope ->
            evalBlock $
                State
                    (ScopeState empty (Continuations (statements ++ [EndBlock])) (Just advancedScope))
                    ctxVals
        Error e -> Error e

evalEndBlockStatement :: State -> Result State String
evalEndBlockStatement (State (ScopeState _ _ pScope) ctxVals) =
    case pScope of
        Just rpScope -> Ok $ State rpScope ctxVals
        _ -> Error "EndBlock must have a parent scope"

valNextStatement :: VState -> Result VState String
valNextStatement state =
    case vNextStatement state of
        Ok stmt ->
            let tracedStmt = doTraceStatements ("valNextStatement: " ++ show stmt) stmt
             in case tracedStmt of
                    Assign var expr -> valAssignStatement state var expr
                    Return expr -> valReturnStatement state expr
                    ValidationStatement valStmt -> valValidationStatement state valStmt
                    Block bstmts -> valBlockStatement state bstmts
                    EndBlock -> valEndBlockStatement state
        Error e -> Error e

vNextStatement :: VState -> Result Statement String
vNextStatement (VState (VScopeState _ _ (Continuations (stmt : _)) _) _ _ _) = Ok stmt
vNextStatement _ = Error "No next validation statement available"

valAssignStatement :: VState -> Variable -> Expression -> Result VState String
valAssignStatement state var expr =
    case vAdvanceStatement state of
        Ok advancedState ->
            case popIotaFromSeq advancedState of
                Ok (niota, state') ->
                    case valExpression state' niota expr of
                        Ok (exprState, nproofs) -> doTrace3 (var ++ " = " ++ show nproofs) (Ok $ vInsertVar exprState var niota nproofs)
                        Error e -> Error e
                Error e -> Error e
        Error e -> Error e

-- Return proofs are trimmed to names visible at the call boundary so nested block-local
-- iotas do not leak out when a function or block returns a value.
valReturnStatement :: VState -> Expression -> Result VState String
valReturnStatement state expr =
    let VState (VScopeState _ proofs c _) _ _ _ = state
     in case vAdvanceStatement state of
            Ok advancedState ->
                case popIotaFromSeq advancedState of
                    Ok (niota, state') ->
                        case valExpression state' niota expr of
                            Ok (exprState, nproofs) ->
                                let refledNProofs = reflProofsByProofs nproofs proofs
                                    visibleIotas = niota : map snd (toList (vGetVars exprState))
                                    state'' = vTopLevelScope exprState
                                 in Ok $ vSetReturn state'' niota (filter (proofOnlyOfIotasOrConst visibleIotas) (nproofs ++ refledNProofs))
                            Error e -> Error e
                    Error e -> Error e
            Error e -> Error e

valBlockStatement :: VState -> [Statement] -> Result VState String
valBlockStatement (VState scope iotaCtx proofCtx iotaseq) bstmts =
    case vScopeAdvanceStatement scope of
        Ok advancedScope -> valBlock $ VState (VScopeState empty [] (Continuations $ bstmts ++ [EndBlock]) (Just advancedScope)) iotaCtx proofCtx iotaseq
        Error e -> Error e

valEndBlockStatement :: VState -> Result VState String
valEndBlockStatement (VState (VScopeState _ _ _ pscope) iotaCtx proofCtx iotaseq) =
    case pscope of
        Just ps -> Ok $ VState ps iotaCtx proofCtx iotaseq
        _ -> Error "EndBlock must have a parent state"

-- Rewrite proofs using eq relation
-- proofs to change -> eq relations -> updated proofs
reflProofsByProofs :: [IotaProof] -> [IotaProof] -> [IotaProof]
reflProofsByProofs = Engine.reflectProofsByProofs

valValidationStatement :: VState -> ValidationStatement -> Result VState String
valValidationStatement state (Rewrite rwrule) =
    case vAdvanceStatement (doTrace "starting rewrite" state) of
        Ok advancedState -> doTrace "rewrite" (valRewrite advancedState rwrule)
        Error e -> Error e
valValidationStatement state (ProofAssert varproof) =
    case vAdvanceStatement (doTrace "proofAssert" state) of
        Ok state' ->
            case varProofToIotaProof varproof state' of
                Ok iotaProof ->
                    let proofs = vGetProofs state'
                        proofContext = Engine.proofContextFromFacts proofs
                     in if Engine.entails iotaProof proofContext
                            then Ok state'
                            else doTrace4 ("Had vars: " ++ show (vGetVars state')) (doTrace4 ("Had proofs: " ++ show proofs) (Error $ "Assertion failed: " ++ show varproof))
                Error e -> Error e
        Error e -> Error e
valValidationStatement state (AssignProofVar var expr) =
    case vAdvanceStatement state of
        Ok advancedState -> assignProofVarImpl advancedState var expr
        Error e -> Error e

assignProofVarImpl :: VState -> Variable -> Expression -> Result VState String
assignProofVarImpl state var expr =
    case popIotaFromSeq state of
        Ok (niota, state') ->
            case doTrace "apv1" (valExpression state' niota expr) of
                -- TODO: Convert expression to iota proof p1, and add additional proof (niota == p1)
                Ok (exprState, nproofs) ->
                    -- TODO: Should we be doing this in the ordinary valExpression?
                    case varProofToIotaProof (exprToProof expr) exprState of
                        Ok exprAsProof ->
                            let nonEvalProof = FApp eqProof [ATerm niota, exprAsProof]
                                reverseNonEvalProof = reverseEqProof nonEvalProof
                                refledProofs =
                                    reflProofsByProofs (vGetProofs exprState) [nonEvalProof, reverseNonEvalProof]
                                newProofs = nonEvalProof : nproofs ++ refledProofs
                             in doTrace2
                                    ("New assign proof var proofs: " ++ show newProofs)
                                    (Ok $ doTrace "apv2" (vInsertVar exprState var niota newProofs))
                        Error e -> Error e
                Error e -> Error e
        Error e -> Error e

valRewrite :: VState -> RwRule -> Result VState String
valRewrite state (Refl varProof) = rewriteRefl state varProof
valRewrite state (Eval var) = rewriteEval state var
valRewrite state EvalAll = rewriteEvalAll state
valRewrite state (EqToLtPlus1 var) = rewriteEqToLtPlus1 state var
valRewrite state (EqToGtZero var) = rewriteEqToGtZero state var

applyEngineRewrite :: VState -> Engine.EngineRewriteRule -> Result VState String
applyEngineRewrite state rule =
    let oldContext = Engine.proofContextFromFacts (vGetProofs state)
     in case Engine.applyRewrite evalBuiltinFunct rule oldContext of
            Ok newContext ->
                Ok $ vInsertProofs state (Engine.proofContextDelta oldContext newContext)
            Error e -> Error e

rewriteRefl :: VState -> VariableProof -> Result VState String
rewriteRefl state varProof =
    case varProofToIotaProof varProof state of
        Ok _iotaProof ->
            applyEngineRewrite state Engine.EngineRefl
        Error e -> Error e

rewriteEval :: VState -> Variable -> Result VState String
rewriteEval state var =
    case vLookupVar state var of
        Nothing -> Error $ "(Eval) Undefined variable: " ++ var
        Just iota ->
            applyEngineRewrite state (Engine.EngineEval iota)

rewriteEvalAll :: VState -> Result VState String
rewriteEvalAll state =
    applyEngineRewrite state Engine.EngineEvalAll

rewriteEqToLtPlus1 :: VState -> Variable -> Result VState String
rewriteEqToLtPlus1 state@(VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx (niota : c1iota : iotaseq)) var =
    case vLookupVar state var of
        Nothing -> Error $ "(EqToLtPlus1) Undefined variable: " ++ var
        Just iota ->
            applyEngineRewrite
                (VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx iotaseq)
                (Engine.EngineEqToLtPlus1 iota niota c1iota)
rewriteEqToLtPlus1 _ _ = Error "EqToLtPlus1 requires two fresh iotas"

rewriteEqToGtZero :: VState -> Variable -> Result VState String
rewriteEqToGtZero state var =
    case vLookupVar state var of
        Nothing -> Error $ "(EqToGtZero) Undefined variable: " ++ var
        Just iota ->
            case applyEngineRewrite state (Engine.EngineEqToGtZero iota) of
                Ok state' -> Ok state'
                Error e -> Error $ "(EqToGtZero) " ++ e ++ ": " ++ var

evalExpressionList :: State -> [Expression] -> Result (State, [Value]) String
evalExpressionList state [] = Ok (state, [])
evalExpressionList sstate (expr : exprs) =
    case evalExpression sstate expr of
        Ok (val, estate) ->
            case evalExpressionList estate exprs of
                Ok (state, vals) -> Ok (state, val : vals)
                Error e -> Error e
        Error e -> Error e

evalExpression :: State -> Expression -> Result (Value, State) String
evalExpression state (Val val) = Ok (val, state)
evalExpression state (Var var) =
    case lookupVar state var of
        Just val -> Ok (val, state)
        Nothing -> Error $ "Undefined variable: " ++ var
evalExpression sstate (F fnExpr argExprs) =
    case evalExpressionList sstate (fnExpr : argExprs) of
        Ok (State scope valCtx, fval : argVals) ->
            case evalFunctCall fval valCtx argVals of
                Ok val -> Ok (val, State scope valCtx)
                Error e -> Error e
        Ok (_, []) -> Error "Function expression must produce a value"
        Error e -> Error e

-- State -> iota of result -> expression -> Result (updated state, proofs about result iota) String
valExpression :: VState -> Iota -> Expression -> Result (VState, [IotaProof]) String
valExpression state iota (Val val) = valExpressionValue state iota val
valExpression state iota (Var var) = valExpressionVar state iota var
valExpression state iota (F fnexpr argexprs) = valExpressionFunction state iota fnexpr argexprs
valExpression _ _ e = Error $ "Unsupported expression: " ++ show e

valExpressionValue :: VState -> Iota -> Value -> Result (VState, [IotaProof]) String
valExpressionValue state iota val =
    let functValResult = validateValue state val
        r = mapResult (\validatedVal -> (state, [FApp eqProof [ATerm iota, CTerm validatedVal]])) functValResult
     in doTrace3 (show r) r

valExpressionVar :: VState -> Iota -> Variable -> Result (VState, [IotaProof]) String
valExpressionVar state iota var =
    case vLookupVar state var of
        Nothing -> Error $ "(Validate Expression) Undefined variable: " ++ var ++ " \nState: " ++ show state
        Just oiota ->
            let iotaEq = FApp eqProof [ATerm iota, ATerm oiota]
                reverseIotaEq = reverseEqProof iotaEq
                refledEqProofs = reflProofsByProofs (vGetProofs state) [iotaEq, reverseIotaEq]
             in Ok (state, iotaEq : reverseIotaEq : refledEqProofs)

valExpressionFunction :: VState -> Iota -> Expression -> [Expression] -> Result (VState, [IotaProof]) String
valExpressionFunction (VState scope iotaCtx proofCtx iotaseq) iota fnexpr argexprs =
    case valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq) fnexpr argexprs iota of
        Ok (nextState, _flatfinputproofs, functProofs, _niotas) ->
            case varProofToIotaProof (exprToProof (F fnexpr argexprs)) nextState of
                Ok fnProof ->
                    let nonEvalProof = FApp eqProof [ATerm iota, fnProof]
                     in Ok (nextState, nonEvalProof : functProofs)
                Error e -> Error e
        Error e -> Error e

validateValue :: VState -> Value -> Result Value String
validateValue state val = case val of
    VFunct args inputValStmts outputValStmts body _ ->
        mapResult
            (VFunct args inputValStmts outputValStmts body)
            (valFunctDef state args inputValStmts outputValStmts body)
    _ -> Ok val

valFunctDef :: VState -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> FunctBody -> Result [VariableProof] String
valFunctDef state args inputValStmts outputValStmts (NativeFunct stmts) =
    case prepareFunctionValidationState state args inputValStmts stmts of
            Ok fnValState ->
                let valResult =
                        doTrace4
                            ("valFunctDef: Validating body: " ++ show (vGetContinuations fnValState))
                            (doTrace4 ("Preval fn body: Vars: " ++ show (vGetVars fnValState) ++ " Proofs: " ++ show (vGetProofs fnValState)) (valReturningBlock fnValState))
                 in case doTrace3 ("valFunctDef val result: " ++ show valResult) valResult of
                        Ok (bodyState, _) -> exportFunctOutputProofs bodyState args inputValStmts outputValStmts
                        Error e -> Error e
            Error e -> Error e
valFunctDef _ _ _ _ BuiltinFunct{} = Ok [] -- Builtin functions assumed to be validly defined

prepareFunctionValidationState :: VState -> [Variable] -> [ValidationStatement] -> [Statement] -> Result VState String
prepareFunctionValidationState state args inputValStmts stmts =
    let newState = vSetScope state emptyVScopeState
        wContinuations =
            doTrace4
                ("valFunctDef: Setting conts: " ++ show stmts)
                (vSetContinuations newState (Continuations stmts))
     in case popNIotasFromSeq wContinuations (length args) of
            Ok (niotas, newState') ->
                case zipMap args niotas (,) of
                    Ok (argIotas, _) ->
                        let preInputValState = vInsertVars newState' argIotas []
                         in assumeValStmts preInputValState inputValStmts
                    Error e -> Error e
            Error e -> Error e

exportFunctOutputProofs :: VState -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> Result [VariableProof] String
exportFunctOutputProofs bodyState args inputValStmts outputValStmts =
    let bodyStateWithOutput =
            if null outputValStmts
                then Ok bodyState
                else
                    valBlock
                        ( vSetContinuations
                            bodyState
                            (Continuations (map ValidationStatement outputValStmts))
                        )
     in case bodyStateWithOutput of
            Error e -> Error e
            Ok outputState ->
                let allowedNames = nub (args ++ ["return"] ++ concatMap valStmtDefinedVars inputValStmts ++ concatMap valStmtDefinedVars outputValStmts)
                 in let allowedBindings =
                            mapMaybe
                                (\var -> case vLookupVar outputState var of
                                    Just iota -> Just (var, iota)
                                    Nothing -> Nothing)
                                allowedNames
                    in let namedIotas = namedIotaMap allowedBindings
                       in let exportedProofs =
                                  nub $
                                      mapMaybe
                                          (iotaProofToVarProof namedIotas)
                                          ( filter
                                              (proofOnlyOfNamedIotasOrConst namedIotas)
                                              (vGetProofs outputState)
                                          )
                          in Ok exportedProofs

assumeValStmts :: VState -> [ValidationStatement] -> Result VState String
assumeValStmts state [] = Ok state
assumeValStmts state (stmt : stmts) = doTraceStatements ("assumeValStmt: " ++ show stmt) $
    case assumeValStmt state stmt of
        Ok newState -> assumeValStmts newState stmts
        Error e -> Error e

assumeValStmt :: VState -> ValidationStatement -> Result VState String
assumeValStmt state (Rewrite rwrule) = Ok state -- TODO: Instead of ignoring rewrites entirely during assumptions, should we just ignore failures?
--  doTrace4 ("assume rewrite: " ++ show rwrule ++ " Proofs: " ++ show (vGetProofs state)) (valRewrite state rwrule)
assumeValStmt state (ProofAssert varproof) =
    case varProofToIotaProof varproof state of
        Ok proof -> Ok $ vInsertProofs state [proof]
        Error e -> Error e
assumeValStmt state (AssignProofVar var expr) = assignProofVarImpl state var expr

-- Given expression evaluating to a function object, expressions evaluating to
-- the function's arguments, and the iota corresponding to the function return value,
-- validate and return:
-- 1) proofs of input expressions 2) proofs of the evaluated fn result 3) the new iotas used
-- state -> fnexpr -> argexprs -> (argProofs, functresultproofs, new iotas)
valFunctExprHelper :: VState -> Expression -> [Expression] -> Iota -> Result (VState, [IotaProof], [IotaProof], [Iota]) String
valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq) functionExpr argExprs resultIota =
    let proofs = vGetProofs (VState scope iotaCtx proofCtx iotaseq)
     in -- Get proofs from the function and arg expressions
         let exprsToVal = functionExpr : argExprs
          in let (freshIotas, iotaseq') = splitAt (length exprsToVal) iotaseq
               in let exprState = VState scope iotaCtx proofCtx iotaseq'
                   in case valExpressionSeq exprState exprsToVal freshIotas of
                         Error e -> Error e
                         Ok (exprValidatedState, inputProofGroups) ->
                             let flatInputProofs = concat inputProofGroups
                              in let reflectedInputProofs =
                                         reflProofsByProofs flatInputProofs (proofs ++ proofCtx)
                                   in let availableInputProofs = reflectedInputProofs ++ flatInputProofs
                                      in case freshIotas of
                                            functionIota : inputIotas ->
                                                case valFunctCall exprValidatedState functionIota inputIotas availableInputProofs resultIota of
                                                    Ok (callState, functionProofs) -> Ok (callState, flatInputProofs, functionProofs, freshIotas)
                                                    Error e -> Error e
                                            [] -> Error "Not enough fresh iotas for function expression"

valExpressionSeq :: VState -> [Expression] -> [Iota] -> Result (VState, [[IotaProof]]) String
valExpressionSeq state [] [] = Ok (state, [])
valExpressionSeq state (expr : exprs) (iota : iotas) =
    case valExpression state iota expr of
        Ok (nextState, proofs) ->
            case valExpressionSeq nextState exprs iotas of
                Ok (finalState, remainingProofs) -> Ok (finalState, proofs : remainingProofs)
                Error e -> Error e
        Error e -> Error e
valExpressionSeq _ _ _ = Error "Expression/iota arity mismatch"

evalFunctCall :: Value -> Map Variable Value -> [Value] -> Result Value String
evalFunctCall (VFunct _ _ _ (BuiltinFunct builtin) _) valCtx args =
    evalBuiltinFunct builtin args
evalFunctCall (VFunct vars _ _ (NativeFunct block) _) valCtx args =
    case zipMap vars args (,) of
        Ok (argVals, _) ->
            let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
                scope = ScopeState varMap (Continuations block) (Just emptyScopeState)
             in case evalReturningBlock (State scope valCtx) of
                    Ok (_, Just val) -> Ok val
                    Ok (_, Nothing) -> Error "Function did not return a value"
                    Error e -> Error e
        Error e -> Error e
evalFunctCall _ _ _ = Error "Object being called must be a function"

evalBuiltinFunct :: BuiltinFunct -> [Value] -> Result Value String
evalBuiltinFunct Size [VIntList l] = Ok $ VInt (fromIntegral (length l))
evalBuiltinFunct Size _ = Error "Size only valid for IntList"
evalBuiltinFunct First [VIntList []] = Error "First requires a non-empty IntList"
evalBuiltinFunct First [VIntList l] = Ok $ VInt (head l)
evalBuiltinFunct First _ = Error "First only valid for IntList"
evalBuiltinFunct Last [VIntList []] = Error "Last requires a non-empty IntList"
evalBuiltinFunct Last [VIntList l] = Ok $ VInt (last l)
evalBuiltinFunct Last _ = Error "Last only valid for IntList"
evalBuiltinFunct Minus [VInt v1, VInt v2] = Ok $ VInt (v1 - v2)
evalBuiltinFunct Minus _ = Error "Plus only valid for two ints"
evalBuiltinFunct Plus [VInt v1, VInt v2] = Ok $ VInt (v1 + v2)
evalBuiltinFunct Plus _ = Error "Plus only valid for two ints"
evalBuiltinFunct (Rel Eq) [VInt v1, VInt v2] = Ok $ VBool (v1 == v2)
evalBuiltinFunct (Rel Eq) _ = Error "Eq only valid for two ints"
evalBuiltinFunct (Rel Lt) [VInt v1, VInt v2] = Ok $ VBool (v1 < v2)
evalBuiltinFunct (Rel Lt) _ = Error "Lt only valid for two ints"
evalBuiltinFunct (Rel Gt) [VInt v1, VInt v2] = Ok $ VBool (v1 > v2)
evalBuiltinFunct (Rel Gt) _ = Error "Rt only valid for two ints"
evalBuiltinFunct (Rel LtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 <= v2)
evalBuiltinFunct (Rel LtEq) _ = Error "LtEq only valid for two ints"
evalBuiltinFunct (Rel GtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 >= v2)
evalBuiltinFunct (Rel GtEq) _ = Error "GtEq only valid for two ints"

iotaMapToConcreteMap :: (Ord a) => Map a Iota -> [IotaProof] -> Map a Value
iotaMapToConcreteMap imap proofs =
    Data.Map.fromList $
        mapMaybe
            ( \(k, i) -> case iotaToValueWProofList i proofs of
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
valFunctCall :: VState -> Iota -> [Iota] -> [IotaProof] -> Iota -> Result (VState, [IotaProof]) String
valFunctCall state fniota iiotas iproofs retiota =
    case resolveValidatedFunction fniota iproofs of
        Error e -> Error e
        Ok fnVal@(VFunct varArgs inputValStmts _ _ exportedProofs) ->
            case valFunctInput state varArgs iiotas iproofs inputValStmts of
                Error e -> Error $ "Funct input validation failed: " ++ e
                Ok fnValState ->
                    case instantiateFunctOutputProofs state varArgs iiotas retiota exportedProofs of
                        Error e -> Error e
                        Ok (stateWithExports, instantiatedProofs) ->
                            Ok (stateWithExports, maybeConcreteFunctionResult fnValState fnVal iiotas iproofs retiota instantiatedProofs)

resolveValidatedFunction :: Iota -> [IotaProof] -> Result Value String
resolveValidatedFunction fniota iproofs =
    case concreteValOfIotaMaybe fniota iproofs of
        Just fnVal@VFunct{} -> Ok fnVal
        Just _ -> Error "Non-function value called"
        Nothing ->
            Error $
                "Function object not validated. Function iota: "
                    ++ show fniota
                    ++ ". Input proofs: "
                    ++ show iproofs

maybeConcreteFunctionResult :: VState -> Value -> [Iota] -> [IotaProof] -> Iota -> [IotaProof] -> [IotaProof]
maybeConcreteFunctionResult fnValState fnVal iiotas iproofs retiota instantiatedProofs =
    case collectMaybes (`concreteValOfIotaMaybe` iproofs) iiotas of
        Just argVals ->
            let VState _ iotaCtx proofCtx _ = fnValState
             in case evalFunctCall fnVal (iotaMapToConcreteMap iotaCtx proofCtx) argVals of
                    Ok functResult -> FApp eqProof [ATerm retiota, CTerm functResult] : instantiatedProofs
                    Error _ -> instantiatedProofs
        Nothing -> instantiatedProofs

-- Exported proof variables are rebound to fresh caller-side iotas before the callee's
-- proof templates are converted back into concrete caller-visible proofs.
instantiateFunctOutputProofs :: VState -> [Variable] -> [Iota] -> Iota -> [VariableProof] -> Result (VState, [IotaProof]) String
instantiateFunctOutputProofs state _ _ _ [] = Ok (state, [])
instantiateFunctOutputProofs state varArgs argIotas returnIota exportedProofs =
    let exportedNames = nub (concatMap proofVars exportedProofs)
     in let exportedProofVarNames = filter (\var -> var /= "return" && notElem var varArgs) exportedNames
         in case popNIotasFromSeq state (length exportedProofVarNames) of
                Ok (exportedProofVarIotas, state') ->
                    let argBindings = zip (varArgs ++ ["return"]) (argIotas ++ [returnIota])
                        proofVarBindings = exportedProofVarNames `zip` exportedProofVarIotas
                        exportBindings = argBindings ++ proofVarBindings
                        exportState = buildVarToIotaState state' exportBindings [] (case state' of VState _ _ _ remaining -> remaining)
                     in case flatResultMap (`varProofToIotaProof` exportState) exportedProofs of
                            Ok instantiatedProofs -> Ok (vInsertVars state' proofVarBindings instantiatedProofs, instantiatedProofs)
                            Error e -> Error e
                Error e -> Error e

-- Validate the input arguments of a function call using the functions validation block
-- (outer) state -> function arg names -> function arg iotas -> function arg proofs -> function validation block
-- -> function validation state
valFunctInput :: VState -> [Variable] -> [Iota] -> [IotaProof] -> [ValidationStatement] -> Result VState String
valFunctInput state _ _ _ [] = Ok state
valFunctInput state varArgs argIotas argProofs valStmts =
    let VState scope iotaCtx proofCtx iotaseq = state
     in case doTrace3 ("Arg iotas: " ++ show argIotas) (doTrace3 ("Arg proofs: " ++ show argProofs) (zipMap varArgs argIotas (,))) of
            Ok (argIotasMap, _) ->
                let stmts = map ValidationStatement valStmts
                 in valBlock $
                        VState
                            (VScopeState (Data.Map.fromList argIotasMap) (argProofs ++ vGetProofs state) (Continuations stmts) Nothing)
                            iotaCtx
                            proofCtx
                            iotaseq
            Error e -> Error e

-- TODO: Export validation vars from this into the function body
-- WIP: ^^ + use refling rather than evaling the function call in the input validation

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
        FApp funct [ATerm iota, CTerm (VFunct argList _ _ _ _)]
            | funct == eqProof && argList == varList ->
                Just iota
        _ -> findIotaEqToFn varList tail
