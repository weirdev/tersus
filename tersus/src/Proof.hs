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
                , FApp (CTerm (VFunct _ _ _ (BuiltinFunct funct) _)) args
                ]
        )
    proofs
    ctx | eqFunct == eqProof =
        -- TODO: Make recursive
        case collectMaybes maybeATermProofToIota args of
            Just iotas -> case iotasToValues iotas proofs of
                -- TODO: Produce FApp with CTerm
                Just values ->
                    let (iotaCtx, proofCtx) = ctx
                     in [FApp eqFunct [ATerm iota, CTerm $ evalFunctCall (builtinFunct funct) (iotaMapToConcreteMap iotaCtx proofCtx) values]]
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
        case remainingIotas of
            nextIota : _ -> Ok $ VState vScopeState iotaCtx proofCtx [nextIota]
            [] -> Error "Validation exhausted the available iota sequence"
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
         in let nxtStmt = doTraceStatements ("valNextStatement: " ++ show (head stmts)) (head stmts)
             in case nxtStmt of
                    Assign var expr ->
                        let (niota, state') = doTrace "assign" (popIotaFromSeq (vAdvanceStatement state))
                         in case valExpression state' niota expr of
                                 -- TODO: Partition nproofs into 1) those that only use niota and iotas
                                 -- from scopes higher than where niota is declared and 2) the inverse
                                 Ok (exprState, nproofs) -> doTrace3 (var ++ " = " ++ show nproofs) (Ok $ vInsertVar exprState var niota nproofs)
                                 Error e -> Error e
                    Return expr ->
                        let (VState (VScopeState _ proofs c _) _ _ _) = state
                         in let (niota, state') = doTrace ("return: " ++ show c) (popIotaFromSeq (vAdvanceStatement state))
                              in case valExpression state' niota expr of
                                     Ok (exprState, nproofs) ->
                                         -- TODO: Break out of the current block and return the value
                                         -- TODO: Shoud vSetReturn also pass up the nproofs?
                                         let refledNProofs = reflProofsByProofs nproofs proofs
                                          in let visibleIotas = niota : map snd (toList (vGetVars exprState))
                                           in let state'' = vTopLevelScope exprState
                                               in Ok $ vSetReturn state'' niota (filter (proofOnlyOfIotasOrConst visibleIotas) (nproofs ++ refledNProofs))
                                     Error e -> Error e
                    ValidationStatement valStmt -> valValidationStatement state valStmt
                    Block bstmts ->
                        valBlock $ VState (VScopeState empty [] (Continuations $ bstmts ++ [EndBlock]) (Just $ vScopeAdvanceStatement scope)) iotaCtx proofCtx iotaseq
                    EndBlock -> case pscope of
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
                    else doTrace4 ("Had vars: " ++ show (vGetVars state')) (doTrace4 ("Had proofs: " ++ show proofs) (Error $ "Assertion failed: " ++ show varproof))
valValidationStatement state (AssignProofVar var expr) =
    let VState scope _ _ _ = state
     in let VScopeState _ _ c _ = scope
         in let state' = vAdvanceStatement state
             in assignProofVarImpl state' var expr

assignProofVarImpl :: VState -> Variable -> Expression -> Result VState String
assignProofVarImpl state var expr =
    let (niota, state') = popIotaFromSeq state
      in case doTrace "apv1" (valExpression state' niota expr) of
             -- TODO: Convert expression to iota proof p1, and add additional proof (niota == p1)
             Ok (exprState, nproofs) ->
                 -- TODO: Should we be doing this in the ordinary valExpression?
                 let nonEvalProof =
                        let exprAsProof = varProofToIotaProof (exprToProof expr) exprState
                         in FApp eqProof [ATerm niota, exprAsProof]
                  in let reverseNonEvalProof = reverseEqProof nonEvalProof
                      in let refledProofs =
                                 reflProofsByProofs (vGetProofs exprState) [nonEvalProof, reverseNonEvalProof]
                          in let newProofs = nonEvalProof : nproofs ++ refledProofs
                              in doTrace2
                                     ("New assign proof var proofs: " ++ show newProofs)
                                     (Ok $ doTrace "apv2" (vInsertVar exprState var niota newProofs))
             Error e -> Error e

valRewrite :: VState -> RwRule -> Result VState String
valRewrite state (Refl varProof) =
    let (VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx iotaseq) = state
     in let iotaProof = varProofToIotaProof varProof state
         in let reverseEqProofs =
                    [ reverseEqProof proof
                    | proof@(FApp funct [_lhs, _rhs]) <- proofs
                    , funct == eqProof
                    ]
             in let newProofs = reflProofsByProofs proofs (proofs ++ reverseEqProofs) -- TODO: limit to proofs with iotaProof
              in Ok $ VState (VScopeState iotas (proofs ++ newProofs) c pscope) iotaCtx proofCtx iotaseq
valRewrite state (Eval var) =
    let (VState (VScopeState iotas proofs c pscope) iotaCtx proofCtx iotaseq) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "(Eval) Undefined variable: " ++ var
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
                Nothing -> Error $ "(EqToLtPlus1) Undefined variable: " ++ var
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
        Nothing -> Error $ "(EqToGtZero) Undefined variable: " ++ var
        Just iota ->
            let shouldProduceRewrite =
                    case iotaToValue iota state of
                        Nothing ->
                            doTrace4 ("Var lacks concrete definition: " ++ var) $
                                -- Do we already have the proof we are trying to produce?
                                let equivProofExists =
                                        let allProofs = doTrace4 ("Vars: " ++ show (vGetVars state) ++ " All proofs: " ++ show (vGetProofs state)) vGetProofs state
                                         in let matcher =
                                                    let gtProofs = extractNDegreeEquivalentsInclusive 10 (CTerm (builtinFunct (Rel Gt))) allProofs
                                                     in let lhsProofs = extractNDegreeEquivalentsInclusive 10 (ATerm iota) allProofs
                                                         in let rhsProofs = extractNDegreeEquivalentsInclusive 10 (CTerm (VInt 0)) allProofs
                                                             in FAppMatch
                                                                    (ProofMatchTerm (MatchEquivalents gtProofs))
                                                                    [ ProofMatchTerm (MatchEquivalents lhsProofs)
                                                                    , ProofMatchTerm (MatchEquivalents rhsProofs)
                                                                    ]
                                             in any (matchIotaProof matcher) allProofs
                                 in if equivProofExists
                                        then Ok ()
                                        else Error $ "Var lacks concrete definition and no equivalent proof exists: " ++ var
                        -- If we have the proof, we are done
                        -- doTrace4
                        -- ("Var w/o def: " ++ var ++ " Iotas: " ++ show (vGetVars state) ++ " Proofs: " ++ show (vGetProofs state))
                        Just (VInt num) ->
                            doTrace4 ("EqToGtZero found concrete val: " ++ show num) $
                                if num > 0
                                    then
                                        Ok ()
                                    else Error $ "Var is not greater than 0: " ++ var
                        Just _ -> Error $ "Var is not an int: " ++ var
             in case shouldProduceRewrite of
                    Ok{} ->
                        let gtZeroProof = FApp (CTerm (builtinFunct (Rel Gt))) [ATerm iota, CTerm (VInt 0)]
                         in let refledNewProof = reflProofsByProofs [gtZeroProof] (vGetProofs state)
                             in let newproofs = gtZeroProof : refledNewProof
                                 in Ok $ vInsertProofs state newproofs
                    Error e -> Error e

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
            Nothing -> error $ "Undefined variable: " ++ var
evalExpression sstate (F fnExpr argExprs) =
    let (State scope valCtx, fval : argVals) = evalExpressionList sstate (fnExpr : argExprs)
     in (Just $ evalFunctCall fval valCtx argVals, State scope valCtx)

-- State -> iota of result -> expression -> Result (updated state, proofs about result iota) String
valExpression :: VState -> Iota -> Expression -> Result (VState, [IotaProof]) String
valExpression state iota (Val val) =
    let functValResult = validateValue state val
     in let r = mapResult (\validatedVal -> (state, [FApp eqProof [ATerm iota, CTerm validatedVal]])) functValResult
             in doTrace3 (show r) r
valExpression state iota (Var var) =
    let omiota = vLookupVar state var
     in case omiota of
            Nothing -> Error $ "(Validate Expression) Undefined variable: " ++ var ++ " \nState: " ++ show state
            Just oiota ->
                let iotaEq = FApp eqProof [ATerm iota, ATerm oiota]
                 in let reverseIotaEq = reverseEqProof iotaEq
                      in -- Propagate proofs across the fresh alias in both directions.
                         let refledEqProofs =
                                 reflProofsByProofs (vGetProofs state) [iotaEq, reverseIotaEq]
                          in Ok (state, iotaEq : reverseIotaEq : refledEqProofs)
valExpression (VState scope iotaCtx proofCtx iotaseq) iota (F fnexpr argexprs) =
    let functResults = valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq) fnexpr argexprs iota
     in case functResults of
            Ok (nextState, _flatfinputproofs, functProofs, _niotas) ->
                let nonEvalProof =
                        FApp
                            eqProof
                            [ ATerm iota
                            , varProofToIotaProof (exprToProof (F fnexpr argexprs)) nextState
                            ]
                 in Ok (nextState, nonEvalProof : functProofs)
            Error e -> Error e
valExpression _ _ e = Error $ "Unsupported expression: " ++ show e

validateValue :: VState -> Value -> Result Value String
validateValue state val = case val of
    VFunct args inputValStmts outputValStmts body _ ->
        mapResult
            (VFunct args inputValStmts outputValStmts body)
            (valFunctDef state args inputValStmts outputValStmts body)
    _ -> Ok val

valFunctDef :: VState -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> FunctBody -> Result [VariableProof] String
valFunctDef state args inputValStmts outputValStmts (NativeFunct stmts) =
    let fnValStateResult =
            let newState = vSetScope state emptyVScopeState
             in let wContinuations =
                        doTrace4
                            ("valFunctDef: Setting conts: " ++ show stmts)
                            (vSetContinuations newState (Continuations stmts))
                 in let (niotas, newState') = popNIotasFromSeq wContinuations (length args)
                     in let (argIotas, _) = zipMap args niotas (,)
                         in let preInputValState = vInsertVars newState' argIotas []
                             in assumeValStmts preInputValState inputValStmts
     in case fnValStateResult of
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
assumeValStmt state (ProofAssert varproof) = Ok $ vInsertProofs state [varProofToIotaProof varproof state]
assumeValStmt state (AssignProofVar var expr) = assignProofVarImpl state var expr

-- Given expression evaluating to a function object, expressions evaluating to
-- the function's arguments, and the iota corresponding to the function return value,
-- validate and return:
-- 1) proofs of input expressions 2) proofs of the evaluated fn result 3) the new iotas used
-- state -> fnexpr -> argexprs -> (argProofs, functresultproofs, new iotas)
valFunctExprHelper :: VState -> Expression -> [Expression] -> Iota -> Result (VState, [IotaProof], [IotaProof], [Iota]) String
valFunctExprHelper (VState scope iotaCtx proofCtx iotaseq) fnexpr exprargs riota =
    let proofs = vGetProofs (VState scope iotaCtx proofCtx iotaseq)
     in -- Get proofs from the function and arg expressions
         let exprsToVal = fnexpr : exprargs
          in let (niotas, iotaseq') = splitAt (length exprsToVal) iotaseq
              in let exprState = VState scope iotaCtx proofCtx iotaseq'
                  in case valExpressionSeq exprState exprsToVal niotas of
                        Error e -> Error e
                        Ok (exprValidatedState, finputproofs) ->
                            let flatfinputproofs = concat finputproofs
                             in let refloncefiproofs =
                                        reflProofsByProofs flatfinputproofs (proofs ++ proofCtx)
                                 in let ps = refloncefiproofs ++ flatfinputproofs
                                     in let (fniota : argiotas) = niotas
                                         in case valFunctCall exprValidatedState fniota argiotas ps riota of
                                                Ok (callState, functProofs) -> Ok (callState, flatfinputproofs, functProofs, niotas)
                                                Error e -> Error e

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

evalFunctCall :: Value -> Map Variable Value -> [Value] -> Value
evalFunctCall (VFunct _ _ _ (BuiltinFunct builtin) _) valCtx args =
    evalBuiltinFunct builtin args
evalFunctCall (VFunct vars _ _ (NativeFunct block) _) valCtx args =
    let (argVals, _) = zipMap vars args (,)
     in -- Give args the function parameter names
        let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
         in let scope = ScopeState varMap (Continuations block) (Just emptyScopeState)
             in case evalReturningBlock (State scope valCtx) of
                    (_, Just val) -> val
                    _ -> error "Function did not return a value"
evalFunctCall _ _ _ = error "Object being called must be a function"

evalBuiltinFunct :: BuiltinFunct -> [Value] -> Value
evalBuiltinFunct Size [VIntList l] = VInt (fromIntegral (length l))
evalBuiltinFunct Size _ = error "Size only valid for IntList"
evalBuiltinFunct First [VIntList []] = error "First requires a non-empty IntList"
evalBuiltinFunct First [VIntList l] = VInt (head l)
evalBuiltinFunct First _ = error "First only valid for IntList"
evalBuiltinFunct Last [VIntList []] = error "Last requires a non-empty IntList"
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
    -- Get the concrete function object
    -- TODO: Support function proof evaluation with less than the full concrete function
    case concreteValOfIotaMaybe fniota iproofs of
        Just fnVal -> case fnVal of
            VFunct varArgs inputValStmts _ _ exportedProofs ->
                -- Validate the inputs are valid wrt the function signature
                case valFunctInput state varArgs iiotas iproofs inputValStmts of
                    Error e -> Error $ "Funct input validation failed: " ++ e
                    Ok fnValState ->
                        let exportStateResult = instantiateFunctOutputProofs state varArgs iiotas retiota exportedProofs
                         in case exportStateResult of
                                Error e -> Error e
                                Ok (stateWithExports, instantiatedProofs) ->
                                    let argvalsMaybe = collectMaybes (`concreteValOfIotaMaybe` iproofs) iiotas
                                     in case argvalsMaybe of
                                            Just argVals ->
                                                let (VState _ iotaCtx proofCtx _) = fnValState
                                                 in let functResult = evalFunctCall fnVal (iotaMapToConcreteMap iotaCtx proofCtx) argVals
                                                     in Ok (stateWithExports, FApp eqProof [ATerm retiota, CTerm functResult] : instantiatedProofs)
                                            Nothing ->
                                                Ok (stateWithExports, instantiatedProofs)
            _ -> Error "Non-function value called"
        Nothing ->
            Error $
                "Function object not validated. Function iota: "
                    ++ show fniota
                    ++ ". Input proofs: "
                    ++ show iproofs

instantiateFunctOutputProofs :: VState -> [Variable] -> [Iota] -> Iota -> [VariableProof] -> Result (VState, [IotaProof]) String
instantiateFunctOutputProofs state _ _ _ [] = Ok (state, [])
instantiateFunctOutputProofs state varArgs argIotas retiota exportedProofs =
    let exportedNames = nub (concatMap proofVars exportedProofs)
     in let proofVarNames = filter (\var -> var /= "return" && notElem var varArgs) exportedNames
         in let (proofVarIotas, state') = popNIotasFromSeq state (length proofVarNames)
             in let argBindings =
                        zip (varArgs ++ ["return"]) (argIotas ++ [retiota])
                 in let proofBindings = proofVarNames `zip` proofVarIotas
                      in let exportBindings = argBindings ++ proofBindings
                          in let exportState = buildVarToIotaState state' exportBindings [] (case state' of VState _ _ _ remaining -> remaining)
                              in let instantiatedProofs = map (`varProofToIotaProof` exportState) exportedProofs
                                  in Ok (vInsertVars state' proofBindings instantiatedProofs, instantiatedProofs)

-- Validate the input arguments of a function call using the functions validation block
-- (outer) state -> function arg names -> function arg iotas -> function arg proofs -> function validation block
-- -> function validation state
valFunctInput :: VState -> [Variable] -> [Iota] -> [IotaProof] -> [ValidationStatement] -> Result VState String
valFunctInput state _ _ _ [] = Ok state
valFunctInput state varArgs argIotas argProofs valStmts =
    let VState scope iotaCtx proofCtx iotaseq = state
     in let (argIotasMap, _) =
                doTrace3
                    ("Arg iotas: " ++ show argIotas)
                    (doTrace3 ("Arg proofs: " ++ show argProofs) (zipMap varArgs argIotas (,)))
         in let stmts = map ValidationStatement valStmts
             in valBlock $
                    VState
                        (VScopeState (Data.Map.fromList argIotasMap) (argProofs ++ vGetProofs state) (Continuations stmts) Nothing)
                        iotaCtx
                        proofCtx
                        iotaseq

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
