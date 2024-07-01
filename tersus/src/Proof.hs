module Proof where

import Data.Map (
    Map,
    delete,
    empty,
    fromList,
    insert,
    lookup,
    toList,
 )

import Data.Maybe (mapMaybe)

import TersusTypes

-- Map elementwise two lists with a function,
-- returning the result list and the second list trimmed to the length of the first
zipMap :: [a] -> [b] -> (a -> b -> c) -> ([c], [b])
zipMap [] _ _ = ([], [])
zipMap (ah : at) (bh : bt) f =
    let (atr, btr) = zipMap at bt f in (f ah bh : atr, bh : btr)
zipMap (_ : _) [] _ = error "Second list must be at least length of first"

flatMap :: (a -> Either b c) -> [a] -> Either [b] c
flatMap _ [] = Left []
flatMap f (ah : at) = case f ah of
    Left b -> case flatMap f at of
        Left bt -> Left (b : bt)
        Right c -> Right c
    Right c -> Right c

flatMaybeMap :: (a -> Maybe b) -> [a] -> Maybe [b]
flatMaybeMap f as = case flatMap
    ( \a -> case f a of
        Just b -> Left b
        Nothing -> Right ()
    )
    as of
    Left bs -> Just bs
    Right _ -> Nothing

flatResultMap :: (a -> Result b e) -> [a] -> Result [b] e
flatResultMap f as = case flatMap (\a -> case f a of Ok b -> Left b; Error e -> Right e) as of
    Left bs -> Ok bs
    Right e -> Error e

unwrapOrThrow :: String -> Maybe a -> a
unwrapOrThrow _ (Just a) = a
unwrapOrThrow err Nothing = error err

-- Lookup the value of a var in State, including parent scopes
lookupVar :: State -> Variable -> Maybe Value
lookupVar (State (scope, ctxVals)) var = case scopeLookupVar scope var of
    Just val -> Just val
    Nothing -> Data.Map.lookup var ctxVals

scopeLookupVar :: ScopeState -> Variable -> Maybe Value
scopeLookupVar (ScopeState (vals, _, pScope)) var = case Data.Map.lookup var vals of
    Just val -> Just val
    Nothing -> case pScope of
        Just p -> scopeLookupVar p var
        Nothing -> Nothing

vLookupVar :: VState -> Variable -> Maybe Iota
vLookupVar (VState (scope, iotaCtx, _, _)) var = case vScopeLookupVar scope var of
    Just iota -> Just iota
    Nothing -> Data.Map.lookup var iotaCtx

vScopeLookupVar :: VScopeState -> Variable -> Maybe Iota
vScopeLookupVar (VScopeState (iotas, _, _, pScope)) var =
    case Data.Map.lookup var iotas of
        Just iota -> Just iota
        Nothing -> case pScope of
            Just p -> vScopeLookupVar p var
            Nothing -> Nothing

updateExistingVar :: State -> Variable -> Value -> Maybe State
updateExistingVar (State (scope, ctxVals)) var val =
    case scopeUpdateExistingVar scope var val of
        Just ns -> Just $ State (ns, ctxVals)
        Nothing -> Nothing

scopeUpdateExistingVar :: ScopeState -> Variable -> Value -> Maybe ScopeState
scopeUpdateExistingVar (ScopeState (vals, c, pState)) var val =
    case Data.Map.lookup var vals of
        Just _ -> Just (ScopeState (insert var val vals, c, pState))
        Nothing -> case pState of
            Just p -> case scopeUpdateExistingVar p var val of
                Just np -> Just (ScopeState (vals, c, Just np))
                Nothing -> Nothing
            Nothing -> Nothing

vUpdateExistingVar :: VState -> Variable -> Iota -> [IotaProof] -> Maybe VState
vUpdateExistingVar (VState (scope, iotaCtx, proofCtx, iotaseq)) var niota nproofs =
    case vScopeUpdateExistingVar scope var niota nproofs of
        Just ns -> Just $ VState (ns, iotaCtx, proofCtx, iotaseq)
        Nothing -> Nothing

vScopeUpdateExistingVar :: VScopeState -> Variable -> Iota -> [IotaProof] -> Maybe VScopeState
vScopeUpdateExistingVar (VScopeState (iotas, proofs, c, pScope)) var niota nproofs =
    case Data.Map.lookup var iotas of
        Just _ -> Just $ VScopeState (insert var niota iotas, proofs ++ nproofs, c, pScope)
        Nothing -> case pScope of
            Just p -> case vScopeUpdateExistingVar p var niota nproofs of
                Just np -> Just $ VScopeState (iotas, proofs, c, Just np)
                Nothing -> Nothing
            Nothing -> Nothing

insertVar :: State -> Variable -> Value -> State
insertVar (State (ScopeState (vals, c, pState), ctxVals)) var val =
    -- Prefentially update existing var in this or parent scope if the variable is already bound.
    -- Otherwise, just insert the new variable in the current scope.
    case updateExistingVar (State (ScopeState (vals, c, pState), ctxVals)) var val of
        Just s -> s
        Nothing -> State (ScopeState (insert var val vals, c, pState), ctxVals)

vInsertVar :: VState -> Variable -> Iota -> [IotaProof] -> VState
vInsertVar (VState (VScopeState (iotas, proofs, c, pScope), iotaCtx, proofCtx, iotaseq)) var niota nproofs =
    case vUpdateExistingVar (VState (VScopeState (iotas, proofs, c, pScope), iotaCtx, proofCtx, iotaseq)) var niota nproofs of
        Just s -> s
        Nothing -> VState (VScopeState (insert var niota iotas, proofs ++ nproofs, c, pScope), iotaCtx, proofCtx, iotaseq)

-- Return is always set in the top level scope
-- TODO: We should have a real return slot rather than using a var
getReturn :: State -> Maybe Value
getReturn (State (ScopeState (vals, _, _), _)) = Data.Map.lookup "return" vals

-- Return is always set in the top level scope
-- TODO: We should have a real return slot rather than using a var
vGetReturn :: VState -> Maybe Iota
vGetReturn (VState (VScopeState (iotas, _, _, Nothing), _, _, _)) =
    Data.Map.lookup "return" iotas
vGetReturn _ = error "Not top scope"

-- Return is always set in the top level scope
-- NOTE: If we ever have nested functions that implicitly get their parent's scope,
-- this will need to be updated to indicate on which scope to set the return value
setReturn :: State -> Value -> State
setReturn (State (scope, ctxVals)) val = State (scopeSetReturn scope val, ctxVals)

scopeSetReturn :: ScopeState -> Value -> ScopeState
scopeSetReturn (ScopeState (vals, c, Nothing)) val = ScopeState (insert "return" val vals, c, Nothing)
scopeSetReturn (ScopeState (_, _, Just pScope)) val = scopeSetReturn pScope val

vSetReturn :: VState -> Iota -> [IotaProof] -> VState
vSetReturn (VState (scope, iotaCtx, proofCtx, iotaseq)) niota nproofs =
    VState (vScopeSetReturn scope niota nproofs, iotaCtx, proofCtx, iotaseq)

vScopeSetReturn :: VScopeState -> Iota -> [IotaProof] -> VScopeState
vScopeSetReturn (VScopeState (iotas, proofs, c, Nothing)) niota nproofs =
    VScopeState (insert "return" niota iotas, proofs ++ nproofs, c, Nothing)
vScopeSetReturn (VScopeState (iotas, proofs, c, Just pScope)) niota nproofs =
    VScopeState (iotas, proofs, c, Just $ vScopeSetReturn pScope niota nproofs)

popIotaFromSeq :: VState -> (Iota, VState)
popIotaFromSeq (VState (vScopeState, iotaCtx, proofCtx, iotaseq)) = case iotaseq of
    [] -> error "No more iotas to pop"
    i : is -> (i, VState (vScopeState, iotaCtx, proofCtx, is))

emptyContinuations :: Continuations
emptyContinuations = Continuations []

advanceStatement :: State -> State
advanceStatement (State (scope, ctxVals)) = State (scopeAdvanceStatement scope, ctxVals)

scopeAdvanceStatement :: ScopeState -> ScopeState
scopeAdvanceStatement (ScopeState (vals, Continuations [], _)) = error "No more statements to advance"
scopeAdvanceStatement (ScopeState (vals, Continuations (_ : nxt), pState)) = ScopeState (vals, Continuations nxt, pState)

vAdvanceStatement :: VState -> VState
vAdvanceStatement (VState (scope, iotaCtx, proofCtx, iotaseq)) =
    VState (vScopeAdvanceStatement scope, iotaCtx, proofCtx, iotaseq)

vScopeAdvanceStatement :: VScopeState -> VScopeState
vScopeAdvanceStatement (VScopeState (iotas, proofs, Continuations [], _)) =
    error "No more statements to advance"
vScopeAdvanceStatement (VScopeState (iotas, proofs, Continuations (_ : nxt), pScope)) =
    VScopeState (iotas, proofs, Continuations nxt, pScope)

topLevelScope :: State -> State
topLevelScope (State (scope, ctxVals)) = State (scopeTopLevelScope scope, ctxVals)

scopeTopLevelScope :: ScopeState -> ScopeState
scopeTopLevelScope (ScopeState (vals, c, Nothing)) = ScopeState (vals, c, Nothing)
scopeTopLevelScope (ScopeState (_, _, Just pScope)) = scopeTopLevelScope pScope

vTopLevelScope :: VState -> VState
vTopLevelScope (VState (scope, iotaCtx, proofCtx, iotaseq)) = VState (vScopeTopLevelScope scope, iotaCtx, proofCtx, iotaseq)

vScopeTopLevelScope :: VScopeState -> VScopeState
vScopeTopLevelScope (VScopeState (iotas, proofs, c, Nothing)) = VScopeState (iotas, proofs, c, Nothing)
vScopeTopLevelScope (VScopeState (_, _, _, Just pScope)) = vScopeTopLevelScope pScope

emptyVScopeState :: VScopeState
emptyVScopeState = VScopeState (empty, [], emptyContinuations, Nothing)

-- Infinite sequence of iota names (a0, b0, ..., z0, a1, b1, ...)
iotalist :: [String]
iotalist = [l : show x | x <- [0 :: Integer ..], l <- ['a' .. 'z']]

maybeATermProofToIota :: IotaProof -> Maybe Iota
maybeATermProofToIota (ATerm i) = Just i
maybeATermProofToIota _ = Nothing

-- Find all proofs with the given iota on the LHS
proofLIotaLookup :: [IotaProof] -> Iota -> [IotaProof]
proofLIotaLookup proofs iota = filter (proofLIota iota) proofs

-- Proofs where the LHS is the given iota
-- For FApp, check if the first arg is the given iota
proofLIota :: Iota -> IotaProof -> Bool
proofLIota iota (FApp (Rel Eq) proofs) = case proofs of
    -- TODO: checking first arg only is arbitrary
    ATerm piota : _ -> piota == iota
    _ -> False
proofLIota _ _ = error "Only Eq relation supported"

proofOnlyOfIotasOrConst :: [Iota] -> IotaProof -> Bool
proofOnlyOfIotasOrConst iotas (ATerm i) = i `elem` iotas
proofOnlyOfIotasOrConst _ CTerm{} = True
proofOnlyOfIotasOrConst iotas (FApp _ proofs) = all (proofOnlyOfIotasOrConst iotas) proofs

-- Does the proof use the given relation
proofRel :: Rel -> IotaProof -> Bool
proofRel rel (FApp (Rel prel) _) = prel == rel
proofRel _ _ = False

-- Is the proof concrete
proofConcrete :: IotaProof -> Bool
proofConcrete (FApp (Rel Eq) [ATerm _, CTerm _]) = True
proofConcrete _ = False

proofAbstract :: IotaProof -> Bool
proofAbstract (FApp (Rel Eq) [ATerm _, ATerm _]) = True
proofAbstract _ = False

-- replaceLIotas :: [Proof] -> Iota -> [Proof]
-- replaceLIotas [] _ = []
-- replaceLIotas (A _ rel ptiota : tail) iota =
--     A iota rel ptiota : replaceLIotas tail iota
-- replaceLIotas (C _ rel val : tail) iota =
--     C iota rel val : replaceLIotas tail iota
-- replaceLIotas (FApp _ funct ptiota : tail) iota =
--     FApp iota funct ptiota : replaceLIotas tail iota

-- Given an eqality relation, construct a new proof by replacing
-- instances of the LHS iota (from the equality) with the RHS iota or value
reflProofByProof :: IotaProof -> IotaProof -> Maybe IotaProof
reflProofByProof proof (FApp (Rel Eq) [ATerm iota, ATerm oiota]) = case proof of
    ATerm li
        | li == iota ->
            Just (ATerm oiota)
    FApp (Rel Eq) [ATerm li, CTerm val]
        | li == oiota ->
            Just (FApp (Rel Eq) [ATerm oiota, CTerm val])
    -- TODO: This should apply recursively to the entire proof structure
    FApp (Rel Eq) [ATerm li, rhs] ->
        case reflProofByProof rhs (FApp (Rel Eq) [ATerm iota, ATerm oiota]) of
            Just newRhs -> Just (FApp (Rel Eq) [ATerm li, newRhs])
            _ -> Nothing
    -- TODO: This should apply to all arguments rather than arbitrarily the first
    FApp funct (ATerm fi : rtaili)
        | fi == iota ->
            Just (FApp funct (ATerm oiota : rtaili))
    _ -> Nothing
reflProofByProof proof (FApp (Rel Eq) [ATerm iota, CTerm val]) = case proof of
    -- TODO: This should apply to all arguments rather than arbitrarily the second
    FApp funct [ATerm li, ATerm ri]
        | ri == iota ->
            Just (FApp funct [ATerm li, CTerm val])
    FApp (Rel Eq) [ATerm li, CTerm lval]
        | val == lval && iota /= li ->
            Just (FApp (Rel Eq) [ATerm iota, ATerm li])
    _ -> Nothing
reflProofByProof _ _ = error "Only Eq relation supported"

-- Given an eqality relation, construct new proofs by replacing the
-- LHS iota with the RHS iota or value
reflProofsByProof :: [IotaProof] -> IotaProof -> [IotaProof]
reflProofsByProof (proof : ptail) (FApp (Rel Eq) [ATerm iota, ATerm oiota]) =
    case reflProofByProof proof (FApp (Rel Eq) [ATerm iota, ATerm oiota]) of
        Just newProof -> newProof : reflProofsByProof ptail (FApp (Rel Eq) [ATerm iota, ATerm oiota])
        _ -> reflProofsByProof ptail (FApp (Rel Eq) [ATerm iota, ATerm oiota])
reflProofsByProof (proof : ptail) (FApp (Rel Eq) [ATerm iota, CTerm val]) =
    case reflProofByProof proof (FApp (Rel Eq) [ATerm iota, CTerm val]) of
        Just newProof -> newProof : reflProofsByProof ptail (FApp (Rel Eq) [ATerm iota, CTerm val])
        _ -> reflProofsByProof ptail (FApp (Rel Eq) [ATerm iota, CTerm val])
reflProofsByProof _ _ = []

evalIota :: Iota -> [IotaProof] -> (Map Variable Iota, [IotaProof]) -> [IotaProof]
evalIota iota proofs ctx =
    concatMap (\proof -> evalIotaProofIfForIota iota proof proofs ctx) proofs

evalIotaProofIfForIota :: Iota -> IotaProof -> [IotaProof] -> (Map Variable Iota, [IotaProof]) -> [IotaProof]
evalIotaProofIfForIota iota proof proofs ctx =
    case proof of
        -- TODO: Support other functions
        (FApp (Rel Eq) [ATerm fiota, FApp _ _]) ->
            if fiota == iota
                then evalIotaProof proof proofs ctx
                else []
        _ -> []

-- Given an iota proof and a list of proofs as context,
-- return a list of new proofs
evalIotaProof :: IotaProof -> [IotaProof] -> (Map Variable Iota, [IotaProof]) -> [IotaProof]
evalIotaProof (FApp (Rel Eq) [ATerm iota, FApp funct args]) proofs ctx =
    -- TODO: Make recursive
    case flatMaybeMap maybeATermProofToIota args of
        Just iotas -> case iotasToValues iotas proofs of
            -- TODO: Produce FApp with CTerm
            Just values ->
                let (iotaCtx, proofCtx) = ctx
                 in [FApp (Rel Eq) [ATerm iota, CTerm $ evalFunct funct (iotaMapToConcreteMap iotaCtx proofCtx) values]]
            _ -> []
        _ -> []
evalIotaProof _ _ _ = []

-- Given a list of iotas and a list of proofs,
-- return a list of values or nothing if not all iotas have concrete definitions
iotasToValues :: [Iota] -> [IotaProof] -> Maybe [Value]
iotasToValues [] _ = Just []
iotasToValues (iota : itail) proofs =
    let maybeValue = iotaToValue iota proofs
     in case maybeValue of
            Just value -> case iotasToValues itail proofs of
                Just values -> Just $ value : values
                _ -> Nothing
            _ -> Nothing

-- Given an iota and a list of proofs,
-- return the concrete value of the iota or nothing if not found
iotaToValue :: Iota -> [IotaProof] -> Maybe Value
iotaToValue _ [] = Nothing
iotaToValue iota (proof : ptail) = case proof of
    FApp (Rel Eq) [ATerm piota, CTerm val] | piota == iota -> Just val
    _ -> iotaToValue iota ptail

varProofToIotaProof :: VariableProof -> VState -> IotaProof
varProofToIotaProof (CTerm val) _ = CTerm val
varProofToIotaProof (ATerm var) state =
    let maybeIotaval = vLookupVar state var
     in case maybeIotaval of
            Just iotaval -> ATerm iotaval
            _ -> error "Variable not found in proof map"
varProofToIotaProof (FApp funct args) state =
    let iotaproofs = map (`varProofToIotaProof` state) args
     in FApp funct iotaproofs

-- reflProofsByProofs :: [Proof] -> [Proof] -> [Proof]
-- reflProofsByProofs [] _ = []
-- reflProofsByProofs _ [] = []
-- reflProofsByProofs origProofs (reflByProof : rbpTail) = reflProofsByProof origProofs reflByProof ++ reflProofsByProofs origProofs rbpTail

-- Public fns
evaluate :: [Statement] -> State
evaluate [] = State (ScopeState (empty, emptyContinuations, Nothing), empty)
evaluate l = evalBlock (State (ScopeState (empty, Continuations l, Nothing), empty))

validate :: [Statement] -> Result VState String
validate [] = Ok $ VState (emptyVScopeState, empty, [], [])
validate l = case valBlock (VState (VScopeState (empty, [], Continuations l, Nothing), empty, [], iotalist)) of
    Ok (VState (vScopeState, iotaCtx, proofCtx, remainingIotas)) -> Ok $ VState (vScopeState, iotaCtx, proofCtx, [head remainingIotas])
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

valReturningBlock :: VState -> [Statement] -> Result (VState, Maybe Iota) String
valReturningBlock state stmts =
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
valRewrite state (Refl var) =
    let (VState (VScopeState (iotas, proofs, c, pscope), iotaCtx, proofCtx, iotaseq)) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "Undefined variable: " ++ var
                Just _ ->
                    let newProofs = concatMap (reflProofsByProof proofs) proofs -- TODO: limit to proofs with iota
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
                                ++ [ FApp (Rel Lt) [ATerm iota, ATerm niota]
                                   , FApp (Rel Eq) [ATerm niota, FApp Plus [ATerm iota, ATerm c1iota]]
                                   , FApp (Rel Eq) [ATerm c1iota, CTerm $ VInt 1]
                                   ]
                     in let withEvaledProofs = withNewProofs ++ evalIota niota withNewProofs (iotaCtx, proofCtx)
                         in let withRefledNewProofs =
                                    withEvaledProofs
                                        ++ concatMap (reflProofsByProof withEvaledProofs) withEvaledProofs -- TODO: Maybe limit to new proofs
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
evalExpression sstate (F funct exprs) =
    let (State (scope, valCtx), vals) = evalExpressionList sstate exprs
     in (Just $ evalFunct funct valCtx vals, State (scope, valCtx))

valExpression :: VState -> Iota -> Expression -> Result [IotaProof] String -- produces only the new proofs
valExpression _ iota (Val val) = Ok [FApp (Rel Eq) [ATerm iota, CTerm val]]
-- foldr (\iota _ -> [C iota Eq val]) [] miota
valExpression state iota (Var var) =
    let omiota = vLookupVar state var
     in case omiota of
            Nothing -> Error $ "Undefined variable: " ++ var
            Just oiota -> Ok [FApp (Rel Eq) [ATerm iota, ATerm oiota]]
valExpression (VState (VScopeState (iotas, proofs, c, pscope), iotaCtx, proofCtx, iotaseq)) iota (F funct exprargs) =
    let tiotalist = iotaseq
     in let (fInputProofResults, niotas) =
                zipMap
                    exprargs
                    tiotalist
                    (flip (valExpression $ VState (VScopeState (iotas, proofs, c, pscope), iotaCtx, proofCtx, tiotalist))) -- proofs of input expression in terms of new iotas
                    -- If finputproofs = [A niota rel oi] where oi is already defined, replace with the definition of oi
         in case flatResultMap id fInputProofResults of
                Error e -> Error e
                Ok finputproofs ->
                    let flatfinputproofs = concat finputproofs
                     in let refloncefiproofs =
                                concatMap (reflProofsByProof flatfinputproofs) proofs
                         in let concreteProofs = filter proofConcrete flatfinputproofs -- C niota rel val
                             in let ps = refloncefiproofs ++ concreteProofs
                                 in case valFunct funct (iotaCtx, proofCtx) niotas ps iota of
                                        Ok functProofs ->
                                            Ok
                                                ( concatMap
                                                    ( reflProofsByProof
                                                        [ FApp
                                                            (Rel Eq)
                                                            [ ATerm iota
                                                            , FApp funct (map ATerm niotas)
                                                            ]
                                                        ]
                                                    )
                                                    flatfinputproofs
                                                    ++ functProofs
                                                )
                                        Error e -> Error e
valExpression _ _ e = Error $ "Unsupported expression: " ++ show e

evalFunct :: Funct -> Map Variable Value -> [Value] -> Value
evalFunct Size _ [VIntList l] = VInt (fromIntegral (length l))
evalFunct Size _ _ = error "Size only valid for IntList"
evalFunct First _ [VIntList l] = VInt (head l)
evalFunct First _ _ = error "First only valid for IntList"
evalFunct Last _ [VIntList l] = VInt (last l)
evalFunct Last _ _ = error "Last only valid for IntList"
evalFunct Minus _ [VInt v1, VInt v2] = VInt (v1 - v2)
evalFunct Minus _ _ = error "Plus only valid for two ints"
evalFunct Plus _ [VInt v1, VInt v2] = VInt (v1 + v2)
evalFunct Plus _ _ = error "Plus only valid for two ints"
evalFunct (Rel Eq) _ [VInt v1, VInt v2] = VBool (v1 == v2)
evalFunct (Rel Eq) _ _ = error "Eq only valid for two ints"
evalFunct (Rel Lt) _ [VInt v1, VInt v2] = VBool (v1 < v2)
evalFunct (Rel Lt) _ _ = error "Lt only valid for two ints"
evalFunct (Rel Gt) _ [VInt v1, VInt v2] = VBool (v1 > v2)
evalFunct (Rel Gt) _ _ = error "Rt only valid for two ints"
evalFunct (Rel LtEq) _ [VInt v1, VInt v2] = VBool (v1 <= v2)
evalFunct (Rel LtEq) _ _ = error "LtEq only valid for two ints"
evalFunct (Rel GtEq) _ [VInt v1, VInt v2] = VBool (v1 >= v2)
evalFunct (Rel GtEq) _ _ = error "GtEq only valid for two ints"
evalFunct Call valCtx (VFunct vars _ block _ : args) =
    let (argVals, _) = zipMap vars args (,)
     in -- Give args the function parameter names
        let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
         in let scope = ScopeState (varMap, Continuations block, Just $ ScopeState (empty, emptyContinuations, Nothing))
             in case evalReturningBlock (State (scope, valCtx)) of
                    (_, Just val) -> val
                    _ -> error "Function did not return a value"

concreteValsOfAllMaybe :: [[IotaProof]] -> Maybe [Value]
concreteValsOfAllMaybe [] = Just []
concreteValsOfAllMaybe (ps : pst) = case ps of
    FApp (Rel Eq) [ATerm _, CTerm l] : _ -> case concreteValsOfAllMaybe pst of
        Just vt -> Just (l : vt)
        Nothing -> Nothing
    _ -> Nothing

iotaMapToConcreteMap :: (Ord a) => Map a Iota -> [IotaProof] -> Map a Value
iotaMapToConcreteMap imap proofs =
    Data.Map.fromList $
        mapMaybe ( \(k, i) -> case iotaToValue i proofs of
                Just val -> Just (k, val)
                Nothing -> Nothing
            ) (Data.Map.toList imap)

concreteValOfIotaMaybe :: Iota -> [IotaProof] -> Maybe Value
concreteValOfIotaMaybe iota [] = Nothing
concreteValOfIotaMaybe iota (proof : ptail) = case concreteValOfIotaFromProofMaybe iota proof of
    Just val -> Just val
    Nothing -> concreteValOfIotaMaybe iota ptail

concreteValOfIotaFromProofMaybe :: Iota -> IotaProof -> Maybe Value
concreteValOfIotaFromProofMaybe iota proof = case proof of
    FApp (Rel Eq) [ATerm piota, CTerm val] | piota == iota -> Just val
    _ -> Nothing

-- Takes: Funct, funct input iotas, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunct :: Funct -> (Map Variable Iota, [IotaProof]) -> [Iota] -> [IotaProof] -> Iota -> Result [IotaProof] String
valFunct funct ctx iiotas iproofs retiota =
    let iEqProofs =
            map
                ( \iiota ->
                    filter
                        proofConcrete
                        (filter (proofRel Eq) (filter (proofLIota iiota) iproofs))
                )
                iiotas
     in let vals = concreteValsOfAllMaybe iEqProofs
         in case vals of
                Just vs ->
                    let (iotaCtx, proofCtx) = ctx
                     in Ok [FApp (Rel Eq) [ATerm retiota, CTerm (evalFunct funct (iotaMapToConcreteMap iotaCtx proofCtx) vs)]]
                Nothing ->
                    Error
                        ( "Funct '"
                            ++ show funct
                            ++ "' agrs not validated. Input Iotas: "
                            ++ show iiotas
                            ++ ". Input Proofs: "
                            ++ show iproofs
                        )
