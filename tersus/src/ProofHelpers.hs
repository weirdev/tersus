module ProofHelpers where

import Data.Map (
    empty,
    insert,
    lookup,
 )

import StdLib
import TersusTypes
import Utils

initState :: State
initState = State (emptyScopeState, stdLibCtx)

initStateWStatements :: [Statement] -> State
initStateWStatements stmts = case initState of
    State (_, ctxVals) -> State (initScopeStateWStatements stmts, ctxVals)

initScopeStateWStatements :: [Statement] -> ScopeState
initScopeStateWStatements stmts = ScopeState (empty, Continuations stmts, Nothing)

initVStateWStatements :: [Statement] -> VState
initVStateWStatements stmts =
    let (iotaCtx, proofCtx) = stdLibValCtx
     in VState (initVScopeStateWStatements stmts, iotaCtx, proofCtx, iotalist)

initVScopeStateWStatements :: [Statement] -> VScopeState
initVScopeStateWStatements stmts = VScopeState (empty, [], Continuations stmts, Nothing)

emptyScopeState :: ScopeState
emptyScopeState = ScopeState (empty, emptyContinuations, Nothing)

setPScope :: State -> Maybe ScopeState -> State
setPScope (State (scope, ctxVals)) p = State (scopeSetPScope scope p, ctxVals)

scopeSetPScope :: ScopeState -> Maybe ScopeState -> ScopeState
scopeSetPScope (ScopeState (vals, c, _)) p = ScopeState (vals, c, p)

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
scopeAdvanceStatement (ScopeState (_, Continuations [], _)) = error "No more statements to advance"
scopeAdvanceStatement (ScopeState (vals, Continuations (_ : nxt), pState)) = ScopeState (vals, Continuations nxt, pState)

vAdvanceStatement :: VState -> VState
vAdvanceStatement (VState (scope, iotaCtx, proofCtx, iotaseq)) =
    VState (vScopeAdvanceStatement scope, iotaCtx, proofCtx, iotaseq)

vScopeAdvanceStatement :: VScopeState -> VScopeState
vScopeAdvanceStatement (VScopeState (_, _, Continuations [], _)) =
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
proofLIota iota (FApp _ args) = case args of
    -- TODO: checking first arg only is arbitrary
    ATerm piota : _ -> piota == iota
    _ -> False

proofOnlyOfIotasOrConst :: [Iota] -> IotaProof -> Bool
proofOnlyOfIotasOrConst iotas (ATerm i) = i `elem` iotas
proofOnlyOfIotasOrConst _ CTerm{} = True
proofOnlyOfIotasOrConst iotas (FApp _ proofs) = all (proofOnlyOfIotasOrConst iotas) proofs

-- Does the proof use the given relation
proofRel :: Rel -> IotaProof -> Bool
proofRel rel (FApp funct _) = funct == CTerm (builtinFunct (Rel rel))
proofRel _ _ = False

-- Is the proof concrete
abstractLhsEqConcreteRhs :: IotaProof -> Bool
abstractLhsEqConcreteRhs (FApp funct [ATerm _, CTerm _]) = funct == CTerm (builtinFunct (Rel Eq))
abstractLhsEqConcreteRhs _ = False

abstractLhsEqAbstractRhs :: IotaProof -> Bool
abstractLhsEqAbstractRhs (FApp funct [ATerm _, ATerm _]) = funct == CTerm (builtinFunct (Rel Eq))
abstractLhsEqAbstractRhs _ = False

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
reflProofByProof proof (FApp funct [ATerm iota, ATerm oiota]) | funct == eqProof =
    case proof of
        ATerm li
            | li == iota ->
                Just (ATerm oiota)
        FApp funct [ATerm li, CTerm val]
            | li == oiota && funct == eqProof ->
                Just (FApp eqProof [ATerm oiota, CTerm val])
        -- TODO: This should apply recursively to the entire proof structure
        FApp funct [ATerm li, rhs] | funct == eqProof ->
            case reflProofByProof rhs (FApp eqProof [ATerm iota, ATerm oiota]) of
                Just newRhs -> Just (FApp eqProof [ATerm li, newRhs])
                _ -> Nothing
        -- TODO: This should apply to all arguments rather than arbitrarily the first
        FApp funct (ATerm fi : rtaili)
            | fi == iota ->
                Just (FApp funct (ATerm oiota : rtaili))
        _ -> Nothing
reflProofByProof proof (FApp funct [ATerm iota, CTerm val]) | funct == eqProof =
    case proof of
        -- TODO: This should apply to all arguments rather than arbitrarily the second
        FApp funct [ATerm li, ATerm ri]
            | ri == iota ->
                Just (FApp funct [ATerm li, CTerm val])
        FApp funct [ATerm li, CTerm lval]
            | val == lval && iota /= li && funct == eqProof ->
                Just (FApp eqProof [ATerm iota, ATerm li])
        _ -> Nothing
reflProofByProof _ _ = error "Only Eq relation supported"

-- Given an eqality relation, construct new proofs by replacing the
-- LHS iota with the RHS iota or value
reflProofsByProof :: [IotaProof] -> IotaProof -> [IotaProof]
reflProofsByProof (proof : ptail) (FApp funct [ATerm iota, ATerm oiota]) | funct == eqProof =
    case reflProofByProof proof (FApp eqProof [ATerm iota, ATerm oiota]) of
        Just newProof -> newProof : reflProofsByProof ptail (FApp eqProof [ATerm iota, ATerm oiota])
        _ -> reflProofsByProof ptail (FApp eqProof [ATerm iota, ATerm oiota])
reflProofsByProof (proof : ptail) (FApp funct [ATerm iota, CTerm val]) | funct == eqProof =
    case reflProofByProof proof (FApp eqProof [ATerm iota, CTerm val]) of
        Just newProof -> newProof : reflProofsByProof ptail (FApp eqProof [ATerm iota, CTerm val])
        _ -> reflProofsByProof ptail (FApp eqProof [ATerm iota, CTerm val])
reflProofsByProof _ _ = []

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
    FApp eqProof [ATerm piota, CTerm val] | piota == iota -> Just val
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
