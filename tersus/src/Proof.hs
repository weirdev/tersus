module Proof where

import Data.Map (
    Map,
    delete,
    empty,
    insert,
    lookup,
 )

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

-- flatMaybeMap _ [] = Just []
-- flatMaybeMap f (ah : at) = case f ah of
--     Just b -> case flatMaybeMap f at of
--         Just bt -> Just (b : bt)
--         _ -> Nothing
--     Nothing -> Nothing

unwrapOrThrow :: String -> Maybe a -> a
unwrapOrThrow _ (Just a) = a
unwrapOrThrow err Nothing = error err

-- Lookup the value of a var in State, including parent scopes
lookupVar :: State -> Variable -> Maybe Value
lookupVar (State (vals, _, pState)) var = case Data.Map.lookup var vals of
    Just val -> Just val
    Nothing -> case pState of
        Just p -> lookupVar p var
        Nothing -> Nothing

vLookupVar :: VState -> Variable -> Maybe Iota
vLookupVar (VState (scope, _)) = vScopeLookupVar scope

vScopeLookupVar :: VScopeState -> Variable -> Maybe Iota
vScopeLookupVar (VScopeState (iotas, _, _, pScope)) var =
    case Data.Map.lookup var iotas of
        Just iota -> Just iota
        Nothing -> case pScope of
            Just p -> vScopeLookupVar p var
            Nothing -> Nothing

updateExistingVar :: State -> Variable -> Value -> Maybe State
updateExistingVar (State (vals, c, pState)) var val = case Data.Map.lookup var vals of
    Just _ -> Just (State (insert var val vals, c, pState))
    Nothing -> case pState of
        Just p -> case updateExistingVar p var val of
            Just np -> Just (State (vals, c, Just np))
            Nothing -> Nothing
        Nothing -> Nothing

vUpdateExistingVar :: VState -> Variable -> Iota -> Maybe VState
vUpdateExistingVar (VState (scope, iotaseq)) var iota = case vScopeUpdateExistingVar scope var iota of
    Just ns -> Just $ VState (ns, iotaseq)
    Nothing -> Nothing

vScopeUpdateExistingVar :: VScopeState -> Variable -> Iota -> Maybe VScopeState
vScopeUpdateExistingVar (VScopeState (iotas, proofs, c, pScope)) var iota =
    case Data.Map.lookup var iotas of
        Just _ -> Just $ VScopeState (insert var iota iotas, proofs, c, pScope)
        Nothing -> case pScope of
            Just p -> case vScopeUpdateExistingVar p var iota of
                Just np -> Just $ VScopeState (iotas, proofs, c, Just np)
                Nothing -> Nothing
            Nothing -> Nothing

insertVar :: State -> Variable -> Value -> State
insertVar (State (vals, c, pState)) var val =
    -- Prefentially update existing var in this or parent scope if the variable is already bound.
    -- Otherwise, just insert the new variable in the current scope.
    case updateExistingVar (State (vals, c, pState)) var val of
        Just s -> s
        Nothing -> State (insert var val vals, c, pState)

vInsertVar :: VState -> Variable -> Iota -> VState
vInsertVar (VState (VScopeState (iotas, proofs, c, pScope), iotaseq)) var iota =
    case vUpdateExistingVar (VState (VScopeState (iotas, proofs, c, pScope), iotaseq)) var iota of
        Just s -> s
        Nothing -> VState (VScopeState (insert var iota iotas, proofs, c, pScope), iotaseq)

-- Return is always set in the top level scope
-- TODO: We should have a real return slot rather than using a var
getReturn :: State -> Maybe Value
getReturn (State (vals, _, _)) = Data.Map.lookup "return" vals

-- Return is always set in the top level scope
vGetReturn :: VState -> Maybe Iota
vGetReturn (VState (VScopeState (iotas, _, _, _), _)) = Data.Map.lookup "return" iotas

-- Return is always set in the top level scope
-- NOTE: If we ever have nested functions that implicitly get their parent's scope,
-- this will need to be updated to indicate on which scope to set the return value
setReturn :: State -> Value -> State
setReturn (State (vals, c, Nothing)) val = State (insert "return" val vals, c, Nothing)
setReturn (State (_, _, Just pState)) val = setReturn pState val

vSetReturn :: VState -> Iota -> VState
vSetReturn (VState (scope, iotaseq)) iota =
    VState (vScopeSetReturn scope iota, iotaseq)

vScopeSetReturn :: VScopeState -> Iota -> VScopeState
vScopeSetReturn (VScopeState (iotas, proofs, c, Nothing)) iota =
    VScopeState (insert "return" iota iotas, proofs, c, Nothing)
vScopeSetReturn (VScopeState (iotas, proofs, c, Just pScope)) iota =
    VScopeState (iotas, proofs, c, Just $ vScopeSetReturn pScope iota)

popIotaFromSeq :: VState -> (Iota, VState)
popIotaFromSeq (VState (vScopeState, iotaseq)) = case iotaseq of
    [] -> error "No more iotas to pop"
    i : is -> (i, VState (vScopeState, is))

emptyContinuations :: Continuations
emptyContinuations = Continuations []

advanceStatement :: State -> State
advanceStatement (State (_, Continuations [], _)) = error "No more statements to advance"
advanceStatement (State (vals, Continuations (_ : nxt), pState)) =
    State (vals, Continuations nxt, pState)

topLevelScope :: State -> State
topLevelScope (State (vals, c, Nothing)) = State (vals, c, Nothing)
topLevelScope (State (_, _, Just pState)) = topLevelScope pState

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

evalIota :: Iota -> [IotaProof] -> [IotaProof]
evalIota iota proofs =
    concatMap (\proof -> evalIotaProofIfForIota iota proof proofs) proofs

evalIotaProofIfForIota :: Iota -> IotaProof -> [IotaProof] -> [IotaProof]
evalIotaProofIfForIota iota proof proofs =
    case proof of
        -- TODO: Support other functions
        (FApp (Rel Eq) [ATerm fiota, FApp _ _]) ->
            if fiota == iota
                then evalIotaProof proof proofs
                else []
        _ -> []

-- Given an iota proof and a list of proofs as context,
-- return a list of new proofs
evalIotaProof :: IotaProof -> [IotaProof] -> [IotaProof]
evalIotaProof (FApp (Rel Eq) [ATerm iota, FApp funct args]) proofs =
    -- TODO: Make recursive
    case flatMaybeMap maybeATermProofToIota args of
        Just iotas -> case iotasToValues iotas proofs of
            -- TODO: Produce FApp with CTerm
            Just values -> [FApp (Rel Eq) [ATerm iota, CTerm $ evalFunct funct values]]
            _ -> []
        _ -> []
evalIotaProof _ _ = []

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
varProofToIotaProof (FApp (Rel rel) [ATerm var, CTerm val]) state =
    let maybeIotaval = vLookupVar state var
     in case maybeIotaval of
            Just iotaval -> FApp (Rel rel) [ATerm iotaval, CTerm val]
            _ -> error "Variable not found in proof map"
-- TODO: Support more than two arguments and non Rel functions
varProofToIotaProof (FApp (Rel rel) [ATerm var1, ATerm var2]) state =
    let maybeIotaval1 = vLookupVar state var1
        maybeIotaval2 = vLookupVar state var2
     in case (maybeIotaval1, maybeIotaval2) of
            (Just iotaval1, Just iotaval2) ->
                FApp (Rel rel) [ATerm iotaval1, ATerm iotaval2]
            _ -> error "Variable not found in proof map"
varProofToIotaProof _ _ = error "Only Eq relation supported"

-- reflProofsByProofs :: [Proof] -> [Proof] -> [Proof]
-- reflProofsByProofs [] _ = []
-- reflProofsByProofs _ [] = []
-- reflProofsByProofs origProofs (reflByProof : rbpTail) = reflProofsByProof origProofs reflByProof ++ reflProofsByProofs origProofs rbpTail

-- Public fns
evaluate :: [Statement] -> State
evaluate [] = State (empty, emptyContinuations, Nothing)
evaluate l = evalBlock (State (empty, Continuations l, Nothing))

validate :: [Statement] -> Result VState String
validate [] = Ok $ VState (emptyVScopeState, [])
validate l = case valProgram (VState (emptyVScopeState, iotalist)) l of
    Ok (VState (vScopeState, remainingIotas)) -> Ok $ VState (vScopeState, [head remainingIotas])
    Error e -> Error e

-- Private fns
evalBlock :: State -> State
evalBlock state = case state of
    State (_, Continuations [], _) -> state
    State (_, Continuations (_ : _), _) ->
        let nState = evalNextStatement state
         in evalBlock nState

evalReturningBlock :: State -> (State, Maybe Value)
evalReturningBlock state =
    let rState = evalBlock state
     in (rState, getReturn rState)

valProgram :: VState -> [Statement] -> Result VState String
valProgram state [] = Ok state
valProgram state (stmt : stmts) = case valStatement state stmt of
    Ok nstate -> valProgram nstate stmts
    _ -> Error "Validation failed"

evalNextStatement :: State -> State
evalNextStatement state = case state of
    State (_, Continuations (Assign var expr : _), _) ->
        let (mval, rState) = evalExpression (advanceStatement state) expr
         in case mval of
                Just val -> insertVar rState var val
                -- TODO: Is this an error case?
                Nothing -> rState
    State (_, Continuations (Return expr : _), _) ->
        let (mval, rState) = evalExpression (advanceStatement state) expr
         in -- Break out of the current block and return the value
            let prState = topLevelScope rState
             in case mval of
                    Just val -> setReturn prState val
                    -- TODO: Allow this for functions returning nothing
                    Nothing -> error "Return expression must return a value"
    State (_, Continuations (Rewrite{} : _), _) -> advanceStatement state
    State (_, Continuations (ProofAssert{} : _), _) -> advanceStatement state
    State (_, Continuations (AssignProofVar{} : _), _) -> advanceStatement state
    State (_, Continuations (Block statements : _), _) ->
        evalBlock (State (empty, Continuations (statements ++ [EndBlock]), Just (advanceStatement state)))
    State (_, Continuations (EndBlock : _), pState) ->
        -- Any vars declared in the block are not exported,
        -- but any vars updated in the parent scope must be exported
        case pState of
            Just rpState -> rpState
            _ -> error "EndBlock must have a parent state"

valStatement :: VState -> Statement -> Result VState String
valStatement state (Assign var expr) =
    let (niota, state') = popIotaFromSeq state
     in case valExpression state' niota expr of
            Ok nproofs ->
                let state'' = vInsertVar state' var niota
                 in let (VState (VScopeState (iotas, proofs, c, pscope), iotaseq)) = state''
                     in Ok $ VState (VScopeState (iotas, proofs ++ nproofs, c, pscope), iotaseq)
            Error e -> Error e
valStatement state (Rewrite rwrule) = valRewrite state rwrule
valStatement state (ProofAssert varproof) =
    let (VState (VScopeState (_, proofs, _, _), _)) = state
     in let iotaProof = varProofToIotaProof varproof state
         in if iotaProof `elem` proofs
                then Ok state
                else Error $ "Assertion failed: " ++ show varproof
valStatement state (AssignProofVar var expr) =
    let (niota, state') = popIotaFromSeq state
     in case valExpression state' niota expr of
            Ok nproofs ->
                let state'' = vInsertVar state' var niota
                 in let (VState (VScopeState (iotas, proofs, c, pscope), iotaseq)) = state''
                     in Ok $ VState (VScopeState (iotas, proofs ++ nproofs, c, pscope), iotaseq)
            Error e -> Error e

valRewrite :: VState -> RwRule -> Result VState String
valRewrite state (Refl var) =
    let (VState (VScopeState (iotas, proofs, c, pscope), iotaseq)) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "Undefined variable: " ++ var
                Just _ ->
                    let newProofs = concatMap (reflProofsByProof proofs) proofs -- TODO: limit to proofs with iota
                     in Ok $ VState (VScopeState (iotas, proofs ++ newProofs, c, pscope), iotaseq)
valRewrite state (Eval var) =
    let (VState (VScopeState (iotas, proofs, c, pscope), iotaseq)) = state
     in let oiota = vLookupVar state var
         in case oiota of
                Nothing -> Error $ "Undefined variable: " ++ var
                Just iota -> Ok $ VState (VScopeState (iotas, evalIota iota proofs ++ proofs, c, pscope), iotaseq)
valRewrite (VState (VScopeState (iotas, proofs, c, pscope), iotaseq)) EvalAll =
    let newProofs = concatMap (`evalIotaProof` proofs) proofs
     in Ok $ VState (VScopeState (iotas, proofs ++ newProofs, c, pscope), iotaseq)
valRewrite state (EqToLtPlus1 var) =
    let (VState (VScopeState (iotas, proofs, c, pscope), niota : c1iota : iotaseq)) = state
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
                     in let withEvaledProofs = withNewProofs ++ evalIota niota withNewProofs
                         in let withRefledNewProofs =
                                    withEvaledProofs
                                        ++ concatMap (reflProofsByProof withEvaledProofs) withEvaledProofs -- TODO: Maybe limit to new proofs
                             in Ok $ VState (VScopeState (iotas, withRefledNewProofs, c, pscope), iotaseq)

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
    let (state, vals) = evalExpressionList sstate exprs
     in (Just $ evalFunct funct vals, state)

valExpression :: VState -> Iota -> Expression -> Result [IotaProof] String -- produces only the new proofs
valExpression _ iota (Val val) = Ok [FApp (Rel Eq) [ATerm iota, CTerm val]]
-- foldr (\iota _ -> [C iota Eq val]) [] miota
valExpression state iota (Var var) =
    let omiota = vLookupVar state var
     in case omiota of
            Nothing -> Error $ "Undefined variable: " ++ var
            Just oiota -> Ok [FApp (Rel Eq) [ATerm iota, ATerm oiota]]
valExpression (VState (VScopeState (iotas, proofs, c, pscope), iotaseq)) iota (F funct exprargs) =
    let tiotalist = iotaseq
     in let (fInputProofResults, niotas) =
                zipMap
                    exprargs
                    tiotalist
                    (flip (valExpression $ VState (VScopeState (iotas, proofs, c, pscope), tiotalist))) -- proofs of input expression in terms of new iotas
                    -- If finputproofs = [A niota rel oi] where oi is already defined, replace with the definition of oi
         in case flatResultMap id fInputProofResults of
                Error e -> Error e
                Ok finputproofs ->
                    let flatfinputproofs = concat finputproofs
                     in let refloncefiproofs =
                                concatMap (reflProofsByProof flatfinputproofs) proofs
                         in let concreteProofs = filter proofConcrete flatfinputproofs -- C niota rel val
                             in let ps = refloncefiproofs ++ concreteProofs
                                 in case valFunct funct niotas ps iota of
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

evalFunct :: Funct -> [Value] -> Value
evalFunct Size [VIntList l] = VInt (fromIntegral (length l))
evalFunct Size _ = error "Size only valid for IntList"
evalFunct First [VIntList l] = VInt (head l)
evalFunct First _ = error "First only valid for IntList"
evalFunct Last [VIntList l] = VInt (last l)
evalFunct Last _ = error "Last only valid for IntList"
evalFunct Minus [VInt v1, VInt v2] = VInt (v1 - v2)
evalFunct Minus _ = error "Plus only valid for two ints"
evalFunct Plus [VInt v1, VInt v2] = VInt (v1 + v2)
evalFunct Plus _ = error "Plus only valid for two ints"
evalFunct (Rel Eq) [VInt v1, VInt v2] = VBool (v1 == v2)
evalFunct (Rel Eq) _ = error "Eq only valid for two ints"
evalFunct (Rel Lt) [VInt v1, VInt v2] = VBool (v1 < v2)
evalFunct (Rel Lt) _ = error "Lt only valid for two ints"
evalFunct (Rel Gt) [VInt v1, VInt v2] = VBool (v1 > v2)
evalFunct (Rel Gt) _ = error "Rt only valid for two ints"
evalFunct (Rel LtEq) [VInt v1, VInt v2] = VBool (v1 <= v2)
evalFunct (Rel LtEq) _ = error "LtEq only valid for two ints"
evalFunct (Rel GtEq) [VInt v1, VInt v2] = VBool (v1 >= v2)
evalFunct (Rel GtEq) _ = error "GtEq only valid for two ints"
evalFunct Call (VFunct vars block : args) =
    let (argVals, _) = zipMap vars args (,)
     in -- Give args the function parameter names
        let varMap = foldl (\vm (var, val) -> insert var val vm) empty argVals
         in case evalReturningBlock (State (varMap, Continuations block, Just $ State (empty, emptyContinuations, Nothing))) of
                (_, Just val) -> val
                _ -> error "Function did not return a value"

concreteValsOfAllMaybe :: [[IotaProof]] -> Maybe [Value]
concreteValsOfAllMaybe [] = Just []
concreteValsOfAllMaybe (ps : pst) = case ps of
    FApp (Rel Eq) [ATerm _, CTerm l] : _ -> case concreteValsOfAllMaybe pst of
        Just vt -> Just (l : vt)
        Nothing -> Nothing
    _ -> Nothing

-- Takes: Funct, funct input iotas, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunct :: Funct -> [Iota] -> [IotaProof] -> Iota -> Result [IotaProof] String
valFunct funct iiotas iproofs retiota =
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
                Just vs -> Ok [FApp (Rel Eq) [ATerm retiota, CTerm (evalFunct funct vs)]]
                Nothing ->
                    Error
                        ( "Funct '"
                            ++ show funct
                            ++ "' not validated. Input Iotas: "
                            ++ show iiotas
                            ++ ". Input Proofs: "
                            ++ show iproofs
                        )
