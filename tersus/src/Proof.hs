module Proof where

import           Data.Map                       ( Map
                                                , empty
                                                , insert
                                                , lookup
                                                )

import          TersusTypes

-- Map elementwise two lists with a function, 
-- returning the result list and the second list trimmed to the length of the first
zipMap :: [a] -> [b] -> (a -> b -> c) -> ([c], [b])
zipMap [] _ _ = ([], [])
zipMap (ah : at) (bh : bt) f =
    let (atr, btr) = zipMap at bt f in (f ah bh : atr, bh : btr)
zipMap (_ : _) [] _ = error "Second list must be at least length of first"

flatMaybeMap :: (a -> Maybe b) -> [a] -> Maybe [b]
flatMaybeMap _ [] = Just []
flatMaybeMap f (ah : at) = case f ah of
    Just b  -> case flatMaybeMap f at of
        Just bt -> Just (b : bt)
        _       -> Nothing
    Nothing -> Nothing

unwrapOrThrow :: String -> Maybe a -> a
unwrapOrThrow _ (Just a) = a
unwrapOrThrow err Nothing  = error err

-- Infinite sequence of iota names (a0, b0, ..., z0, a1, b1, ...)
iotalist :: [String]
iotalist = [ l : show x | x <- [0 :: Integer ..], l <- ['a' .. 'z'] ]

maybeATermProofToIota :: IotaProof -> Maybe Iota
maybeATermProofToIota (ATerm i) = Just i
maybeATermProofToIota _         = Nothing

-- Find all proofs with the given iota on the LHS
proofLIotaLookup :: [IotaProof] -> Iota -> [IotaProof]
proofLIotaLookup proofs iota = filter (proofLIota iota) proofs

-- Proofs where the LHS is the given iota
-- For FApp2, check if the first arg is the given iota
proofLIota :: Iota -> IotaProof -> Bool
proofLIota iota (FApp2 (Rel Eq) proofs) = case proofs of
    -- TODO: checking first arg only is arbitrary
    ATerm piota : _ -> piota == iota
    _                 -> False
proofLIota _ _ = error "Only Eq relation supported"

-- Does the proof use the given relation
proofRel :: Rel -> IotaProof -> Bool
proofRel rel (FApp2 (Rel prel) _) = prel == rel
proofRel _ _       = False

-- Is the proof concrete
proofConcrete :: IotaProof -> Bool
proofConcrete (FApp2 (Rel Eq) [ATerm _, CTerm _]) = True
proofConcrete _   = False

proofAbstract :: IotaProof -> Bool
proofAbstract (FApp2 (Rel Eq) [ATerm _, ATerm _]) = True
proofAbstract _   = False

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
reflProofByProof proof (FApp2 (Rel Eq) [ATerm iota, ATerm oiota]) = case proof of
    ATerm li | li == iota ->
        Just (ATerm oiota)
    FApp2 (Rel Eq) [ATerm li, CTerm val] | li == oiota ->
        Just (FApp2 (Rel Eq) [ATerm oiota, CTerm val])
    -- TODO: This should apply recursively to the entire proof structure
    FApp2 (Rel Eq) [ATerm li, rhs] -> case reflProofByProof rhs (FApp2 (Rel Eq) [ATerm iota, ATerm oiota]) of
        Just newRhs -> Just (FApp2 (Rel Eq) [ATerm li, newRhs])
        _           -> Nothing
    -- TODO: This should apply to all arguments rather than arbitrarily the first
    FApp2 funct (ATerm fi : rtaili) | fi == iota ->
        Just (FApp2 funct (ATerm oiota : rtaili))
    _ -> Nothing
reflProofByProof proof (FApp2 (Rel Eq) [ATerm iota, CTerm val]) = case proof of
    -- TODO: This should apply to all arguments rather than arbitrarily the second
    FApp2 funct [ATerm li, ATerm ri] | ri == iota ->
        Just (FApp2 funct [ATerm li, CTerm val])
    FApp2 (Rel Eq) [ATerm li, CTerm lval] | val == lval && iota /= li ->
        Just (FApp2 (Rel Eq) [ATerm iota, ATerm li])
    _ -> Nothing
reflProofByProof _ _ = error "Only Eq relation supported"

-- Given an eqality relation, construct new proofs by replacing the
-- LHS iota with the RHS iota or value
reflProofsByProof :: [IotaProof] -> IotaProof -> [IotaProof]
reflProofsByProof (proof : ptail) (FApp2 (Rel Eq) [ATerm iota, ATerm oiota]) = case reflProofByProof proof (FApp2 (Rel Eq) [ATerm iota, ATerm oiota]) of
    Just newProof -> newProof : reflProofsByProof ptail (FApp2 (Rel Eq) [ATerm iota, ATerm oiota])
    _             -> reflProofsByProof ptail (FApp2 (Rel Eq) [ATerm iota, ATerm oiota])
reflProofsByProof (proof : ptail) (FApp2 (Rel Eq) [ATerm iota, CTerm val]) = case reflProofByProof proof (FApp2 (Rel Eq) [ATerm iota, CTerm val]) of
    Just newProof -> newProof : reflProofsByProof ptail (FApp2 (Rel Eq) [ATerm iota, CTerm val])
    _             -> reflProofsByProof ptail (FApp2 (Rel Eq) [ATerm iota, CTerm val])
reflProofsByProof _ _ = []

evalIota :: Iota -> [IotaProof] -> [IotaProof]
evalIota iota proofs =
    concatMap (\proof -> evalIotaProofIfForIota iota proof proofs) proofs

evalIotaProofIfForIota :: Iota -> IotaProof -> [IotaProof] -> [IotaProof]
evalIotaProofIfForIota iota proof proofs =
    case proof of
        -- TODO: Support other functions
        (FApp2 (Rel Eq) [ATerm fiota, FApp2 _ _]) ->
            if fiota == iota
                then evalIotaProof proof proofs
                else []
        _ -> []

-- Given an iota proof and a list of proofs as context,
-- return a list of new proofs
evalIotaProof :: IotaProof -> [IotaProof] -> [IotaProof]
evalIotaProof (FApp2 (Rel Eq) [ATerm iota, FApp2 funct args]) proofs =
    -- TODO: Make recursive
    case flatMaybeMap maybeATermProofToIota args of
        Just iotas -> case iotasToValues iotas proofs of
            -- TODO: Produce FApp2 with CTerm
            Just values -> [FApp2 (Rel Eq) [ATerm iota, CTerm $ evalFunct funct values]]
            _          -> []
        _ -> []
evalIotaProof _ _ = []

-- Given a list of iotas and a list of proofs, 
-- return a list of values or nothing if not all iotas have concrete definitions
iotasToValues :: [Iota] -> [IotaProof] -> Maybe [Value]
iotasToValues [] _ = Just []
iotasToValues (iota : itail) proofs =
    let maybeValue = iotaToValue iota proofs
    in  case maybeValue of
            Just value -> case iotasToValues itail proofs of
                Just values -> Just $ value : values
                _           -> Nothing
            _ -> Nothing

-- Given an iota and a list of proofs, 
-- return the concrete value of the iota or nothing if not found
iotaToValue :: Iota -> [IotaProof] -> Maybe Value
iotaToValue _ [] = Nothing
iotaToValue iota (proof : ptail) = case proof of
    FApp2 (Rel Eq) [ATerm piota, CTerm val] | piota == iota -> Just val
    _ -> iotaToValue iota ptail

varProofToIotaProof :: VariableProof -> Map Variable Iota -> IotaProof
varProofToIotaProof (FApp2 (Rel rel) [ATerm var, CTerm val]) proofs =
    let maybeIotaval = Data.Map.lookup var proofs
    in  case maybeIotaval of
            Just iotaval -> FApp2 (Rel rel) [ATerm iotaval, CTerm val]
            _            -> error "Variable not found in proof map"
-- TODO: Support more than two arguments and non Rel functions
varProofToIotaProof (FApp2 (Rel rel) [ATerm var1, ATerm var2]) proofs =
    let maybeIotaval1 = Data.Map.lookup var1 proofs
        maybeIotaval2 = Data.Map.lookup var2 proofs
    in  case (maybeIotaval1, maybeIotaval2) of
            (Just iotaval1, Just iotaval2) ->
                FApp2 (Rel rel) [ATerm iotaval1, ATerm iotaval2]
            _ -> error "Variable not found in proof map"
varProofToIotaProof _ _ = error "Only Eq relation supported"

-- reflProofsByProofs :: [Proof] -> [Proof] -> [Proof]
-- reflProofsByProofs [] _ = []
-- reflProofsByProofs _ [] = []
-- reflProofsByProofs origProofs (reflByProof : rbpTail) = reflProofsByProof origProofs reflByProof ++ reflProofsByProofs origProofs rbpTail

-- Public fns
evaluate :: [Statement] -> State
evaluate [] = (empty, empty, [])
evaluate l  = evalBlock (empty, empty, []) l

validate :: [Statement] -> VState
validate [] = (empty, [], [head iotalist])
validate l =
    let (iotas, proofs, remainingIotas) = valProgram (empty, [], iotalist) l
    in  (iotas, proofs, [head remainingIotas])

-- Private fns
evalBlock :: State -> [Statement] -> State
evalBlock = foldl evalStatement

valProgram :: VState -> [Statement] -> VState
valProgram = foldl valStatement

evalStatement :: State -> Statement -> State
evalStatement (svals, siotas, sproofs) (Assign _var expr) =
    let (mval, miota, (vals, iotas, proofs)) = evalExpression (svals, siotas, sproofs) expr
    in  case (mval, miota) of
        (Just _, Just _niota) -> (vals, iotas, proofs) -- (insert var val vals, insert var niota iotas, proofs)
        (Just _val, Nothing)    -> (vals, iotas, proofs) -- (insert var val vals, delete var iotas, proofs)
        (Nothing, _) -> (vals, iotas, proofs)
evalStatement state Rewrite{} = state
evalStatement state ProofAssert{} = state
evalStatement state AssignProofVar{} = state

valStatement :: VState -> Statement -> VState
valStatement (iotas, proofs, iotaseq) (Assign var expr) =
    let niota : tiotalist = iotaseq
    in  let nproofs = valExpression (iotas, proofs, tiotalist) niota expr
        in  (insert var niota iotas, proofs ++ nproofs, tiotalist)
valStatement (iotas, proofs, iotaseq) (Rewrite (Refl var)) =
    let oiota = Data.Map.lookup var iotas
    in  let _ = case oiota of
                Nothing -> error "Undefined variable"
                Just i  -> i
        in  let newProofs = concatMap (reflProofsByProof proofs) proofs -- TODO: limit to proofs with iota
            in  (iotas, proofs ++ newProofs, iotaseq)
valStatement (iotas, proofs, iotaseq) (Rewrite (Eval var)) =
    let oiota = Data.Map.lookup var iotas
    in  let iota = case oiota of
                Nothing -> error "Undefined variable"
                Just i  -> i
        in  (iotas, evalIota iota proofs ++ proofs, iotaseq)
valStatement (iotas, proofs, iotaseq) (Rewrite EvalAll) =
    let newProofs = concatMap (`evalIotaProof` proofs) proofs
    in  (iotas, proofs ++ newProofs, iotaseq)
valStatement (iotas, proofs, niota : c1iota : iotaseq) (Rewrite (EqToLtPlus1 var)) =
    let oiota = Data.Map.lookup var iotas
    in  let iota = case oiota of
                Nothing -> error "Undefined variable"
                Just i  -> i
        in let withNewProofs = proofs ++ [FApp2 (Rel Lt) [ATerm iota, ATerm niota], FApp2 (Rel Eq) [ATerm niota, FApp2 Plus [ATerm iota, ATerm c1iota]], FApp2 (Rel Eq) [ATerm c1iota, CTerm $ VInt 1]]
            in let withEvaledProofs = withNewProofs ++ evalIota niota withNewProofs
                in let withRefledNewProofs = withEvaledProofs ++ concatMap (reflProofsByProof withEvaledProofs) withEvaledProofs -- TODO: Maybe limit to new proofs
                    in (iotas, withRefledNewProofs, iotaseq)
valStatement (iotas, proofs, iotaseq) (ProofAssert varproof) =
    let iotaProof = varProofToIotaProof varproof iotas
    in  (if iotaProof `elem` proofs then (iotas, proofs, iotaseq) else error "Assertion failed")
valStatement (iotas, proofs, iotaseq) (AssignProofVar var expr) =
    let niota : tiotalist = iotaseq
    in  let nproofs = valExpression (iotas, proofs, tiotalist) niota expr
        in  (insert var niota iotas, proofs ++ nproofs, tiotalist)
valStatement (iotas, proofs, iotaseq) _ = (iotas, proofs, iotaseq)

evalExpressionList :: State -> [Expression] -> (State, [Value])
evalExpressionList state [] = (state, [])
evalExpressionList sstate (expr : exprs) =
    let (mval, _, estate) = evalExpression sstate expr
    in  case mval of
            Just val -> let (state, vals) = evalExpressionList estate exprs
                        in  (state, val : vals)
            Nothing -> error "Expression must return a value to be passed to a function"

evalExpression :: State -> Expression -> (Maybe Value, Maybe Iota, State)
evalExpression state (Val val) = (Just val, Nothing, state)
evalExpression state (Var var) =
    let (vals, iotas, _) = state
    in let mval = Data.Map.lookup var vals
        in  let miota = Data.Map.lookup var iotas
            in  case mval of
                    Just _ -> (mval, miota, state)
                    Nothing  -> error "Undefined variable"
evalExpression sstate (F funct exprs) =
    let (state, vals) = evalExpressionList sstate exprs
    in (Just $ evalFunct funct vals, Nothing, state)
evalExpression state (Block statements) =
    let newState = evalBlock state statements
    in  (Nothing, Nothing, newState)

valExpression :: VState -> Iota -> Expression -> [IotaProof] -- produces only the new proofs
valExpression _ iota (Val val) = [FApp2 (Rel Eq) [ATerm iota, CTerm val]]
    -- foldr (\iota _ -> [C iota Eq val]) [] miota
valExpression (iotas, _, _) iota (Var var) =
    let omiota = Data.Map.lookup var iotas
    in  case omiota of
            Nothing    -> error "Undefined variable"
            Just oiota -> [FApp2 (Rel Eq) [ATerm iota, ATerm oiota]]
valExpression (iotas, proofs, iotaseq) iota (F funct exprargs) =
    let tiotalist = iotaseq
    in
        let (finputproofs, niotas) = zipMap
                exprargs
                tiotalist
                (flip (valExpression (iotas, proofs, tiotalist)))  -- proofs of input expression in terms of new iotas
    -- If finputproofs = [A niota rel oi] where oi is already defined, replace with the definition of oi
        in
            let flatfinputproofs = concat finputproofs
            in
                let refloncefiproofs =
                        concatMap (reflProofsByProof flatfinputproofs) proofs
                in
                    let concreteProofs = filter proofConcrete flatfinputproofs -- C niota rel val
                    in
                        let ps = refloncefiproofs ++ concreteProofs
                        in  concatMap
                                    (reflProofsByProof [FApp2 (Rel Eq) [ATerm iota, FApp2 funct (map ATerm niotas)]])
                                    flatfinputproofs
                                ++ valFunct funct niotas ps iota
valExpression _ _ _ = error "Unsupported expression"

evalFunct :: Funct -> [Value] -> Value
evalFunct Size  [VIntList l] = VInt (fromIntegral (length l))
evalFunct Size  _            = error "Size only valid for IntList"
evalFunct First [VIntList l] = VInt (head l)
evalFunct First _            = error "First only valid for IntList"
evalFunct Last  [VIntList l] = VInt (last l)
evalFunct Last  _            = error "Last only valid for IntList"
evalFunct Minus [VInt v1, VInt v2] = VInt (v1 - v2)
evalFunct Minus  _            = error "Plus only valid for two ints"
evalFunct Plus [VInt v1, VInt v2] = VInt (v1 + v2)
evalFunct Plus  _            = error "Plus only valid for two ints"
evalFunct (Rel Eq) [VInt v1, VInt v2] = VBool (v1 == v2)
evalFunct (Rel Eq) _                  = error "Eq only valid for two ints"
evalFunct (Rel Lt) [VInt v1, VInt v2] = VBool (v1 < v2)
evalFunct (Rel Lt) _                  = error "Lt only valid for two ints"
evalFunct (Rel Gt) [VInt v1, VInt v2] = VBool (v1 > v2)
evalFunct (Rel Gt) _                  = error "Rt only valid for two ints"
evalFunct (Rel LtEq) [VInt v1, VInt v2] = VBool (v1 <= v2)
evalFunct (Rel LtEq) _                  = error "LtEq only valid for two ints"
evalFunct (Rel GtEq) [VInt v1, VInt v2] = VBool (v1 >= v2)
evalFunct (Rel GtEq) _                  = error "GtEq only valid for two ints"

concreteValsOfAllMaybe :: [[IotaProof]] -> Maybe [Value]
concreteValsOfAllMaybe [] = Just []
concreteValsOfAllMaybe (ps : pst) = case ps of
                                            FApp2 (Rel Eq) [ATerm _, CTerm l] : _ -> case concreteValsOfAllMaybe pst of
                                                Just vt -> Just (l : vt)
                                                Nothing -> Nothing
                                            _            -> Nothing

-- Takes: Funct, funct input iotas, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunct :: Funct -> [Iota] -> [IotaProof] -> Iota -> [IotaProof]
valFunct funct iiotas iproofs retiota =
    let iEqProofs = map (\iiota -> filter
            proofConcrete
            (filter (proofRel Eq) (filter (proofLIota iiota) iproofs))) iiotas
    in let vals = concreteValsOfAllMaybe iEqProofs in
        case vals of
            Just vs -> [FApp2 (Rel Eq) [ATerm retiota, CTerm (evalFunct funct vs)]]
            Nothing -> error
                (  "Funct '"
                ++ show funct
                ++ "' not validated. Input Iotas: "
                ++ show iiotas
                ++ ". Input Proofs: "
                ++ show iproofs
                )
