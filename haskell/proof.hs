import           Data.Map                       ( Map
                                                , delete
                                                , empty
                                                , insert
                                                , lookup
                                                )

data Funct = Size | First | Last | Plus | Minus | Rel Rel | Call deriving (Show, Eq)
type Variable = String
data Value = VInt Integer | VIntList [Integer] | VBool Bool -- | VFunct
    deriving (Show, Eq)
data Expression = Val Value | Var Variable | F Funct [Expression] | Block [Statement] deriving Show
data Statement = Assign Variable Expression | Rewrite RwRule | ProofAssert VariableProof | AssignProofVar Variable Expression deriving Show -- Assign ProofVar used only in validations, TODO: maintain separate var map for proof vars
type State = (Map Variable Value, Map Variable Iota, [IotaProof])

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
type Iota = String
-- TODO: Relations should just be FApps
-- TODO: FApps should support complex arguments
data Proof i = A i Rel i | C i Rel Value | FApp2 Funct [Proof i] | ATerm i | CTerm Value deriving (Show, Eq)
type IotaProof = Proof Iota
type VariableProof = Proof Variable
data RwRule = Refl Variable | EqToLtPlus1 Variable | Eval Variable | EvalAll deriving Show -- TODO | LtTrans Variable Variable | GtTrans Variable Variable | LtEqTrans Variable Variable deriving Show
type VState = (Map Variable Iota, [IotaProof], [String])

-- Map elementwise two lists with a function, 
-- returning the result list and the second list trimmed to the length of the first
zipMap :: [a] -> [b] -> (a -> b -> c) -> ([c], [b])
zipMap [] _ _ = ([], [])
zipMap (ah : at) (bh : bt) f =
    let (atr, btr) = zipMap at bt f in (f ah bh : atr, bh : btr)
zipMap (ah : at) [] _ = error "Second list must be at least length of first"

flatMaybeMap :: (a -> Maybe b) -> [a] -> Maybe [b]
flatMaybeMap _ [] = Just []
flatMaybeMap f (ah : at) = case f ah of
    Just b  -> case flatMaybeMap f at of
        Just bt -> Just $ (b : bt)
        _       -> Nothing
    Nothing -> Nothing

unwrapOrThrow :: String -> Maybe a -> a
unwrapOrThrow _ (Just a) = a
unwrapOrThrow err Nothing  = error err

-- Infinite sequence of iota names (a0, b0, ..., z0, a1, b1, ...)
iotalist :: [String]
iotalist = [ l : show x | x <- [0 ..], l <- ['a' .. 'z'] ]

maybeATermProofToIota :: IotaProof -> Maybe Iota
maybeATermProofToIota (ATerm i) = Just i
maybeATermProofToIota _         = Nothing

-- Find all proofs with the given iota on the LHS
proofLIotaLookup :: [IotaProof] -> Iota -> [IotaProof]
proofLIotaLookup proofs iota = filter (proofLIota iota) proofs

-- Proofs where the LHS is the given iota
-- For FApp2, check if the first arg is the given iota
proofLIota :: Iota -> IotaProof -> Bool
proofLIota iota (A    piota _ _) = piota == iota
proofLIota iota (C    piota _ _) = piota == iota
proofLIota iota (FApp2 (Rel Eq) proofs) = case proofs of
    -- TODO: checking first arg only is arbitrary
    (ATerm piota) : _ -> piota == iota
    _                 -> False

-- Does the proof use the given relation
proofRel :: Rel -> IotaProof -> Bool
proofRel rel (A _ prel _) = prel == rel
proofRel rel (C _ prel _) = prel == rel
proofRel rel _       = False

-- Is the proof concrete
proofConcrete :: IotaProof -> Bool
proofConcrete C{} = True
-- TODO: Add CTerm?
proofConcrete _   = False

proofAbstract :: IotaProof -> Bool
proofAbstract A{} = True
-- TODO: Add ATerm?
proofAbstract _   = False

-- replaceLIotas :: [Proof] -> Iota -> [Proof]
-- replaceLIotas [] _ = []
-- replaceLIotas (A _ rel ptiota : tail) iota =
--     A iota rel ptiota : replaceLIotas tail iota
-- replaceLIotas (C _ rel val : tail) iota =
--     C iota rel val : replaceLIotas tail iota
-- replaceLIotas (FApp _ funct ptiota : tail) iota =
--     FApp iota funct ptiota : replaceLIotas tail iota

reflProofByProof :: IotaProof -> IotaProof -> Maybe IotaProof
reflProofByProof proof (A iota Eq oiota) = case proof of
    A li rel ri | li == iota ->
        Just (A oiota rel ri)
    C li rel val | li == iota ->
        Just (C oiota rel val)
    -- TODO: This should apply recursively to the entire proof structure
    FApp2 (Rel Eq) (ATerm li : rhs : []) -> case reflProofByProof rhs (A iota Eq oiota) of
        Just newRhs -> Just (FApp2 (Rel Eq) (ATerm li : newRhs : []))
        _           -> Nothing
    -- TODO: This should apply to all arguments rather than arbitrarily the first
    FApp2 funct (ATerm fi : rtaili) | fi == iota ->
        Just (FApp2 funct (ATerm oiota : rtaili))
    _ -> Nothing
reflProofByProof proof (C iota Eq val) = case proof of
    A li rel ri | ri == iota ->
        Just (C li rel val)
    C li Eq lval | (val == lval) && (iota /= li) ->
        Just (A iota Eq li)
    _ -> Nothing

-- Given an eqality relation, construct new proofs by replacing the
-- LHS iota with the RHS iota or value
reflProofsByProof :: [IotaProof] -> IotaProof -> [IotaProof]
reflProofsByProof (proof : ptail) (A iota Eq oiota) = case reflProofByProof proof (A iota Eq oiota) of
    Just newProof -> newProof : reflProofsByProof ptail (A iota Eq oiota)
    _             -> reflProofsByProof ptail (A iota Eq oiota)
reflProofsByProof (proof : ptail) (C iota Eq val) = case reflProofByProof proof (C iota Eq val) of
    Just newProof -> newProof : reflProofsByProof ptail (C iota Eq val)
    _             -> reflProofsByProof ptail (C iota Eq val)
reflProofsByProof _ _ = []

evalIota :: Iota -> [IotaProof] -> [IotaProof]
evalIota iota proofs =
    concatMap (\proof -> evalIotaProofIfForIota iota proof proofs) proofs

evalIotaProofIfForIota :: Iota -> IotaProof -> [IotaProof] -> [IotaProof]
evalIotaProofIfForIota _ A{} _ = []
evalIotaProofIfForIota _ C{} _ = []
evalIotaProofIfForIota iota proof proofs =
    case proof of
        (FApp2 (Rel Eq) (ATerm fiota : (FApp2 funct args) : [])) -> 
            if fiota == iota
                then evalIotaProof proof proofs
                else []
        _ -> []

-- Given an iota proof and a list of proofs as context,
-- return a list of new proofs
evalIotaProof :: IotaProof -> [IotaProof] -> [IotaProof]
evalIotaProof (FApp2 (Rel Eq) (ATerm iota : (FApp2 funct args) : [])) proofs =
    -- TODO: Make recursive
    case flatMaybeMap maybeATermProofToIota args of
        Just iotas -> case iotasToValues iotas proofs of
            -- TODO: Produce FApp2 with CTerm
            Just values -> [C iota Eq $ evalFunct funct values]
            _          -> []
        _ -> []
evalIotaProof _ _ = []

-- Given a list of iotas and a list of proofs, 
-- return a list of values or nothing if not all iotas have concrete definitions
iotasToValues :: [Iota] -> [IotaProof] -> Maybe [Value]
iotasToValues [] _ = Just []
iotasToValues (iota : tail) proofs =
    let maybeValue = iotaToValue iota proofs
    in  case maybeValue of
            Just value -> case iotasToValues tail proofs of
                Just values -> Just $ value : values
                _           -> Nothing
            _ -> Nothing

-- Given an iota and a list of proofs, 
-- return the concrete value of the iota or nothing if not found
iotaToValue :: Iota -> [IotaProof] -> Maybe Value
iotaToValue iota [] = Nothing
iotaToValue iota (proof : ptail) = case proof of
    C piota Eq val | piota == iota -> Just val
    _ -> iotaToValue iota ptail

varProofToIotaProof :: VariableProof -> Map Variable Iota -> IotaProof
varProofToIotaProof (C var rel val) proofs =
    let maybeIotaval = Data.Map.lookup var proofs
    in  case maybeIotaval of
            Just iotaval -> C iotaval rel val
            _            -> error "Variable not found in proof map"
varProofToIotaProof (A var1 rel var2) proofs =
    let maybeIotaval1 = Data.Map.lookup var1 proofs
        maybeIotaval2 = Data.Map.lookup var2 proofs
    in  case (maybeIotaval1, maybeIotaval2) of
            (Just iotaval1, Just iotaval2) ->
                A iotaval1 rel iotaval2
            _ -> error "Variable not found in proof map"

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
evalStatement (vals, iotas, proofs) (Assign var expr) =
    let (mval, miota, (vals, iotas, proofs)) = evalExpression (vals, iotas, proofs) expr
    in  case (mval, miota) of
        (Just val, Just niota) -> (vals, iotas, proofs) -- (insert var val vals, insert var niota iotas, proofs)
        (Just val, Nothing)    -> (vals, iotas, proofs) -- (insert var val vals, delete var iotas, proofs)
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
    in  let iota = case oiota of
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
        in let withNewProofs = proofs ++ [A iota Lt niota, FApp2 (Rel Eq) [(ATerm niota), FApp2 Plus [(ATerm iota), (ATerm c1iota)]], C c1iota Eq $ VInt 1]
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

evalExpressionList :: State -> [Expression] -> (State, [Value])
evalExpressionList state [] = (state, [])
evalExpressionList state (expr : exprs) =
    let (mval, miota, state) = evalExpression state expr
    in  case mval of
            Just val -> let (state, vals) = evalExpressionList state exprs
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
evalExpression state (F funct exprs) =
    let (state, vals) = evalExpressionList state exprs
    in (Just $ evalFunct funct vals, Nothing, state)
evalExpression state (Block statements) =
    let newState = evalBlock state statements
    in  (Nothing, Nothing, newState)

valExpression :: VState -> Iota -> Expression -> [IotaProof] -- produces only the new proofs
valExpression state iota (Val val) = [C iota Eq val]
    -- foldr (\iota _ -> [C iota Eq val]) [] miota
valExpression (iotas, proofs, _) iota (Var var) =
    let omiota = Data.Map.lookup var iotas
    in  case omiota of
            Nothing    -> error "Undefined variable"
            Just oiota -> [A iota Eq oiota]
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
                                    (reflProofsByProof [FApp2 (Rel Eq) [(ATerm iota), FApp2 funct (map (\i -> ATerm i) niotas)]])
                                    flatfinputproofs
                                ++ valFunct funct niotas ps iota

evalFunct :: Funct -> [Value] -> Value
evalFunct Size  [VIntList l] = VInt (fromIntegral (length l))
evalFunct Size  _            = error "Size only valid for IntList"
evalFunct First [VIntList l] = VInt (fromIntegral (head l))
evalFunct First _            = error "First only valid for IntList"
evalFunct Last  [VIntList l] = VInt (fromIntegral (last l))
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
                                            C _ Eq l : _ -> case concreteValsOfAllMaybe pst of
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
            Just vs -> [C retiota Eq (evalFunct funct vs)]
            Nothing -> error
                (  "Funct '"
                ++ show funct
                ++ "' not validated. Input Iotas: "
                ++ show iiotas
                ++ ". Input Proofs: "
                ++ show iproofs
                )
