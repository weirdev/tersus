import           Data.Map                       ( Map
                                                , delete
                                                , empty
                                                , insert
                                                , lookup
                                                )

data Funct = Size | First | Last | Plus | Minus | Rel Rel deriving Show
type Variable = String
data Value = VInt Integer | VIntList [Integer] | VBool Bool
    deriving Show
data Expression = Val Value | Var Variable | F Funct [Expression] | ProofAssert VariableProof deriving Show
data Statement = Assign Variable Expression | Rewrite RwRule
type State = (Map Variable Value, Map Variable Iota, [IotaProof])

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
type Iota = String
data Proof i = A i Rel i | C i Rel Value | FApp i Funct [i] deriving Show
type IotaProof = Proof Iota
type VariableProof = Proof Variable
data RwRule = Refl Variable | LtTrans Variable Variable | GtTrans Variable Variable | LtEqTrans Variable Variable deriving Show
type VState = (Map Variable Iota, [IotaProof], [String])

zipMap :: [a] -> [b] -> (a -> b -> c) -> ([c], [b])
zipMap [] _ _ = ([], [])
zipMap (ah : at) (bh : bt) f =
    let (atr, btr) = zipMap at bt f in (f ah bh : atr, bh : btr)
zipMap (ah : at) [] _ = error "Second list must be at least length of first"

iotalist :: [String]
iotalist = [ l : show x | x <- [0 ..], l <- ['a' .. 'z'] ]

proofLIotaLookup :: [IotaProof] -> Iota -> [IotaProof]
proofLIotaLookup proofs iota = filter (proofLIota iota) proofs

proofLIota :: Iota -> IotaProof -> Bool
proofLIota iota (A    piota _ _) = piota == iota
proofLIota iota (C    piota _ _) = piota == iota
proofLIota iota (FApp piota _ _) = piota == iota

proofRel :: Rel -> IotaProof -> Bool
proofRel rel (A _ prel _) = prel == rel
proofRel rel (C _ prel _) = prel == rel
proofRel rel FApp{}       = False

proofConcrete :: IotaProof -> Bool
proofConcrete C{} = True
proofConcrete _   = False

proofAbstract :: IotaProof -> Bool
proofAbstract A{} = True
proofAbstract _   = False

-- replaceLIotas :: [Proof] -> Iota -> [Proof]
-- replaceLIotas [] _ = []
-- replaceLIotas (A _ rel ptiota : tail) iota =
--     A iota rel ptiota : replaceLIotas tail iota
-- replaceLIotas (C _ rel val : tail) iota =
--     C iota rel val : replaceLIotas tail iota
-- replaceLIotas (FApp _ funct ptiota : tail) iota =
--     FApp iota funct ptiota : replaceLIotas tail iota


reflProofsByProof :: [IotaProof] -> IotaProof -> [IotaProof]
reflProofsByProof (proof : ptail) (A iota Eq oiota) = case proof of
    A li rel ri | li == iota ->
        A oiota rel ri : reflProofsByProof ptail (A iota Eq oiota)
    C li rel val | li == iota ->
        C oiota rel val : reflProofsByProof ptail (A iota Eq oiota)
    FApp li funct ri | li == iota ->
        FApp oiota funct ri : reflProofsByProof ptail (A iota Eq oiota)
    FApp li funct (ri : rtaili) | ri == iota ->
        FApp li funct (oiota : rtaili)
            : reflProofsByProof ptail (A iota Eq oiota)
    _ -> reflProofsByProof ptail (A iota Eq oiota)
reflProofsByProof (proof : ptail) (C iota Eq val) = case proof of
    A li rel ri | ri == iota ->
        C li rel val : reflProofsByProof ptail (C iota Eq val)
    _ -> reflProofsByProof ptail (C iota Eq val)
reflProofsByProof _ _ = []

-- reflProofsByProofs :: [Proof] -> [Proof] -> [Proof]
-- reflProofsByProofs [] _ = []
-- reflProofsByProofs _ [] = []
-- reflProofsByProofs origProofs (reflByProof : rbpTail) = reflProofsByProof origProofs reflByProof ++ reflProofsByProofs origProofs rbpTail

-- Public fns
evaluate :: [Statement] -> State
evaluate [] = (empty, empty, [])
evaluate l  = evalProgram (empty, empty, []) l

validate :: [Statement] -> VState
validate [] = (empty, [], [head iotalist])
validate l =
    let (iotas, proofs, remainingIotas) = valProgram (empty, [], iotalist) l
    in  (iotas, proofs, [head remainingIotas])

-- Private fns
evalProgram :: State -> [Statement] -> State
evalProgram = foldl evalStatement

valProgram :: VState -> [Statement] -> VState
valProgram = foldl valStatement

evalStatement :: State -> Statement -> State
evalStatement (vals, iotas, proofs) (Assign var expr) =
    let (val, miota) = evalExpression (vals, iotas, proofs) expr
    in  case miota of
            Just niota -> (insert var val vals, insert var niota iotas, proofs)
            Nothing    -> (insert var val vals, delete var iotas, proofs)
evalStatement state Rewrite{} = state

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
        in  let newProofs = concatMap (reflProofsByProof proofs) proofs
            in  (iotas, proofs ++ newProofs, iotaseq)

evalExpression :: State -> Expression -> (Value, Maybe Iota)
evalExpression state (Val val) = (val, Nothing)
evalExpression (vals, iotas, _) (Var var) =
    let mval = Data.Map.lookup var vals
    in  let miota = Data.Map.lookup var iotas
        in  case mval of
                Just val -> (val, miota)
                Nothing  -> error "Undefined variable"
evalExpression state (F funct exprs) =
    (evalFunct funct (map (fst . evalExpression state) exprs), Nothing)


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
                                    (reflProofsByProof [FApp iota funct niotas])
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
