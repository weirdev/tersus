import           Data.Map                       ( Map
                                                , delete
                                                , empty
                                                , insert
                                                , lookup
                                                )

data Funct = Size | First | Last deriving Show
type Variable = String
data Value = VInt Integer | VIntList [Integer]
    deriving Show
data Op = Plus | Minus
data Expression = Val Value | Var Variable | E Expression Op Expression | F Funct [Expression]
data Statement = Assign Variable Expression | Rewrite RwRule
type State = (Map Variable Value, Map Variable Iota, [Proof])

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
type Iota = String
data Proof = A Iota Rel Iota | C Iota Rel Value | FApp Iota Funct [Iota] deriving Show
data RwRule = Refl Variable
type VState = (Map Variable Iota, [Proof], [String])

zipMap :: [a] -> [b] -> (a -> b -> c) -> ([c], [b])
zipMap [] _ _ = ([], [])
zipMap (ah : at) (bh : bt) f =
    let (atr, btr) = zipMap at bt f in (f ah bh : atr, bh : btr)
zipMap (ah : at) [] _ = error "Second list must be at least length of first"

iotalist :: [String]
iotalist = [ l : show x | x <- [0 ..], l <- ['a' .. 'z'] ]

proofLIotaLookup :: [Proof] -> Iota -> [Proof]
proofLIotaLookup proofs iota = filter (proofLIota iota) proofs

proofLIota :: Iota -> Proof -> Bool
proofLIota iota (A    piota _ _) = piota == iota
proofLIota iota (C    piota _ _) = piota == iota
proofLIota iota (FApp piota _ _) = piota == iota

proofRel :: Rel -> Proof -> Bool
proofRel rel (A _ prel _) = prel == rel
proofRel rel (C _ prel _) = prel == rel
proofRel rel FApp{}       = False

proofConcrete :: Proof -> Bool
proofConcrete C{} = True
proofConcrete _   = False

proofAbstract :: Proof -> Bool
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


reflProofsByProof :: [Proof] -> Proof -> [Proof]
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
evalExpression state (E expr1 op expr2) =
    let (val1, _) = evalExpression state expr1
    in  let (val2, _) = evalExpression state expr2
        in  (evalOp op val1 val2, Nothing)


valExpression :: VState -> Iota -> Expression -> [Proof] -- produces only the new proofs
valExpression state iota (Val val) = [C iota Eq val]
    -- foldr (\iota _ -> [C iota Eq val]) [] miota
valExpression (iotas, proofs, _) iota (Var var) =
    let omiota = Data.Map.lookup var iotas
    in  case omiota of
            Nothing    -> error "Undefined variable"
            Just oiota -> [A iota Eq oiota]
valExpression (iotas, proofs, iotaseq) iota (E expr1 op expr2) =
    let niota1 : niota2 : tiotalist = iotaseq
    in  let proofs1 = valExpression (iotas, proofs, tiotalist) niota1 expr1
        in  let proofs2 = valExpression (iotas, proofs, tiotalist) niota2 expr2
            in  valOp op
                      niota1
                      (proofs ++ proofs1)
                      niota2
                      (proofs ++ proofs2)
                      iota
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

evalOp :: Op -> Value -> Value -> Value
evalOp Plus (VInt i1) (VInt i2) = VInt (i1 + i2)
evalOp Plus _ _ = error "Only ints are valid arguments to + operator"
evalOp Minus (VInt i1) (VInt i2) = VInt (i1 - i2)
evalOp Minus _ _ = error "Only ints are valid arguments to - operator"

-- Takes: Op, left arg iota, Proofs of left arg, right arg iota, Proofs of right arg, result iota
-- Returns: Proofs for result iota
-- TODO: See README. Replace with functions and proof engine.
-- Currently only handling proving with concrete values (ex. iotaA=5 + iotaB=4 = iotaC=9)
-- Later updates will produce proofs of abstract values (ex. iotaA + iotaB = iotaC)
valOp :: Op -> Iota -> [Proof] -> Iota -> [Proof] -> Iota -> [Proof]
valOp op liota lproofs riota rproofs retiota =
    let lEqProofs = filter
            proofConcrete
            (filter (proofRel Eq) (filter (proofLIota liota) lproofs))
    in  let rEqProofs = filter
                proofConcrete
                (filter (proofRel Eq) (filter (proofLIota riota) rproofs))
        in  case (lEqProofs, rEqProofs) of
                (C _ Eq li : _, C _ Eq ri : _) ->
                    [C retiota Eq (evalOp op li ri)]
                _ -> error "Op not validated"

evalFunct :: Funct -> [Value] -> Value
evalFunct Size  [VIntList l] = VInt (fromIntegral (length l))
evalFunct Size  _            = error "Size only valid for IntList"
evalFunct First [VIntList l] = VInt (fromIntegral (head l))
evalFunct First _            = error "First only valid for IntList"
evalFunct Last  [VIntList l] = VInt (fromIntegral (last l))
evalFunct Last  _            = error "Last only valid for IntList"

-- Takes: Funct, funct input iotas, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunct :: Funct -> [Iota] -> [Proof] -> Iota -> [Proof]
valFunct funct [iiota] iproofs retiota =
    let iEqProofs = filter
            proofConcrete
            (filter (proofRel Eq) (filter (proofLIota iiota) iproofs))
    in  case iEqProofs of
            C _ Eq l : _ -> [C retiota Eq (evalFunct funct [l])]
            _            -> error
                (  "Funct '"
                ++ show funct
                ++ "' not validated. InputIota: "
                ++ show iiota
                ++ ". Input Proofs: "
                ++ show iproofs
                )
valFunct _ _ _ _ = error "Only single argument functions currently supported"
