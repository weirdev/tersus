import           Data.Map                       ( Map
                                                , delete
                                                , empty
                                                , insert
                                                , lookup
                                                )

data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
data Funct = Size | First | Last deriving Show
-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Proof = A Iota Rel Iota | C Iota Rel Value | FApp Iota Funct Iota deriving Show
type Iota = String
type Variable = String
data Value = VInt Integer | VIntList [Integer]
    deriving Show
data Op = Plus | Minus
data Expression = Val Value | Var Variable | E Expression Op Expression | F Funct Expression
data Statement = Assign Variable Expression
type State = (Map Variable Value, Map Variable Iota, [Proof])
type VState = (Map Variable Iota, [Proof], [String])

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

replaceLIotas :: [Proof] -> Iota -> [Proof]
replaceLIotas [] _ = []
replaceLIotas (A _ rel ptiota : tail) iota =
    A iota rel ptiota : replaceLIotas tail iota
replaceLIotas (C _ rel val : tail) iota =
    C iota rel val : replaceLIotas tail iota
replaceLIotas (FApp _ funct ptiota : tail) iota =
    FApp iota funct ptiota : replaceLIotas tail iota

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

valStatement :: VState -> Statement -> VState
valStatement (iotas, proofs, iotaseq) (Assign var expr) =
    let niota : tiotalist = iotaseq
    in  let nproofs = valExpression (iotas, proofs, iotaseq) niota expr
        in  (insert var niota iotas, proofs ++ nproofs, tiotalist)

evalExpression :: State -> Expression -> (Value, Maybe Iota)
evalExpression state (Val val) = (val, Nothing)
evalExpression (vals, iotas, _) (Var var) =
    let mval = Data.Map.lookup var vals
    in  let miota = Data.Map.lookup var iotas
        in  case mval of
                Just val -> (val, miota)
                Nothing  -> error "Undefined variable"
evalExpression state (F funct expr) =
    ((\(v, _) -> evalFunct funct v) (evalExpression state expr), Nothing)
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
            in  valOp op niota1 proofs1 niota2 proofs2 iota
valExpression (iotas, proofs, iotaseq) iota (F funct expr) =
    let niota : tiotalist = iotaseq
    in  let finputproofs = valExpression (iotas, proofs, iotaseq) niota expr
        in  valFunct funct niota finputproofs iota

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

evalFunct :: Funct -> Value -> Value
evalFunct Size  (VIntList l) = VInt (fromIntegral (length l))
evalFunct Size  _            = error "Size only valid for IntList"
evalFunct First (VIntList l) = VInt (fromIntegral (head l))
evalFunct First _            = error "First only valid for IntList"
evalFunct Last  (VIntList l) = VInt (fromIntegral (last l))
evalFunct Last  _            = error "Last only valid for IntList"

-- Takes: Funct, funct input iota, funct input proofs, result iota
-- Returns: Proofs for result iota
-- TODO: Currently only supporting producing concrete proof results
-- (ex. size(iotaA=[5, 4]) = iotaB=2)
-- Later update to produce abstract FApp proofs
-- (ex. size(iotaA) = iotaB)
valFunct :: Funct -> Iota -> [Proof] -> Iota -> [Proof]
valFunct funct iiota iproofs retiota =
    let iEqProofs = filter
            proofConcrete
            (filter (proofRel Eq) (filter (proofLIota iiota) iproofs))
    in  case iEqProofs of
            C _ Eq l : _ -> [C retiota Eq (evalFunct funct l)]
            _            -> error ("Funct not validated: " ++ show iproofs)
