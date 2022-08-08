import           Data.Map                       ( Map
                                                , delete
                                                , empty
                                                , insert
                                                , lookup
                                                )

data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
data Proof = A Iota Rel Iota | C Iota Rel Value deriving Show -- This will need to be made more robust, for now A=abstract, C=concrete
type Iota = String
type Variable = String
data Value = VInt Integer
    deriving Show
data Op = Plus | Minus
data Expression = Val Value | Var Variable | E Expression Op Expression
data Statement = Assign Variable Expression
type State = (Map Variable Value, Map Variable Iota, [Proof])
type VState = (Map Variable Iota, [Proof], [String])

iotalist :: [String]
iotalist = [ l : show x | x <- [0 ..], l <- ['a' .. 'z'] ]

proofLIotaLookup :: [Proof] -> Iota -> [Proof]
proofLIotaLookup proofs iota = filter (proofLIota iota) proofs

proofLIota :: Iota -> Proof -> Bool
proofLIota iota (A piota _ _) = piota == iota
proofLIota iota (C piota _ _) = piota == iota

proofRel :: Rel -> Proof -> Bool
proofRel rel (A _ prel _) = prel == rel
proofRel rel (C _ prel _) = prel == rel

proofConcrete :: Proof -> Bool
proofConcrete C{} = True
proofConcrete _   = False

replaceLIotas :: [Proof] -> Iota -> [Proof]
replaceLIotas [] _ = []
replaceLIotas (A piota rel ptiota : tail) iota =
    A iota rel ptiota : replaceLIotas tail iota
replaceLIotas (C piota rel val : tail) iota =
    C iota rel val : replaceLIotas tail iota

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
                Nothing  -> error "Undefined variable" -- TODO: Validate
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
    in  let proofs1 = valExpression (iotas, proofs, iotaseq) niota1 expr1
        in  let proofs2 = valExpression (iotas, proofs, iotaseq) niota2 expr2
            in  valOp op niota1 proofs1 niota2 proofs2 iota

evalOp :: Op -> Value -> Value -> Value
evalOp Plus  (VInt i1) (VInt i2) = VInt (i1 + i2)
evalOp Minus (VInt i1) (VInt i2) = VInt (i1 - i2)

-- Takes: Op, left arg iota, Proofs of left arg, right arg iota, Proofs of right arg, result iota
-- -- Returns: Proofs for result iota
valOp :: Op -> Iota -> [Proof] -> Iota -> [Proof] -> Iota -> [Proof]
valOp op liota lproofs riota rproofs retiota =
    let lEqProofs = filter (proofRel Eq) (filter (proofLIota liota) lproofs)
    in  let rEqProofs = filter
                proofConcrete
                (filter (proofRel Eq) (filter (proofLIota riota) rproofs))
        in  let opfun = case op of
                    Plus  -> (+)
                    Minus -> (-)
            in  case (lEqProofs, rEqProofs) of
                    (C _ Eq (VInt li) : _, C _ Eq (VInt ri) : _) ->
                        [C retiota Eq (VInt (opfun li ri))]
                    _ -> error "Op not validated"
