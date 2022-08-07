import           Data.Map                       ( Map
                                                , delete
                                                , empty
                                                , insert
                                                , lookup
                                                )

data Proofs = Prfs [Bool]
    deriving Show
type Iota = String
type Variable = String
data Value = VInt Integer
    deriving Show
data Op = Plus | Minus
data Expression = Val Value | Var Variable | E Expression Op Expression
data Statement = Assign Variable Expression
type State = (Map Variable Value, Map Variable Iota, Proofs)
type VState = (Map Variable Iota, Proofs, [String])

iotalist :: [String]
iotalist = [ l : show x | x <- [0 ..], l <- ['a' .. 'z'] ]

-- Public fns
evaluate :: [Statement] -> State
evaluate [] = (empty, empty, Prfs [])
evaluate l  = evalProgram (empty, empty, Prfs []) l

validate :: [Statement] -> VState
validate [] = (empty, Prfs [], [head iotalist])
validate l  = valProgram (empty, Prfs [], [head iotalist]) l

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
    in  let nproofs = valExpression (iotas, proofs, iotaseq) expr
        in  (insert var niota iotas, proofs, tiotalist)

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

valExpression :: VState -> Expression -> Proofs


evalOp :: Op -> Value -> Value -> Value
evalOp Plus  (VInt i1) (VInt i2) = VInt (i1 + i2)
evalOp Minus (VInt i1) (VInt i2) = VInt (i1 - i2)
