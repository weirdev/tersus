import Data.Map

data Proofs = Prfs [Bool] deriving Show
data Iota = I String deriving Show
type Variable = String
data Value = VInt Integer deriving Show
data Op = Plus | Minus
data Expression = V Value | E Expression Op Expression
data Statement = Assign Variable Expression
type State = (Map Variable Value, Map Variable Iota, Proofs)

-- Public fn
evaluate :: [Statement] -> State
evaluate [] = (empty, empty, Prfs [])
evaluate l = evalProgram (evaluate []) l

-- Private fns
evalProgram :: State -> [Statement] -> State
evalProgram state [] = state
evalProgram state (s : tail) = evalProgram (evalStatement state s) tail

evalStatement :: State -> Statement -> State
evalStatement (vals, iotas, proofs) (Assign var expr) = 
    (insert var (evalExpression (vals, iotas, proofs) expr) vals, delete var iotas, proofs)

evalExpression :: State -> Expression -> Value
evalExpression state (V val) = val
evalExpression state (E expr1 op expr2) = evalOp op (evalExpression state expr1) (evalExpression state expr2)

evalOp :: Op -> Value -> Value -> Value
evalOp Plus (VInt i1) (VInt i2) = VInt (i1 + i2)
evalOp Minus (VInt i1) (VInt i2) = VInt (i1 - i2)
