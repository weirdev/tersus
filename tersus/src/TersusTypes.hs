module TersusTypes where

import Data.Map (Map)

data Result a e = Ok a | Error e deriving (Eq)

type Variable = String
data Funct = Size | First | Last | Plus | Minus | Rel Rel | Call deriving (Show, Eq)

-- TODO: Generic list type
data Value
    = VInt Integer
    | VIntList [Integer]
    | VBool Bool
    | -- VFunct inputArgs inputArgAssertions body resultAssertions
      -- Result assertions may contain variables from inputArgs and "return" variable
      -- TODO: Real return slot rather than var
      VFunct [Variable] [ValidationStatement] [Statement] [VariableProof]
    deriving (Show, Eq)
data Expression = Val Value | Var Variable | F Funct [Expression]
    deriving (Show, Eq)
data ValidationStatement
    = Rewrite RwRule
    | ProofAssert VariableProof
    | AssignProofVar Variable Expression
    deriving (Show, Eq)
data Statement
    = Assign Variable Expression
    | Return Expression
    | ValidationStatement ValidationStatement
    | Block [Statement]
    | EndBlock
    deriving (Show, Eq) -- Assign ProofVar used only in validations, TODO: maintain separate var map for proof vars

-- nextStmt
-- TODO: Naming is probably wrong here
newtype Continuations = Continuations [Statement]

newtype ScopeState = ScopeState (Map Variable Value, Continuations, Maybe ScopeState)
-- (scope info, file context [aka standard lib + imports])
newtype State = State (ScopeState, Map Variable Value)

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
type Iota = String
data Proof i = FApp Funct [Proof i] | ATerm i | CTerm Value deriving (Show, Eq)
type IotaProof = Proof Iota
type VariableProof = Proof Variable

-- TODO: As with Funct, the rule name should be a separate type from the arguments
data RwRule = Refl Variable | EqToLtPlus1 Variable | Eval Variable | EvalAll
    deriving (Show, Eq) -- TODO | LtTrans Variable Variable | GtTrans Variable Variable | LtEqTrans Variable Variable deriving Show
newtype VScopeState
    = VScopeState
        ( Map Variable Iota
        , [IotaProof]
        , Continuations
        , Maybe VScopeState
        )
newtype VState = VState (VScopeState, Map Variable Iota, [IotaProof], [Iota])