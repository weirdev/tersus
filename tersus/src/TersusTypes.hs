module TersusTypes where

import Data.Map (Map)

type Variable = String
data BuiltinFunct = Size | First | Last | Plus | Minus | Rel Rel deriving (Show, Eq)

data FunctBody = NativeFunct [Statement] | BuiltinFunct BuiltinFunct deriving (Show, Eq)

-- TODO: Generic list type
data Value
    = VInt Integer
    | VIntList [Integer]
    | VBool Bool
    | -- VFunct inputArgs inputArgAssertions body resultAssertions
      -- Result assertions may contain variables from inputArgs and "return" variable
      -- TODO: Real return slot rather than var
      VFunct [Variable] [ValidationStatement] FunctBody [VariableProof]
    deriving (Show, Eq)

-- TODO: Call
data Expression = Val Value | Var Variable | F Expression [Expression]
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
newtype Continuations = Continuations [Statement] deriving (Show)

newtype ScopeState = ScopeState (Map Variable Value, Continuations, Maybe ScopeState)

-- (scope info, file context [aka standard lib + imports])
data State = State ScopeState (Map Variable Value)

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
newtype Iota = Iota String deriving (Eq, Show)

-- Function being applied, arguments
data Proof i = FApp (Proof i) [Proof i] | ATerm i | CTerm Value deriving (Show, Eq)
type IotaProof = Proof Iota
type VariableProof = Proof Variable

-- TODO: As with BuiltinFunct, the rule name should be a separate type from the arguments
data RwRule
    = Refl VariableProof
    | EqToLtPlus1 Variable
    | EqToGtZero Variable
    | Eval Variable
    | EvalAll
    deriving (Show, Eq) -- TODO | LtTrans Variable Variable | GtTrans Variable Variable | LtEqTrans Variable Variable deriving Show
data VScopeState
    = VScopeState
        (Map Variable Iota)
        [IotaProof]
        Continuations
        (Maybe VScopeState)
    deriving (Show)
data VState = VState VScopeState (Map Variable Iota) [IotaProof] [Iota]

instance Show VState where
    show (VState scope iotaCtx proofCtx iotaseq) =
        "VState (" ++ show (scope, iotaCtx, proofCtx) ++ "("