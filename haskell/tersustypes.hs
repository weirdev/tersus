module TersusTypes where

import           Data.Map                       ( Map )

data Funct = Size | First | Last | Plus | Minus | Rel Rel deriving (Show, Eq)
type Variable = String
-- TODO: Generic list type
data Value = VInt Integer | VIntList [Integer] | VBool Bool -- | VFunct
    deriving (Show, Eq)
data Expression = Val Value | Var Variable | F Funct [Expression] | Block [Statement] deriving Show
data Statement = Assign Variable Expression | Rewrite RwRule | ProofAssert VariableProof | AssignProofVar Variable Expression deriving Show -- Assign ProofVar used only in validations, TODO: maintain separate var map for proof vars
type State = (Map Variable Value, Map Variable Iota, [IotaProof])

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | Lt | Gt | LtEq | GtEq deriving (Eq, Show)
type Iota = String
data Proof i = FApp2 Funct [Proof i] | ATerm i | CTerm Value deriving (Show, Eq)
type IotaProof = Proof Iota
type VariableProof = Proof Variable
data RwRule = Refl Variable | EqToLtPlus1 Variable | Eval Variable | EvalAll deriving Show -- TODO | LtTrans Variable Variable | GtTrans Variable Variable | LtEqTrans Variable Variable deriving Show
type VState = (Map Variable Iota, [IotaProof], [String])