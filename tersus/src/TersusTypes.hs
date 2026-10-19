module TersusTypes where

import Data.Map (Map)

type Variable = String
type Name = String

-- Ctor builds a struct from its fields, given in declaration order, and Field reads one by name.
-- A struct literal is the application of its Ctor, so the proof engine sees structs as ordinary terms.
data BuiltinFunct
    = Size | First | Last | Get | Push | Set | Plus | Minus | Times | Div
    | Rel Rel
    | Ctor Name [Variable]
    | Field Variable
    deriving (Show, Eq, Ord)

-- The types the checker (TypeCheck) knows. They are erased after checking: validation and evaluation never
-- look at them. TVar is the checker's own unknown and is never written by a program.
data Type = TInt | TBool | TList Type | TFn [Type] Type | TNamed Name | TVar Int
    deriving (Show, Eq, Ord)

-- The declared parameter types and return type of a user function
data Signature = Signature [Type] Type deriving (Show, Eq, Ord)

data FunctBody = NativeFunct Signature [Statement] | BuiltinFunct BuiltinFunct deriving (Show, Eq, Ord)

data Value
    = VInt Integer
    | VList [Value]
    | VBool Bool
    | -- A struct value: the struct's name and its fields, in declaration order
      VData Name [(Variable, Value)]
    | -- VFunct inputArgs inputArgAssertions outputAssertions body exportedResultAssertions
      -- Result assertions may contain variables from inputArgs and "return" variable
      -- TODO: Real return slot rather than var
      VFunct [Variable] [ValidationStatement] [ValidationStatement] FunctBody [VariableProof]
    deriving (Show)

-- A builtin is fully described by which builtin it is: its contracts come from the standard library
-- and are large, and values are compared constantly by the proof engine.
instance Eq Value where
    a == b = compare a b == EQ

instance Ord Value where
    compare (VInt a) (VInt b) = compare a b
    compare (VList a) (VList b) = compare a b
    compare (VBool a) (VBool b) = compare a b
    compare (VData n a) (VData m b) = compare (n, a) (m, b)
    compare (VFunct _ _ _ (BuiltinFunct a) _) (VFunct _ _ _ (BuiltinFunct b) _) = compare a b
    compare (VFunct a b c d e) (VFunct a' b' c' d' e') = compare (a, b, c, d, e) (a', b', c', d', e')
    compare a b = compare (rank a) (rank b)
      where
        rank :: Value -> Int
        rank VInt{} = 0
        rank VList{} = 1
        rank VBool{} = 2
        rank VData{} = 3
        rank VFunct{} = 4

-- TODO: Call
data Expression = Val Value | Var Variable | F Expression [Expression]
    deriving (Show, Eq, Ord)
data ValidationStatement
    = Rewrite RwRule
    | ProofAssert VariableProof
    | AssignProofVar Variable Expression
    deriving (Show, Eq, Ord)
data Statement
    = Assign Variable Expression
    | Return Expression
    | ValidationStatement ValidationStatement
    | -- struct Name { field: Type, ... }; it only matters to the type checker
      StructDef Name [(Variable, Type)]
    | AxiomDef Variable [Variable] [ValidationStatement] [ValidationStatement]
    | ProofDef Variable [Variable] [ValidationStatement] [ValidationStatement] [ValidationStatement]
    | Block [Statement]
    | -- If condition thenBranch elseBranch; a missing else is an empty branch
      If Expression [Statement] [Statement]
    | -- While condition invariant body; the invariant is only used by the validator
      While Expression [ValidationStatement] [Statement]
    | -- Never parsed: the validator ends a loop body with this to check the invariant, see valReturningWhile
      LoopEnd [ValidationStatement]
    | EndBlock
    deriving (Show, Eq, Ord) -- Assign ProofVar used only in validations, TODO: maintain separate var map for proof vars

-- nextStmt
-- TODO: Naming is probably wrong here
-- Pending statements for the current scope; entering a block swaps in a new queue.
newtype Continuations = Continuations [Statement] deriving (Show)

-- Runtime state is split between the current lexical scope, the remaining statements
-- for that scope, and an optional parent scope to return to on EndBlock.
data ScopeState = ScopeState (Map Variable Value) Continuations (Maybe ScopeState)

-- (scope info, file context [aka standard lib + imports])
data State = State ScopeState (Map Variable Value)

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | NotEq | Lt | Gt | LtEq | GtEq deriving (Eq, Ord, Show)
newtype Iota = Iota String deriving (Eq, Ord, Show)

-- Function being applied, arguments
-- Proof terms reuse the same tree shape for both concrete values and symbolic placeholders.
-- Forall index guards body: body holds for every index meeting all the guards. The index occurs
-- in the guards and the body as BVar, which no substitution touches, so it cannot be captured.
data Proof i
    = FApp (Proof i) [Proof i]
    | ATerm i
    | CTerm Value
    | Forall Variable [Proof i] (Proof i)
    | BVar Variable
    deriving (Show, Eq, Ord)

proofHasForall :: Proof i -> Bool
proofHasForall Forall{} = True
proofHasForall (FApp funct args) = proofHasForall funct || any proofHasForall args
proofHasForall _ = False
type IotaProof = Proof Iota
type VariableProof = Proof Variable

-- TODO: As with BuiltinFunct, the rule name should be a separate type from the arguments
data RwRule
    = Refl VariableProof
    | Eval Variable
    | EvalAll
    | CheckGtZero VariableProof
    | CheckRel VariableProof
    | UserRewrite Variable [VariableProof]
    deriving (Show, Eq, Ord) -- TODO | LtTrans Variable Variable | GtTrans Variable Variable | LtEqTrans Variable Variable deriving Show

data UserRule
    = AxiomRule [Variable] [ValidationStatement] [ValidationStatement]
    | ProofRule [Variable] [ValidationStatement] [VariableProof]
    deriving (Show, Eq, Ord)

type RuleContext = Map Variable UserRule

data VScopeState
    = VScopeState
        (Map Variable Iota)
        [IotaProof]
        Continuations
        (Maybe VScopeState)
    deriving (Show)
data VState = VState VScopeState (Map Variable Iota) [IotaProof] [Iota] RuleContext

instance Show VState where
    show (VState scope iotaCtx proofCtx _ ruleCtx) =
        "VState (" ++ show (scope, iotaCtx, proofCtx, ruleCtx) ++ ")"
