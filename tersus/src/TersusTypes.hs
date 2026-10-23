{-# LANGUAGE PatternSynonyms #-}

module TersusTypes where

import qualified Data.IntMap.Strict as IntMap
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as S

type Variable = String
type Name = String

-- Ctor builds a struct from its fields, given in declaration order, and Field reads one by name. The Field of a `..base` update names the struct the base must be.
-- A struct literal is the application of its Ctor, so the proof engine sees structs as ordinary terms.
data BuiltinFunct
    = Size | First | Last | Get | Push | Set | Plus | Minus | Times | Div | Mod
    | Rel Rel
    | -- Within a b: a is a field of b, or a field of a field, and so on. Never parsed: it is how the validator checks
      -- that what a loop or function says shrinks has done so.
      Within
    | Ctor Name [Variable]
    | Field (Maybe Name) Variable
    | -- Is Ctor tests which variant an enum value is; Project Ctor reads a field of a value known to be that variant
      Is Name
    | Project Name Variable
    | -- Cast Ctor reinterprets an enum value as that variant so its fields can be read. The validator demands the proof
      -- that the value is that variant; evaluation does nothing, and a wrong cast is undefined behaviour.
      Cast Name
    deriving (Show, Eq, Ord)

-- The types the checker (TypeCheck) knows. They are erased after checking: validation and evaluation never
-- look at them. TVar is the checker's own unknown and is never written by a program.
data Type = TInt | TBool | TList Type | TFn [Type] Type | TNamed Name | TVariant Name | TVar Int
    deriving (Show, Eq, Ord)

-- The declared parameter types and return type of a user function
data Signature = Signature [Type] Type deriving (Show, Eq, Ord)

-- How a loop or function says that it ends. A loop has to say; a function that says nothing is guaranteed to
-- terminate, and so may not call itself.
data Termination
    = -- shrinks e: what the program writes. The type checker resolves it by the type of e, into Counting or Parts,
      -- and the validator only sees those.
      Shrinks Expression
    | -- An integer that is at least 0 and gets smaller every iteration or recursive call
      Counting Expression
    | -- An enum or struct value that is, each iteration or recursive call, a part of the one before it (a field,
      -- or a field of a field). Such values are finite, so this ends.
      Parts Expression
    | -- ~: no guarantee, and whatever runs it is not guaranteed to terminate either
      MayDiverge
    | -- Never parsed: the copy of a function that its own body calls, with what the function said
      Recursing (Maybe Termination)
    deriving (Show, Eq, Ord)

-- NativeFunct signature termination body
data FunctBody = NativeFunct Signature (Maybe Termination) [Statement] | BuiltinFunct BuiltinFunct deriving (Show, Eq, Ord)

data Value
    = VInt Integer
    | VList [Value]
    | VBool Bool
    | -- A struct value: the struct's name and its fields, in declaration order
      VData Name [(Variable, Value)]
    | -- A function of the MIR program, by name: how the validator writes the function as a constant of a proof
      VFnRef Name
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
    compare (VFnRef a) (VFnRef b) = compare a b
    compare a b = compare (rank a) (rank b)
      where
        rank :: Value -> Int
        rank VInt{} = 0
        rank VList{} = 1
        rank VBool{} = 2
        rank VData{} = 3
        rank VFunct{} = 4
        rank VFnRef{} = 5

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
    | -- Binds a variable in the innermost scope, hiding any variable of that name outside it instead of assigning it.
      -- Never parsed: a match uses it for its scrutinee and the fields its patterns name.
      Let Variable Expression
    | Return Expression
    | ValidationStatement ValidationStatement
    | -- struct Name { field: Type, ... }; it only matters to the type checker
      StructDef Name [(Variable, Type)]
    | -- enum Name { Variant { field: Type, ... }, ... } with the variants' full names (Name::Variant)
      EnumDef Name [(Name, [(Variable, Type)])]
    | AxiomDef Variable [Variable] [ValidationStatement] [ValidationStatement]
    | ProofDef Variable [Variable] [ValidationStatement] [ValidationStatement] [ValidationStatement]
    | Block [Statement]
    | -- If condition thenBranch elseBranch; a missing else is an empty branch
      If Expression [Statement] [Statement]
    | -- While condition invariant termination body; the invariant and termination are only used by the validator
      While Expression [ValidationStatement] (Maybe Termination) [Statement]
    deriving (Show, Eq, Ord) -- Assign ProofVar used only in validations, TODO: maintain separate var map for proof vars

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
-- The proof term for an expression: variables are abstract terms, values and builtins constant ones
exprToProof :: Expression -> VariableProof
exprToProof (Val val) = CTerm val
exprToProof (Var var) = ATerm var
exprToProof (F fnExpr argExprs) = FApp (exprToProof fnExpr) (map exprToProof argExprs)

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

-- The proof engine's terms and closure
--
-- A forall is one opaque term built from its guards and body, so the same forall twice is one term
data TermKey = KIota Iota | KConst Int | KApp Int [Int] | KBound Variable | KForall Variable [Int] Int deriving (Eq, Ord)

-- What tells constants apart. Builtin functions are one constant each, however they were written.
-- Any other constant (a user function) has no key and is found by comparing whole values.
data ConstKey = CInt Integer | CList [ConstKey] | CBool Bool | CData Name [(Variable, ConstKey)] | CBuiltin String deriving (Eq, Ord)

data TermTable = TermTable
    { tableKeys :: Map.Map TermKey Int
    , tableConsts :: [(Value, Int)]
    , tableConstIds :: Map.Map ConstKey Int -- the number of each constant, found without comparing whole values
    , tableOtherConsts :: [(Value, Int)] -- constants with no key
    , tableApps :: [(Int, (Int, [Int]))] -- applications: term, function term, argument terms
    , tableForalls :: [(Int, (Variable, [Int], Int))] -- foralls: term, index, guard terms, body term
    , tableAppCount :: Int
    , tableForallCount :: Int
    }

data Shape = AppShape Int [Int] | ForallShape Variable [Int] Int

type ShapeKey = Either (Int, [Int]) (Variable, [Int], Int)

data Closure = Closure
    { closureParents :: IntMap.IntMap Int -- a term number that is not its own class points toward its class
    , closureSignatures :: Map.Map ShapeKey Int -- a term of each signature
    , closureUsers :: IntMap.IntMap [Int] -- the nodes that have a term of the class as a part, by class
    , closureNodes :: IntMap.IntMap (Int, Shape) -- the terms that have parts
    }

-- A solver holds the terms and the congruence closure of some facts, so that more facts and goals can be added to it
-- without starting again. Adding gives a new solver; the one it was added to is unchanged.
data Solver = Solver
    { solverTable :: TermTable
    , solverClosure :: Closure
    , solverTrueId :: Int
    , solverZeroId :: Int
    , solverApps :: Int -- how many applications and foralls of the table the closure has
    , solverForalls :: Int
    }


-- The facts of a proof context that are already in a solver, so that a question about the context does not start again
-- from the facts (see ProofEngine.factCacheAdd). It is a guess about the context that is checked before it is used.
data FactCache = FactCache
    { cacheOriginals :: S.Set IotaProof -- the facts as the program has them
    , cacheFacts :: [IotaProof] -- the facts the solver has, with the builtins' contracts left out
    , cacheFactSet :: S.Set IotaProof
    , cacheSolver :: Solver
    }
