module Syntax where

import Data.List (isPrefixOf)
import Data.Map (Map)

import Types

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
    | -- assume e;: a fact that the rest of the path knows without a proof, as after an affirm. It is an assumption, which
      -- `tersus assumptions` lists: what a program takes on trust, such as what a C function did to memory (POINTERS.md).
      Assume VariableProof
    deriving (Show, Eq, Ord)
data Statement
    = Assign Variable Expression
    | -- Binds a variable in the innermost scope, hiding any variable of that name outside it instead of assigning it.
      -- Never parsed: a match uses it for its scrutinee and the fields its patterns name.
      Let Variable Expression
    | Return Expression
    | ValidationStatement ValidationStatement
    | -- struct Name<sizes> { field: Type, ... }; it only matters to the type checker. A struct with sizes (`struct Packet<n> { body:
      -- Array<Int, n> }`) is a type for each list of sizes, `Packet<4>`: see TNamed. The last field is the invariant, `struct Vec<T> {
      -- data: Box<Array<T>>, len: Int } invariant [{ affirm len >= 0; }]`, which every value of the struct meets.
      StructDef Name [Variable] [(Variable, Type)] [ValidationStatement]
    | -- enum Name { Variant { field: Type, ... }, ... } with the variants' full names (Name::Variant)
      EnumDef Name [(Name, [(Variable, Type)])]
    | AxiomDef Variable [Variable] [ValidationStatement] [ValidationStatement]
    | ProofDef Variable [Variable] [ValidationStatement] [ValidationStatement] [ValidationStatement]
    | Block [Statement]
    | -- If condition thenBranch elseBranch; a missing else is an empty branch
      If Expression [Statement] [Statement]
    | -- While condition invariant termination body; the invariant and termination are only used by the validator
      While Expression [ValidationStatement] (Maybe Termination) [Statement]
    | -- trait Name { fn f(...) -> T [{ in }] [{ out }]; ... }: the functions an impl must have. The type checker takes it
      -- apart; it does not reach the lowering.
      TraitDef Name [Variable] [TraitFn]
    | -- impl Type { fn f ... } or impl Trait for Type { fn f ... }: the functions, which are named Type::f. The fields are the trait
      -- (if any) and the types it is given (`impl<T> Sequence<T> for Vec<T>`), the struct or enum, and the name of its type with the
      -- types and sizes of the impl (`Vec<'T>`, which `Self` stands for). The type checker
      -- checks them against the trait and hands them back as ordinary function definitions, so the lowering never sees it.
      ImplDef (Maybe Name) [Arg] Name Type [Statement]
    | -- fn f<S: Sequence<Int>, T>(...) ...: a function whose type parameters have bounds (`BoundedDef [(S, Sequence, [Int])] (the function)`),
      -- which the type checker keeps as a template and makes a function of for each type it is called with (see TypeCheck.templateCall).
      -- It does not reach the lowering.
      BoundedDef [Bound] Statement
    | -- The line and column of the statement that follows it in its block, in a program that was parsed to keep them (`Pipeline`
      -- does, the parser functions called on their own do not). Nothing runs it: the lowering takes it as the place that the
      -- MIR statements after it come from, for the errors that name a place (a value used after it was moved).
      Mark Int Int
    | -- T implements Copy (`impl Copy for T { };`), which the checker has seen to hold: a value of it is copied where it is wanted,
      -- and not moved. The lowering collects them.
      CopyDef Name
    | -- T is linear (`linear struct T { ... };`): a value of it is used exactly once, as a permission is (POINTERS.md, DROPS.md Part 2).
      -- The lowering collects them, for the check of moves.
      LinearDef Name
    | -- The function of that name, defined next, is extern (`extern fn write(...) -> Int [{ ... }] [{ ... }];`): it has no body, native code
      -- calls the C function of the name, and what its contract promises is assumed (POINTERS.md, Assumptions)
      ExternDef Name
    | -- T has a drop (`impl Drop for T { fn drop(self: Self) -> Int { ... }; };`), which native code calls where a value of it goes out of
      -- scope: the checker hands it to the lowering, for the check of moves (a type with a drop is not linear)
      DropDef Name
    | -- The value of the variable has been taken apart into its fields (`Vec { addr: a, len: n, blk: b } = v;`, which the parser makes into
      -- the reads of the fields and this): it is used up, so a drop it has is not run. Only native code needs it (MirGhost).
      Dissolve Variable
    deriving (Show, Eq, Ord) -- Assign ProofVar used only in validations, TODO: maintain separate var map for proof vars

-- A bound on a type parameter of a function: the parameter, the trait its type has to implement and the types it is given
-- (`S: Sequence<Int>`)
type Bound = (Variable, Name, [Type])

-- A function a trait asks for: its name, the names of its parameters, the signature (Self stands for the type that
-- implements the trait), and the contracts every implementation has to meet
data TraitFn = TraitFn
    { traitFnName :: Name
    , traitFnParams :: [Variable]
    , traitFnSignature :: Signature
    , traitFnRequires :: [ValidationStatement]
    , traitFnEnsures :: [ValidationStatement]
    }
    deriving (Show, Eq, Ord)

-- What a function of an impl is called in the program: <Type>::f for an impl of Type, and <Type as Trait>::f for an impl of a
-- trait. The programs write Type::f, x.f(...) and Trait::f(x), which the type checker resolves to one of these (Type::f is
-- ambiguous if several impls of Type define f), or write the name in full as <Type as Trait>::f(...).
implFunctionName :: Name -> Maybe Name -> Name -> Name
implFunctionName owner Nothing function = "<" ++ owner ++ ">::" ++ function
implFunctionName owner (Just trait) function = "<" ++ owner ++ " as " ++ trait ++ ">::" ++ function

-- The f of such a name
implFunctionPart :: Name -> Name
implFunctionPart = drop 3 . dropWhile (/= '>')

-- The function that stands for the check that an impl meets its trait (see TypeCheck.checkImpl) is named after the trait, the
-- type and the function, in a way no program can write: "Trait for Type::function"
implCheckName :: Name -> Name -> Name -> Name
implCheckName trait owner function = trait ++ " for " ++ owner ++ "::" ++ function

-- (trait, type, function) of such a name
parseImplCheckName :: Name -> Maybe (Name, Name, Name)
parseImplCheckName name =
    case breakOn " for " name of
        Just (trait, rest) | Just (owner, function) <- breakOn "::" rest -> Just (trait, owner, function)
        _ -> Nothing
  where
    breakOn needle = go ""
      where
        go acc text@(c : cs)
            | needle `isPrefixOf` text = Just (reverse acc, drop (length needle) text)
            | otherwise = go (c : acc) cs
        go _ [] = Nothing

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
