module Mir
    ( Local (..)
    , BlockId (..)
    , Program (..)
    , TypeDecl (..)
    , Function (..)
    , LocalDecl (..)
    , BasicBlock (..)
    , Statement (..)
    , GhostStatement (..)
    , Rvalue (..)
    , BinOp (..)
    , ListOp (..)
    , Operand (..)
    , Constant (..)
    , Terminator (..)
    , FunctionSpec (..)
    , LoopSpec (..)
    , emptySpec
    , successors
    , checkProgram
    , renderProgram
    , renderFunction
    ) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

import Pretty (renderVarProof)
import ProofHelpers (exprToProof)
import TersusTypes (Name, Rel (..), Termination (..), Type (..), ValidationStatement (..), Variable, RwRule (..), Expression)
import TypeCheck (renderType)
import Utils (Result (..))

-- The MIR is the program as a control-flow graph: what the machine does, with no `if`, `while`, `match`, `for` or nested
-- expressions left. It follows Rust's MIR where Tersus is like Rust: a function is blocks of simple statements, each
-- ended by a jump, and locals are numbered and typed. Values are immutable, so a place is just a local.
-- See MIR.md.

-- _0 is the return slot, _1 to _n the parameters, the others variables and temporaries
newtype Local = Local Int deriving (Eq, Ord)

-- bb0 is the entry
newtype BlockId = BlockId Int deriving (Eq, Ord)

instance Show Local where
    show (Local n) = "_" ++ show n

instance Show BlockId where
    show (BlockId n) = "bb" ++ show n

data Program = Program
    { progTypes :: Map Name TypeDecl
    , progFunctions :: Map Name Function -- every function but main, a nested one lifted to the top (outer::inner)
    , progMain :: Function -- the statements of the program; no parameters
    }
    deriving (Show)

-- A struct is its fields; an enum its variants (named Enum::Variant) with theirs
data TypeDecl = StructDecl [(Variable, Type)] | EnumDecl [(Name, [(Variable, Type)])]
    deriving (Show)

data Function = Function
    { fnName :: Name
    , fnParams :: [Local]
    , fnReturns :: Maybe Type -- Nothing for a program that does not return
    , fnLocals :: Map Local LocalDecl -- the return slot (when there is one), the parameters, and the rest
    , fnBlocks :: Map BlockId BasicBlock
    , fnSpec :: FunctionSpec
    }
    deriving (Show)

data LocalDecl = LocalDecl
    { localType :: Type
    , localName :: Maybe Variable -- the source name; Nothing for a temporary
    }
    deriving (Show)

data BasicBlock = BasicBlock
    { blockStatements :: [Statement]
    , blockTerminator :: Terminator
    }
    deriving (Show)

data Statement
    = Assign Local Rvalue
    | -- Does nothing when the program runs; the validator's
      Ghost GhostStatement
    deriving (Show)

data GhostStatement
    = GhostValidation ValidationStatement -- affirm, define, rewrite
    | GhostAxiom Variable [Variable] [ValidationStatement] [ValidationStatement]
    | GhostProof Variable [Variable] [ValidationStatement] [ValidationStatement] [ValidationStatement]
    deriving (Show)

data Rvalue
    = Use Operand
    | BinaryOp BinOp Operand Operand
    | ListOp ListOp [Operand]
    | MakeList [Operand]
    | -- A struct or an enum variant (named Enum::Variant), with its fields in declaration order
      MakeData Name [(Variable, Operand)]
    | -- The field of a value that is that constructor (a struct, or a variant the program has shown the value to be)
      ReadField Operand Name Variable
    | IsVariant Operand Name
    deriving (Show)

-- Div and Mod need a divisor that is not 0. Compare Eq and NotEq are structural, and the other comparisons are of Ints.
data BinOp = Add | Sub | Mul | Div | Mod | Compare Rel
    deriving (Show, Eq)

-- First and Last need a list that is not empty, Get and Set an index in range
data ListOp = Length | First | Last | Get | Push | Set
    deriving (Show, Eq)

data Operand = Copy Local | Const Constant
    deriving (Show)

data Constant
    = CInt Integer
    | CBool Bool
    | CList [Constant]
    | CData Name [(Variable, Constant)]
    | CFn Name -- a function of the program, as a value
    deriving (Show)

data Terminator
    = Goto BlockId
    | -- The test of every `if` and `while`: on true the first block, otherwise the second
      SwitchBool Operand BlockId BlockId
    | -- Call callee arguments destination next: the callee is a function constant for a call of a function by name, and a
      -- local for a call of a function value
      Call Operand [Operand] Local BlockId
    | -- The value is in _0
      Return
    | -- The end of a function whose every path returned
      Unreachable
    deriving (Show)

-- What the program says about a function that the validator uses and the executor does not
data FunctionSpec = FunctionSpec
    { specRequires :: [ValidationStatement]
    , specEnsures :: [ValidationStatement]
    , specTermination :: Maybe Termination
    , specLoops :: Map BlockId LoopSpec -- by the header block of the loop
    }
    deriving (Show)

data LoopSpec = LoopSpec
    { loopInvariant :: [ValidationStatement]
    , loopTermination :: Maybe Termination
    }
    deriving (Show)

emptySpec :: FunctionSpec
emptySpec = FunctionSpec [] [] Nothing Map.empty

successors :: Terminator -> [BlockId]
successors (Goto b) = [b]
successors (SwitchBool _ t f) = [t, f]
successors (Call _ _ _ next) = [next]
successors Return = []
successors Unreachable = []

-- Whether the program is well formed: every block a jump names is there, every local used is declared, and every local
-- has a type that is known. What lowering must always produce; the tests run it on every lowering.
checkProgram :: Program -> Result () String
checkProgram program =
    case concatMap problems (progMain program : Map.elems (progFunctions program)) of
        [] -> Ok ()
        problem : _ -> Error problem
  where
    functionNames = Map.keys (progFunctions program)
    problems fn =
        map (("In " ++ fnName fn ++ ": ") ++) $
            [ "no entry block bb0" | not (block (BlockId 0)) ]
                ++ [show l ++ " has no known type" | (l, d) <- Map.toList (fnLocals fn), hasUnknown (localType d)]
                ++ ["parameter " ++ show l ++ " is not declared" | l <- fnParams fn, not (declared l)]
                ++ ["_0 is not declared" | Just _ <- [fnReturns fn], not (declared (Local 0))]
                ++ concat
                    [ [show b ++ " uses the undeclared " ++ show l | l <- concatMap statementLocals stmts ++ terminatorLocals term, not (declared l)]
                        ++ [show b ++ " jumps to " ++ show t ++ ", which is not there" | t <- successors term, not (block t)]
                        ++ [show b ++ " names the function " ++ n ++ ", which is not there" | n <- concatMap statementFunctions stmts ++ terminatorFunctions term, n `notElem` functionNames]
                    | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn)
                    ]
                ++ ["a loop is at " ++ show b ++ ", which is not there" | b <- Map.keys (specLoops (fnSpec fn)), not (block b)]
      where
        declared l = Map.member l (fnLocals fn)
        block b = Map.member b (fnBlocks fn)
    hasUnknown (TVar _) = True
    hasUnknown (TList t) = hasUnknown t
    hasUnknown (TFn args ret) = any hasUnknown (ret : args)
    hasUnknown _ = False

statementLocals :: Statement -> [Local]
statementLocals (Assign dest rv) = dest : rvalueLocals rv
statementLocals Ghost{} = []

rvalueLocals :: Rvalue -> [Local]
rvalueLocals rv = concatMap operandLocals (rvalueOperands rv)

rvalueOperands :: Rvalue -> [Operand]
rvalueOperands (Use o) = [o]
rvalueOperands (BinaryOp _ a b) = [a, b]
rvalueOperands (ListOp _ os) = os
rvalueOperands (MakeList os) = os
rvalueOperands (MakeData _ fields) = map snd fields
rvalueOperands (ReadField o _ _) = [o]
rvalueOperands (IsVariant o _) = [o]

operandLocals :: Operand -> [Local]
operandLocals (Copy l) = [l]
operandLocals (Const _) = []

terminatorLocals :: Terminator -> [Local]
terminatorLocals (SwitchBool o _ _) = operandLocals o
terminatorLocals (Call f args dest _) = dest : concatMap operandLocals (f : args)
terminatorLocals _ = []

statementFunctions :: Statement -> [Name]
statementFunctions (Assign _ rv) = concatMap operandFunctions (rvalueOperands rv)
statementFunctions Ghost{} = []

terminatorFunctions :: Terminator -> [Name]
terminatorFunctions (SwitchBool o _ _) = operandFunctions o
terminatorFunctions (Call f args _ _) = concatMap operandFunctions (f : args)
terminatorFunctions _ = []

operandFunctions :: Operand -> [Name]
operandFunctions (Const c) = constantFunctions c
operandFunctions _ = []

constantFunctions :: Constant -> [Name]
constantFunctions (CFn n) = [n]
constantFunctions (CList cs) = concatMap constantFunctions cs
constantFunctions (CData _ fs) = concatMap (constantFunctions . snd) fs
constantFunctions _ = []

-- Rendering: the text of `tersus mir`

renderProgram :: Program -> String
renderProgram program =
    intercalate "\n" (typeLines ++ map renderFunction (Map.elems (progFunctions program) ++ [progMain program]))
  where
    typeLines = concat [[renderTypeDecl name decl, ""] | (name, decl) <- Map.toList (progTypes program)]

renderTypeDecl :: Name -> TypeDecl -> String
renderTypeDecl name (StructDecl fields) = "struct " ++ name ++ " { " ++ renderFields fields ++ " }"
renderTypeDecl name (EnumDecl variants) =
    "enum " ++ name ++ " { " ++ intercalate ", " [v ++ (if null fs then "" else " { " ++ renderFields fs ++ " }") | (v, fs) <- variants] ++ " }"

renderFields :: [(Variable, Type)] -> String
renderFields fields = intercalate ", " [f ++ ": " ++ renderType t | (f, t) <- fields]

renderFunction :: Function -> String
renderFunction fn =
    unlines $
        [ "fn " ++ fnName fn ++ "(" ++ intercalate ", " [show p ++ ": " ++ maybe "?" (renderType . localType) (Map.lookup p (fnLocals fn)) | p <- fnParams fn] ++ ")" ++ maybe "" (\t -> " -> " ++ renderType t) (fnReturns fn) ++ " {"
        ]
            ++ map ("    " ++) (specLines ++ paramLines ++ localLines)
            ++ concatMap blockLines (Map.toList (fnBlocks fn))
            ++ ["}"]
  where
    spec = fnSpec fn
    specLines =
        [ "requires: " ++ renderGhostList (specRequires spec) | not (null (specRequires spec))
        ]
            ++ ["ensures: " ++ renderGhostList (specEnsures spec) | not (null (specEnsures spec))]
            ++ ["terminates: " ++ renderTermination t | Just t <- [specTermination spec]]
    paramLines =
        [ "// " ++ intercalate ", " [show p ++ " = " ++ n | p <- fnParams fn, Just d <- [Map.lookup p (fnLocals fn)], Just n <- [localName d]]
        | not (null (fnParams fn))
        ]
    localLines =
        [ "let " ++ show l ++ ": " ++ renderType (localType d) ++ ";" ++ maybe "" (\n -> " // " ++ n) (localName d)
        | (l, d) <- Map.toList (fnLocals fn)
        , l `notElem` fnParams fn
        ]
    blockLines (b, BasicBlock stmts term) =
        ["    " ++ show b ++ ": {"]
            ++ ["        // loop: " ++ loopText ls | Just ls <- [Map.lookup b (specLoops spec)]]
            ++ map (("        " ++) . renderStatement) stmts
            ++ ["        " ++ renderTerminator term, "    }"]
    loopText (LoopSpec inv term) =
        intercalate "; " (["invariant " ++ renderGhostList inv | not (null inv)] ++ ["terminates " ++ renderTermination t | Just t <- [term]])

renderTermination :: Termination -> String
renderTermination (Shrinks e) = "shrinks " ++ renderExpr e
renderTermination (Counting e) = "shrinks " ++ renderExpr e
renderTermination (Parts e) = "shrinks " ++ renderExpr e
renderTermination MayDiverge = "~"
renderTermination (Recursing t) = maybe "~" renderTermination t

renderExpr :: Expression -> String
renderExpr = renderVarProof . exprToProof

renderGhostList :: [ValidationStatement] -> String
renderGhostList stmts = "{ " ++ intercalate "; " (map renderValidation stmts) ++ " }"

renderValidation :: ValidationStatement -> String
renderValidation (ProofAssert p) = "affirm " ++ renderVarProof p
renderValidation (AssignProofVar v e) = "define " ++ v ++ " = " ++ renderExpr e
renderValidation (Rewrite rule) = "rewrite " ++ renderRule rule

renderRule :: RwRule -> String
renderRule (Refl p) = "refl " ++ renderVarProof p
renderRule (Eval v) = "eval " ++ v
renderRule EvalAll = "evalAll"
renderRule (CheckGtZero p) = "checkGtZero " ++ renderVarProof p
renderRule (CheckRel p) = "checkRel " ++ renderVarProof p
renderRule (UserRewrite name ps) = unwords (name : map renderVarProof ps)

renderStatement :: Statement -> String
renderStatement (Assign dest rv) = show dest ++ " = " ++ renderRvalue rv ++ ";"
renderStatement (Ghost (GhostValidation v)) = "ghost " ++ renderValidation v ++ ";"
renderStatement (Ghost (GhostAxiom name args _ _)) = "ghost axiom " ++ name ++ "(" ++ intercalate ", " args ++ ");"
renderStatement (Ghost (GhostProof name args _ _ _)) = "ghost proof " ++ name ++ "(" ++ intercalate ", " args ++ ");"

renderRvalue :: Rvalue -> String
renderRvalue (Use o) = renderOperand o
renderRvalue (BinaryOp op a b) = renderBinOp op ++ "(" ++ renderOperand a ++ ", " ++ renderOperand b ++ ")"
renderRvalue (ListOp op os) = show op ++ "(" ++ intercalate ", " (map renderOperand os) ++ ")"
renderRvalue (MakeList os) = "[" ++ intercalate ", " (map renderOperand os) ++ "]"
renderRvalue (MakeData name []) = name
renderRvalue (MakeData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderOperand o | (f, o) <- fields] ++ " }"
renderRvalue (ReadField o name field) = "(" ++ renderOperand o ++ " as " ++ name ++ ")." ++ field
renderRvalue (IsVariant o name) = renderOperand o ++ " is " ++ name

renderBinOp :: BinOp -> String
renderBinOp (Compare rel) = case rel of
    Eq -> "Eq"
    NotEq -> "NotEq"
    Lt -> "Lt"
    Gt -> "Gt"
    LtEq -> "LtEq"
    GtEq -> "GtEq"
renderBinOp op = show op

renderOperand :: Operand -> String
renderOperand (Copy l) = show l
renderOperand (Const c) = "const " ++ renderConstant c

renderConstant :: Constant -> String
renderConstant (CInt i) = show i
renderConstant (CBool True) = "true"
renderConstant (CBool False) = "false"
renderConstant (CList cs) = "[" ++ intercalate ", " (map renderConstant cs) ++ "]"
renderConstant (CData name []) = name
renderConstant (CData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderConstant c | (f, c) <- fields] ++ " }"
renderConstant (CFn name) = "fn " ++ name

renderTerminator :: Terminator -> String
renderTerminator (Goto b) = "goto " ++ show b ++ ";"
renderTerminator (SwitchBool o t f) = "switch " ++ renderOperand o ++ " [true: " ++ show t ++ ", false: " ++ show f ++ "];"
renderTerminator (Call f args dest next) =
    show dest ++ " = call " ++ renderCallee f ++ "(" ++ intercalate ", " (map renderOperand args) ++ ") -> " ++ show next ++ ";"
  where
    renderCallee (Const (CFn name)) = name
    renderCallee o = renderOperand o
renderTerminator Return = "return;"
renderTerminator Unreachable = "unreachable;"
