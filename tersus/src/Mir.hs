{-# LANGUAGE PatternSynonyms #-}

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
    , Env
    , Rvalue (..)
    , BinOp (..)
    , ListOp (..)
    , Operand (..)
    , Constant (..)
    , Terminator (..)
    , FunctionSpec (..)
    , LoopSpec (..)
    , emptySpec
    , completeInstances
    , slotsOf
    , ownerOf
    , successors
    , renderProgram
    , renderFunction
    , renderStatement
    , renderTerminator
    , renderRvalue
    ) where

import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (listToMaybe)

import Pretty (renderType, renderVarProof)
import qualified Data.Set as Set
import TersusTypes (Name, Rel (..), Termination (..), Type (..), ValidationStatement (..), Variable, RwRule (..), Expression, exprToProof, instanceOf, substSizes, Size (..), pattern TArray)

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
    , progGenerics :: Map Name ([Variable], [(Variable, Type)]) -- the structs with sizes: their sizes and fields (see completeInstances)
    }
    deriving (Show, Eq)

-- A struct is its fields; an enum its variants (named Enum::Variant) with theirs
data TypeDecl = StructDecl [(Variable, Type)] | EnumDecl [(Name, [(Variable, Type)])]
    deriving (Show, Eq)

data Function = Function
    { fnName :: Name
    , fnParams :: [Local]
    , fnReturns :: Maybe Type -- Nothing for a program that does not return
    , fnLocals :: Map Local LocalDecl -- the return slot (when there is one), the parameters, and the rest
    , fnBlocks :: Map BlockId BasicBlock
    , fnSizeParams :: [Variable] -- the names of the last parameters, which are the sizes that a call of the function gives (see Mono)
    , fnTypeParams :: [Variable] -- the names of the type parameters, which a call gives and native code makes a copy of the function for (see MirMono)
    , fnBorrowed :: [Local] -- the parameters that the function only reads, which a call lends (see MirOwnership)
    , fnSpec :: FunctionSpec
    }
    deriving (Show, Eq)

data LocalDecl = LocalDecl
    { localType :: Type
    , localName :: Maybe Variable -- the source name; Nothing for a temporary
    }
    deriving (Show, Eq)

data BasicBlock = BasicBlock
    { blockStatements :: [Statement]
    , blockTerminator :: Terminator
    }
    deriving (Show, Eq)

data Statement
    = Assign Local Rvalue
    | -- Does nothing when the program runs; the validator's. The names are those the program can use at this point.
      Ghost Env GhostStatement
    | -- The next two are added by MirOwnership, which makes who owns what explicit, and only native code needs them.
      -- Frees what the local owns, and leaves it holding nothing
      Drop Local
    | -- The local points into a value that something else owns: it does not own what it holds, and so does not free it
      Peek Local Rvalue
    deriving (Show, Eq)

-- What the names of the source mean at a point: the local of a variable, or the function (a constant) of a name that
-- stands for one. Ghost statements, contracts and invariants are written with these names.
type Env = Map Variable Operand

data GhostStatement
    = GhostValidation ValidationStatement -- affirm, define, rewrite
    | GhostAxiom Variable [Variable] [ValidationStatement] [ValidationStatement]
    | GhostProof Variable [Variable] [ValidationStatement] [ValidationStatement] [ValidationStatement]
    | -- Where a function is defined (the validator checks its body here and from then on knows what it promises): its name in
      -- the program, the name it has in the source, and whether it is one of the functions defined at the top of the program
      GhostFunction Name Variable Bool
    deriving (Show, Eq)

data Rvalue
    = Use Operand
    | BinaryOp BinOp Operand Operand
    | ListOp ListOp [Operand]
    | MakeList [Operand]
    | -- The value held in a Box. A Box has the value of what it holds, so this is the same value; what differs is where it lives.
      MakeBox Operand
    | -- The value that a Box holds, taken out of it
      Unbox Operand
    | -- A Box of an array of a size, as a Box of an array of any size: the same value, with the size carried by the Box
      Unsize Operand
    | -- A struct or an enum variant (named Enum::Variant), with its fields in declaration order
      MakeData Name [(Variable, Operand)]
    | -- The field of a value that is that constructor (a struct, or a variant the program has shown the value to be)
      ReadField Operand Name Variable
    | IsVariant Operand Name
    | -- The same value, known to be that variant because the validator proved it (`value as Enum::Variant`). The value is
      -- not changed or checked, and the local that gets it has the variant's type, so its fields can be read.
      AsVariant Operand Name
    | -- A copy of the value that shares nothing with it (MirOwnership)
      Clone Operand
    | -- The field of the value the local owns, taken out of it: the local does not hold it any more (MirOwnership)
      TakeField Local Name Variable
    deriving (Show, Eq)

-- Div and Mod need a divisor that is not 0. Compare Eq and NotEq are structural, and the other comparisons are of Ints.
data BinOp = Add | Sub | Mul | Div | Mod | Compare Rel
    deriving (Show, Eq)

-- First and Last need a list that is not empty, Get and Set an index in range. These work on an array as on a list; NewArray n x
-- makes an array of n copies of x, with n not negative; NewBoxed n x does so for an n that is not a constant, in a Box.
data ListOp = Length | First | Last | Get | Push | Set | NewArray | NewBoxed
    deriving (Show, Eq)

-- Move reads the local and leaves it holding nothing (MirOwnership); it is the last use of what the local owns
data Operand = Copy Local | Move Local | Const Constant
    deriving (Show, Eq)

data Constant
    = CInt Integer
    | CBool Bool
    | CList [Constant]
    | CArray [Constant] -- an array literal (#[1, 2]): held inline, where a list is on the heap
    | CData Name [(Variable, Constant)]
    | CFn Name -- a function of the program, as a value
    deriving (Show, Eq)

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
    deriving (Show, Eq)

-- What the program says about a function that the validator uses and the executor does not
data FunctionSpec = FunctionSpec
    { specRequires :: [ValidationStatement]
    , specEnsures :: [ValidationStatement]
    , specTermination :: Maybe Termination
    , specLoops :: Map BlockId LoopSpec -- by the header block of the loop
    , specEnv :: Env -- the parameters, and the functions defined at the top of the program before this one
    }
    deriving (Show, Eq)

data LoopSpec = LoopSpec
    { loopInvariant :: [ValidationStatement]
    , loopTermination :: Maybe Termination
    , loopEnv :: Env
    }
    deriving (Show, Eq)

-- A struct with sizes is a struct of its own for each list of sizes (`Packet<4>`, and `Packet<n>` in a function that has the size n),
-- named by them. This declares every one the program mentions, from the declaration of the struct with the sizes put in.
completeInstances :: Program -> Program
completeInstances program
    | Map.null (progGenerics program) = program
    | otherwise = program{progTypes = go (progTypes program) (Set.toList mentioned)}
  where
    functions = progMain program : Map.elems (progFunctions program)
    mentioned =
        Set.fromList
            ( concat [typeNames (localType d) | f <- functions, d <- Map.elems (fnLocals f)]
                ++ concat [typeNames t | f <- functions, Just t <- [fnReturns f]]
                ++ concat [rvalueNames rv | f <- functions, BasicBlock stmts _ <- Map.elems (fnBlocks f), s <- stmts, rv <- statementRvalues s]
                ++ concat [operandNames o | f <- functions, BasicBlock _ term <- Map.elems (fnBlocks f), o <- terminatorOperands term]
                ++ concat [typeNames t | StructDecl fields <- Map.elems (progTypes program), (_, t) <- fields]
                ++ concat [typeNames t | EnumDecl variants <- Map.elems (progTypes program), (_, fields) <- variants, (_, t) <- fields]
            )
    go types [] = types
    go types (name : rest) =
        case (Map.member name types, instanceOf name) of
            (False, Just (base, sizes))
                | Just (params, fields) <- Map.lookup base (progGenerics program) ->
                    let fields' = [(f, substSizes (zip params sizes) t) | (f, t) <- fields]
                     in go (Map.insert name (StructDecl fields') types) (concatMap (typeNames . snd) fields' ++ rest)
            _ -> go types rest
    statementRvalues s = case s of
        Assign _ rv -> [rv]
        Peek _ rv -> [rv]
        _ -> []
    terminatorOperands t = case t of
        SwitchBool o _ _ -> [o]
        Call callee args _ _ -> callee : args
        _ -> []
    typeNames ty = case ty of
        TNamed n -> [n]
        TList t -> typeNames t
        TArrayOf t _ -> typeNames t
        TBox t -> typeNames t
        TFn args ret -> concatMap typeNames (ret : args)
        _ -> []
    rvalueNames rv = case rv of
        Use o -> operandNames o
        BinaryOp _ a b -> operandNames a ++ operandNames b
        ListOp _ os -> concatMap operandNames os
        MakeList os -> concatMap operandNames os
        MakeBox o -> operandNames o
        Unbox o -> operandNames o
        Unsize o -> operandNames o
        MakeData name fields -> name : concatMap (operandNames . snd) fields
        ReadField o name _ -> name : operandNames o
        IsVariant o name -> name : operandNames o
        AsVariant o name -> name : operandNames o
        Clone o -> operandNames o
        TakeField _ name _ -> [name]
    operandNames o = case o of
        Const c -> constantNames c
        _ -> []
    constantNames c = case c of
        CData name fields -> name : concatMap (constantNames . snd) fields
        CList cs -> concatMap constantNames cs
        CArray cs -> concatMap constantNames cs
        _ -> []

-- The enum that has the variant
-- (a struct is its own constructor, and a cast to it, `p as P`, has the type of a variant of it)
ownerOf :: Program -> Name -> Maybe Name
ownerOf program v =
    case Map.lookup v (progTypes program) of
        Just StructDecl{} -> Just v
        _ -> listToMaybe [n | (n, EnumDecl variants) <- Map.toList (progTypes program), v `elem` map fst variants]

-- The 8-byte words of a value held inline: an Int, a Bool or an address is one, and an array is its elements', a struct its fields' and
-- an enum a word and the widest of its variants'. A Box of an array of no size is two (the address and the number of elements).
slotsOf :: Program -> Type -> Integer
slotsOf program ty =
    case ty of
        TBox (TArrayOf _ SizeAny) -> 2
        TArray t n -> n * slotsOf program t
        TNamed n -> declaredWords n
        TVariant v -> maybe 1 declaredWords (ownerOf program v)
        _ -> 1
  where
    declaredWords n =
        case Map.lookup n (progTypes program) of
            Just (StructDecl fields) -> sum [slotsOf program t | (_, t) <- fields]
            Just (EnumDecl variants) -> 1 + maximum (0 : [sum [slotsOf program t | (_, t) <- fields] | (_, fields) <- variants])
            Nothing -> 1

emptySpec :: FunctionSpec
emptySpec = FunctionSpec [] [] Nothing Map.empty Map.empty

successors :: Terminator -> [BlockId]
successors (Goto b) = [b]
successors (SwitchBool _ t f) = [t, f]
successors (Call _ _ _ next) = [next]
successors Return = []
successors Unreachable = []

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
    loopText (LoopSpec inv term _) =
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
renderStatement (Ghost _ (GhostValidation v)) = "ghost " ++ renderValidation v ++ ";"
renderStatement (Ghost _ (GhostAxiom name args _ _)) = "ghost axiom " ++ name ++ "(" ++ intercalate ", " args ++ ");"
renderStatement (Ghost _ (GhostProof name args _ _ _)) = "ghost proof " ++ name ++ "(" ++ intercalate ", " args ++ ");"
renderStatement (Ghost _ (GhostFunction name _ _)) = "ghost fn " ++ name ++ ";"
renderStatement (Drop l) = "drop " ++ show l ++ ";"
renderStatement (Peek dest rv) = show dest ++ " = peek " ++ renderRvalue rv ++ ";"

renderRvalue :: Rvalue -> String
renderRvalue (Use o) = renderOperand o
renderRvalue (BinaryOp op a b) = renderBinOp op ++ "(" ++ renderOperand a ++ ", " ++ renderOperand b ++ ")"
renderRvalue (ListOp op os) = show op ++ "(" ++ intercalate ", " (map renderOperand os) ++ ")"
renderRvalue (MakeBox o) = "box " ++ renderOperand o
renderRvalue (Unbox o) = "unbox " ++ renderOperand o
renderRvalue (Unsize o) = "unsize " ++ renderOperand o
renderRvalue (MakeList os) = "[" ++ intercalate ", " (map renderOperand os) ++ "]"
renderRvalue (MakeData name []) = name
renderRvalue (MakeData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderOperand o | (f, o) <- fields] ++ " }"
renderRvalue (ReadField o name field) = "(" ++ renderOperand o ++ " as " ++ name ++ ")." ++ field
renderRvalue (IsVariant o name) = renderOperand o ++ " is " ++ name
renderRvalue (AsVariant o name) = renderOperand o ++ " as " ++ name
renderRvalue (Clone o) = "clone " ++ renderOperand o
renderRvalue (TakeField l name field) = "take (" ++ show l ++ " as " ++ name ++ ")." ++ field

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
renderOperand (Move l) = "move " ++ show l
renderOperand (Const c) = "const " ++ renderConstant c

renderConstant :: Constant -> String
renderConstant (CInt i) = show i
renderConstant (CBool True) = "true"
renderConstant (CBool False) = "false"
renderConstant (CList cs) = "[" ++ intercalate ", " (map renderConstant cs) ++ "]"
renderConstant (CArray cs) = "#[" ++ intercalate ", " (map renderConstant cs) ++ "]"
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
