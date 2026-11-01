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
    , RefStep (..)
    , BinOp (..)
    , ListOp (..)
    , ghostOp
    , Operand (..)
    , Constant (..)
    , Terminator (..)
    , FunctionSpec (..)
    , LoopSpec (..)
    , emptySpec
    , completeInstances
    , completeErasedInstances
    , readersOfInput
    , functionsNamed
    , slotsOf
    , dropFunction
    , isDropFunction
    , layoutOf
    , sizeOf
    , alignOf
    , fieldOffsets
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
import TersusTypes (Name, Rel (..), Termination (..), Type (..), ValidationStatement (..), Variable, RwRule (..), Expression, exprToProof, instanceOf, instanceFields, tupleGeneric, Size (..), pattern TArray)

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
    , progInvariants :: Map Name [ValidationStatement] -- what every value of a struct meets, by the name of the struct (not of an instance of it)
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
    , fnMutBorrowed :: [Local] -- the parameters lent for updating (&mut T)
    , fnFrom :: [Local] -- the parameters a reference result is from
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
    | -- The place a reference is to is given a new value (REFERENCES.md, stage 3): the root local, the steps from it,
      -- and the value. It is not an assignment of the root: it goes through a live update loan to the place, and the
      -- root gets a new version whose place at those steps is the value. Native code expands it (MirOwnership).
      AssignRef Local [RefStep] Rvalue
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
    | -- The line and column in the source of the statements that follow, up to the next one. Lowering writes them and the check of
      -- moves reads them (and takes them out), so no other pass sees one.
      GhostPosition Int Int
    | -- The value of the local has been taken apart into its fields (`S { a: x, ... } = v;`): it is used up, and a drop of its type is not run
      -- on it. The ghost erasure makes it the clearing of the local's bytes, which native code takes for a value that was moved out.
      GhostDissolve Local
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
      CopyOf Operand
    | -- The field of the value the local owns, taken out of it: the local does not hold it any more (MirOwnership)
      TakeField Local Name Variable
    | -- A reference to a place of a local (REFERENCES.md): the root local, the steps from it to the place, and whether
      -- it may update the place. It owns nothing and is never freed; reading it gives the place's current version.
      Borrow Local [RefStep] Bool
    | -- The value at the place a reference local is to: the local's current version, in the validator and the executor
      Deref Operand
    deriving (Show, Eq)

-- A step from the root of a borrowed place to the place itself: a field of a struct or variant, or an element at an index
data RefStep = RefField Name Variable | RefIndex Operand
    deriving (Show, Eq)

-- Div and Mod need a divisor that is not 0. Compare Eq and NotEq are of two words of one type (an Int, a Byte, a Bool, a fixed-width
-- integer or an address: anything else is compared by its Eq, which the checker calls), and the other comparisons are of Ints.
data BinOp = Add | Sub | Mul | Div | Mod | Compare Rel
    deriving (Show, Eq)

-- First and Last need a list that is not empty, Get and Set an index in range. These work on an array as on a list; NewArray n x
-- makes an array of n copies of x, with n not negative; NewBoxed n x does so for an n that is not a constant, in a Box. NewEmptyBoxed makes the Box of an array of no elements.
--
-- The operations on addresses (POINTERS.md): AddrNull, AddrOffset p i (i slots of the type further on), AddrCast p, AddrToInt p and
-- AddrFromInt n need no permission; AddrAlloc n (n new slots), AddrGet p i b (a view of the value in a slot), AddrWrite p i x b (x moved
-- into an empty slot), AddrTake p i b (the value moved out of a slot), AddrDropValue p i b and AddrDropRange p i n b (the values of slots
-- dropped where they are), AddrResize p n b (the slots moved to an allocation of n) and AddrFree p b (the allocation given back) are given
-- the permission b too, which only the validator reads. The Block operations make a permission and are ghost: the validator has them, and
-- they are erased (by the ghost erasure, `examples/mir_erase.tersus`) with the permissions, as are the permissions given to the others. After that, AddrWrite, AddrDropValue
-- and AddrDropRange, which give the permission after, give 0.
data ListOp = Length | First | Last | Get | Push | Pop | Set | NewArray | NewBoxed | NewEmptyBoxed | FromList | WriteByte | WriteError | ReadByte | ArgCount | ArgByte | PathByte | FileLoad | FileByte | StoreByte | FileStore | ToByte | FromByte
    | AddrNull | AddrOffset | AddrCast | AddrToInt | AddrFromInt | AddrAlloc | AddrGet | AddrWrite | AddrTake | AddrDropValue | AddrDropRange | AddrResize | AddrFree
    | BlockNew | BlockTaken | BlockResized | BlockSplitLo | BlockSplitHi | BlockJoin | BlockAssume | BlockCast
    | -- Uninit<T>: an empty one, one that holds x, a view of what one holds, what one holds moved out, and an empty one used up. Natively
      -- an Uninit<T> is a T (see Pipeline.nativeProgram), an empty one its words cleared.
      UninitEmpty | UninitNew | UninitGet | UninitTake | UninitDiscard
    | -- An Int as a fixed-width integer (signed, bits), with its range proved: the same number
      Narrow Bool Integer
    deriving (Show, Eq)

-- The operations that make a permission, which are erased with it
ghostOp :: ListOp -> Bool
ghostOp op = op `elem` [BlockNew, BlockTaken, BlockResized, BlockSplitLo, BlockSplitHi, BlockJoin, BlockAssume, BlockCast]

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
    , specWrites :: [Variable] -- the places an update parameter may change (`writes(n.field)`), as the program wrote them; empty means every update parameter whole (REFERENCES.md)
    , specMutParams :: [Variable] -- the parameters lent for updating (&mut T): a call gives the caller a new version of what they are to
    , specFrom :: [Variable] -- the parameters a reference result is from (`-> &T from xs`): a call's result is a reference to a place of one of them (REFERENCES.md)
    }
    deriving (Show, Eq)

data LoopSpec = LoopSpec
    { loopInvariant :: [ValidationStatement]
    , loopTermination :: Maybe Termination
    , loopEnv :: Env
    , loopBody :: BlockId -- the first block of the body: an iteration starts on each edge into it (a condition made of && and || has several tests)
    }
    deriving (Show, Eq)

-- A struct with sizes is a struct of its own for each list of sizes (`Packet<4>`, and `Packet<n>` in a function that has the size n),
-- named by them. This declares every one the program mentions, from the declaration of the struct with the sizes put in.
completeInstances :: Program -> Program
completeInstances = completeInstancesWith False

-- The same after the permissions are erased (the ghost erasure): an instance that is declared now (by a copy of a function for its types, `(T, Block<T>)`
-- for an Int) has no field that is a permission either
completeErasedInstances :: Program -> Program
completeErasedInstances = completeInstancesWith True

completeInstancesWith :: Bool -> Program -> Program
completeInstancesWith erased program
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
            (False, Just (base, args))
                | Just (params, fields) <- maybe (tupleGeneric base) Just (Map.lookup base (progGenerics program))
                , Just fields0 <- instanceFields params args fields ->
                    let fields' = [(f, t) | (f, t) <- fields0, not (erased && isPermission t)]
                     in go (Map.insert name (StructDecl fields') types) (concatMap (typeNames . snd) fields' ++ rest)
            _ -> go types rest
    isPermission t = case t of
        TBlock _ -> True
        _ -> False
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
        TAddr t -> typeNames t
        TBlock t -> typeNames t
        TUninit t -> typeNames t
        TFn args ret -> concatMap typeNames (ret : args)
        TRef t -> typeNames t
        TMutRef t -> typeNames t
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
        CopyOf o -> operandNames o
        Borrow _ steps _ -> concatMap operandNames [o | RefIndex o <- steps]
        Deref o -> operandNames o
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

-- The layout of a value held inline (POINTERS.md, Layout: C's rules), as its bytes and its alignment:
--
--   * an Int, an address, a function and a Box are 8 bytes, a Box of an array of no size 16 (the address and the number of elements);
--   * a Byte and a Bool are 1 byte, and a fixed-width integer as many as it has bits over 8;
--   * an array is its elements, each the size of one apart;
--   * a struct is its fields in the order they are declared, each at an offset that is a multiple of its alignment, and its size is rounded
--     up to the largest alignment, so a struct of fixed-width fields has the layout of the same struct of C;
--   * an enum is a tag (a U32: the place of the variant in the enum) and then the fields of its variant, laid out as a struct from the first
--     offset after the tag that every variant's fields can start at, with the room of the widest.
layoutOf :: Program -> Type -> (Integer, Integer)
layoutOf program = go (0 :: Int)
  where
    go depth ty
        | depth > 64 = (8, 8)
        | otherwise = case ty of
            TByte -> (1, 1)
            TBool -> (1, 1)
            TWord _ bits -> (bits `div` 8, bits `div` 8)
            -- (a Box is laid out as native code holds it: a StdBox, the address of what it holds, and for an array a StdList, MirLists)
            TBox TArrayOf{} -> (24, 8)
            TArray t n -> let (size, align) = go (depth + 1) t in (n * size, align)
            TNamed n -> declared depth n
            TVariant v -> maybe (8, 8) (declared depth) (ownerOf program v)
            TUninit t -> go (depth + 1) t
            TBlock _ -> (0, 1)
            -- (a list is laid out as the StdList that native code makes of it, MirLists: an address, a length and a capacity)
            TList _ -> (24, 8)
            _ -> (8, 8)
    declared depth n = case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> structLayout (map (go (depth + 1) . snd) fields)
        Just (EnumDecl variants) ->
            let layouts = [structLayout (map (go (depth + 1) . snd) fields) | (_, fields) <- variants]
                payloadAlign = maximum (1 : map snd layouts)
                start = roundUp 4 payloadAlign
                align = max 4 payloadAlign
             in (roundUp (start + maximum (0 : map fst layouts)) align, align)
        Nothing -> (8, 8)

-- The bytes and the alignment of a struct of fields of these layouts
structLayout :: [(Integer, Integer)] -> (Integer, Integer)
structLayout layouts =
    let align = maximum (1 : map snd layouts)
        end = foldl (\offset (size, a) -> roundUp offset a + size) 0 layouts
     in (roundUp end align, align)

-- The offset of each of fields of these layouts, from the start of the struct
structOffsets :: [(Integer, Integer)] -> [Integer]
structOffsets layouts = reverse (snd (foldl (\(offset, acc) (size, a) -> let at = roundUp offset a in (at + size, at : acc)) (0, []) layouts))

roundUp :: Integer -> Integer -> Integer
roundUp n a = if a <= 1 then n else ((n + a - 1) `div` a) * a

sizeOf :: Program -> Type -> Integer
sizeOf program = fst . layoutOf program

alignOf :: Program -> Type -> Integer
alignOf program = snd . layoutOf program

-- The byte offset, from the start of the value, of each field of what builds it: a struct (from 0) or a variant of an enum (after the tag,
-- from the start that every variant of the enum shares)
fieldOffsets :: Program -> Name -> [Integer]
fieldOffsets program name = case Map.lookup name (progTypes program) of
    Just (StructDecl fields) -> structOffsets (map (layoutOf program . snd) fields)
    _ -> case [(variants, fields) | EnumDecl variants <- Map.elems (progTypes program), (v, fields) <- variants, v == name] of
        (variants, fields) : _ ->
            let payloadAlign = maximum (1 : [snd (structLayout (map (layoutOf program . snd) fs)) | (_, fs) <- variants])
                start = roundUp 4 payloadAlign
             in map (+ start) (structOffsets (map (layoutOf program . snd) fields))
        [] -> []

-- The 8-byte words of room a value held inline takes in a frame: its bytes, rounded up
slotsOf :: Program -> Type -> Integer
slotsOf program ty = (sizeOf program ty + 7) `div` 8

-- The drop of a struct or an enum, when it has one (`impl Drop for T`, step 26 of the roadmap): the function `<T as Drop>::drop`, which MirMono
-- also names the copy of the drop of a struct with types for an instance so (`<Vec<Int> as Drop>::drop`)
dropFunction :: Program -> Name -> Maybe Name
dropFunction program n =
    let f = "<" ++ n ++ " as Drop>::drop"
     in if Map.member f (progFunctions program) then Just f else Nothing

isDropFunction :: Name -> Bool
isDropFunction name = let suffix = " as Drop>::drop" in reverse suffix == take (length suffix) (reverse name)

emptySpec :: FunctionSpec
emptySpec = FunctionSpec [] [] Nothing Map.empty Map.empty [] [] []

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
    loopText (LoopSpec inv term _ _) =
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
renderValidation (Assume p) = "assume " ++ renderVarProof p
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
renderStatement (Ghost _ (GhostPosition line column)) = "ghost at " ++ show line ++ ":" ++ show column ++ ";"
renderStatement (Ghost _ (GhostProof name args _ _ _)) = "ghost proof " ++ name ++ "(" ++ intercalate ", " args ++ ");"
renderStatement (Ghost _ (GhostFunction name _ _)) = "ghost fn " ++ name ++ ";"
renderStatement (Ghost _ (GhostDissolve l)) = "ghost dissolve " ++ show l ++ ";"
renderStatement (Drop l) = "drop " ++ show l ++ ";"
renderStatement (Peek dest rv) = show dest ++ " = peek " ++ renderRvalue rv ++ ";"
renderStatement (AssignRef root steps rv) = show root ++ concatMap step steps ++ " := " ++ renderRvalue rv ++ ";"
  where
    step (RefField _ field) = "." ++ field
    step (RefIndex o) = "[" ++ renderOperand o ++ "]"

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
renderRvalue (CopyOf o) = "copy " ++ renderOperand o
renderRvalue (TakeField l name field) = "take (" ++ show l ++ " as " ++ name ++ ")." ++ field
renderRvalue (Borrow root steps mutable) = (if mutable then "&mut " else "&") ++ show root ++ concatMap step steps
  where
    step (RefField _ field) = "." ++ field
    step (RefIndex o) = "[" ++ renderOperand o ++ "]"
renderRvalue (Deref o) = "*" ++ renderOperand o

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

-- The operations that give something outside the program: the input and the arguments, and a new allocation
readsWorldOp :: ListOp -> Bool
readsWorldOp op = op `elem` [ReadByte, ArgCount, ArgByte, PathByte, FileLoad, FileByte, StoreByte, FileStore, AddrAlloc, AddrResize, BlockAssume]

-- The functions of the program that read the standard input or the arguments (`readByte`, `argCount`, `argByte`), or call or mention one that does. What such a function gives is not
-- determined by its arguments, so a validator may not say that two calls with the same arguments give the same value.
readersOfInput :: Program -> Set.Set Name
readersOfInput program = grow (Set.fromList [name | (name, fn) <- functions, any reads (statementsOf fn)])
  where
    functions = Map.toList (progFunctions program)
    reads s = case s of
        Assign _ (ListOp op _) -> readsWorldOp op
        Peek _ (ListOp op _) -> readsWorldOp op
        _ -> False
    statementsOf fn = concatMap blockStatements (Map.elems (fnBlocks fn))
    -- (the functions that a function names, as the callee of a call or anywhere a value is used)
    mentions fn = Set.fromList (concatMap (concatMap operandFns . operandsOfRvalue) (concatMap rvaluesOf (statementsOf fn)) ++ concatMap terminatorFns (map blockTerminator (Map.elems (fnBlocks fn))))
    rvaluesOf s = case s of
        Assign _ rv -> [rv]
        Peek _ rv -> [rv]
        _ -> []
    grow known =
        let more = Set.fromList [name | (name, fn) <- functions, not (Set.member name known), not (Set.null (Set.intersection (mentions fn) known))]
         in if Set.null more then known else grow (Set.union known more)

-- The functions of the program that a function names as values or callees in its statements (not those its contracts could name,
-- which are all the functions before it): the validator knows each as the value it is (see ProofState.withFunctions)
functionsNamed :: Function -> Set.Set Name
functionsNamed fn =
    Set.fromList
        ( concatMap (concatMap operandFns . operandsOfRvalue) [rv | s <- statements, rv <- rvaluesOf s]
            ++ concatMap (terminatorFns . blockTerminator) (Map.elems (fnBlocks fn))
        )
  where
    statements = concatMap blockStatements (Map.elems (fnBlocks fn))
    rvaluesOf s = case s of
        Assign _ rv -> [rv]
        Peek _ rv -> [rv]
        _ -> []

terminatorFns :: Terminator -> [Name]
terminatorFns t = case t of
    Call callee args _ _ -> concatMap operandFns (callee : args)
    SwitchBool o _ _ -> operandFns o
    _ -> []

operandFns :: Operand -> [Name]
operandFns o = case o of
    Const c -> constantFns c
    _ -> []

constantFns :: Constant -> [Name]
constantFns c = case c of
    CFn name -> [name]
    CList cs -> concatMap constantFns cs
    CArray cs -> concatMap constantFns cs
    CData _ fields -> concatMap (constantFns . snd) fields
    _ -> []

operandsOfRvalue :: Rvalue -> [Operand]
operandsOfRvalue rv = case rv of
    Use o -> [o]
    BinaryOp _ a b -> [a, b]
    ListOp _ os -> os
    MakeList os -> os
    MakeBox o -> [o]
    Unbox o -> [o]
    Unsize o -> [o]
    MakeData _ fields -> map snd fields
    ReadField o _ _ -> [o]
    IsVariant o _ -> [o]
    AsVariant o _ -> [o]
    CopyOf o -> [o]
    TakeField{} -> []
    Borrow _ steps _ -> [o | RefIndex o <- steps]
    Deref o -> [o]
