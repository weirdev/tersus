{-# LANGUAGE PatternSynonyms #-}

module TersusTypes where

import qualified Data.IntMap.Strict as IntMap
import Data.Char (isAlphaNum, isDigit, isLower, isUpper)
import Data.List (intercalate, isPrefixOf)
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as S

type Variable = String
type Name = String

-- Ctor builds a struct from its fields, given in declaration order, and Field reads one by name. The Field of a `..base` update names the struct the base must be.
-- A struct literal is the application of its Ctor, so the proof engine sees structs as ordinary terms.
data BuiltinFunct
    = Size | First | Last | Get | Push | Pop | Set | Plus | Minus | Times | Div | Mod
    | -- NewArray n x: an array of n copies of x, n being a constant. ArrayFrom is the array that a literal list of constants makes (`#[1, 2]`).
      NewArray | ArrayFrom
    | -- NewBoxedArray n x: Array::boxed(n, x), an array of n copies of x, n being any Int not negative, in a Box that carries the size
      NewBoxedArray
    | -- NewEmptyArray: Array::empty(), an array of no elements in a Box that carries the size 0, of any element type (no element is needed)
      NewEmptyArray
    | -- WriteByte b: writeByte(b), the Byte b written to the standard output. Its value is b: the only effect of a program that the
      -- language has, which the validator does not model beyond that.
      WriteByte
    | -- WriteError b: writeError(b), the same for the standard error
      WriteError
    | -- ReadByte: readByte(), the next byte of the standard input, or -1 when there is no more. Its value is not known to the validator beyond
      -- being from -1 to 255.
      ReadByte
    | -- ArgCount: argCount(), the number of arguments the program was given. ArgByte i j: argByte(i, j), the byte j of argument i, or -1 when there
      -- is no such argument or byte. What they give is not known to the validator beyond its range.
      ArgCount
    | ArgByte
    | -- The files: pathByte(b) adds a byte to a path, fileLoad() loads the file at the path (its size, or -1), fileByte(i) is a byte of the file that was loaded
      -- (or -1), storeByte(b) adds a byte to the file to be stored, and fileStore() stores it in the file at the path (0, or -1).
      PathByte
    | FileLoad
    | FileByte
    | StoreByte
    | FileStore
    | -- ToByte x: toByte(x), the Byte that the Int x is (x from 0 to 255). FromByte b: toInt(b), the Int that the Byte b is. A Byte is an Int that is from
      -- 0 to 255, and a different type, so nothing makes one by accident: these two are how a value goes from the one to the other.
      ToByte
    | FromByte
    | -- BytesFrom list: the List<Byte> that a list of Ints from 0 to 255 written out is. Only the parser writes it, for the bytes of a string literal.
      BytesFrom
    | -- Unsize b: the Box of an array of a size, as a Box of an array of any size (the size goes into the Box, the value is the same)
      Unsize
    | -- NewBox x: x held in a Box. A Box has the value of what it holds (it is where that lives that differs), so in a value it is x.
      NewBox
    | -- UnBox b: the value that b holds, taken out of it
      UnBox
    | Rel Rel
    | -- a && b, a || b and !a: the connectives of a condition. The lowering turns them into the jumps they stand for (a && b does not
      -- evaluate b when a is false), so only the checker, the evaluation of a constant and the printer see them.
      And
    | Or
    | Not
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

-- The builtins whose value is something outside the program (the input, the arguments): a call of one is not a function of its arguments,
-- so a validator does not say that two calls are the same value, and a proof may not call one
readsWorld :: BuiltinFunct -> Bool
readsWorld b = b `elem` [ReadByte, ArgCount, ArgByte, PathByte, FileLoad, FileByte, StoreByte, FileStore]


-- The types the checker (TypeCheck) knows. They are erased after checking: validation and evaluation never
-- look at them. TVar is the checker's own unknown and is never written by a program.
-- TArrayOf element size: a sequence of that many elements held inline, wherever the array is made (a local, a parameter, a result
-- or an element of a bigger array), with no pointer to it. The size is part of the type.
data Type = TInt | TByte | TBool | TList Type | TArrayOf Type Size | TBox Type | TFn [Type] Type | TNamed Name | TVariant Name | TVar Int
    | -- A function with size parameters (`fn dot<n>(a: Array<Int, n>, ...)`): the type of the function for any values of the sizes. A call
      -- gives each its value, so a use of one that is not a call has no type.
      TForall [Variable] [Variable] Type
    | -- A type parameter of a function (`T` in `fn first<T>(a: &List<T>) -> T`): a type that the function knows nothing of, which a call gives
      TParam Name
    | -- A parameter that the function only reads, so a call does not give it a copy (`fn sum(a: &List<Int>)`). Only a parameter has one:
      -- in the function it is its type, a value it cannot assign, and a call gives it the value as it is.
      TRef Type
    deriving (Show, Eq, Ord)

-- The size argument of a type: a constant, or `?`, a size that the type does not say. A type with a `?` is unsized: its size is
-- known only to something that holds a pointer to it and carries the size along (a Box, later), so it cannot be held by value.
-- `Array<Int>` is `Array<Int, ?>`: a size that is left out is `?`.
-- A name is a size parameter of the function (`n` in `fn dot<n>`), which stands for a constant that its callers give; SizeVar is the
-- checker's own unknown, for the size a call gives a parameter, and is never written by a program.
data Size = SizeConst Integer | SizeAny | SizeParam Name | SizeVar Int
    deriving (Show, Eq, Ord)

-- What a struct with parameters is given: a size, or a type
data Arg = ArgSize Size | ArgType Type
    deriving (Show, Eq, Ord)

-- A parameter that starts with a capital letter is a type, and any other is a size
isTypeName :: Variable -> Bool
isTypeName name = case name of
    c : _ -> isUpper c
    [] -> False

-- The type that a struct with parameters is for a list of sizes and types (`Packet<4>`, `Vec<Int, 3>`, and `Vec<'T, n>` in a function that has
-- the type T and the size n) is a struct of its own, named by them, with the fields of the declaration with them in. Everything after the
-- checker sees an ordinary struct; the name is how the checker and MirMono find the declaration and the arguments again.
instanceName :: Name -> [Arg] -> Name
instanceName base args = base ++ "<" ++ intercalate ", " (map argText args) ++ ">"

argText :: Arg -> String
argText (ArgSize size) = sizeText size
argText (ArgType ty) = typeText ty

sizeText :: Size -> String
sizeText (SizeConst n) = show n
sizeText SizeAny = "?"
sizeText (SizeParam name) = name
sizeText (SizeVar n) = "_" ++ show n

-- A type as the name of an instance writes it (a type parameter has a ' before it, so that it is not a struct, and an unknown has a ?)
typeText :: Type -> String
typeText ty = case ty of
    TInt -> "Int"
    TByte -> "Byte"
    TBool -> "Bool"
    TList t -> "List<" ++ typeText t ++ ">"
    TBox t -> "Box<" ++ typeText t ++ ">"
    TRef t -> "&" ++ typeText t
    TArrayOf t size -> "Array<" ++ typeText t ++ ", " ++ sizeText size ++ ">"
    TFn args ret -> "fn(" ++ intercalate ", " (map typeText args) ++ ") -> " ++ typeText ret
    -- (a name that starts with a small letter has a ` before it, so that it is not read as a size)
    TNamed name -> if bareLower name then '`' : name else name
    TVariant name -> name
    TParam name -> '\'' : name
    TVar n -> '?' : show n
    TForall _ _ t -> typeText t

bareLower :: Name -> Bool
bareLower name = case name of
    c : rest -> isLower c && all isAlphaNum rest
    [] -> False

-- The struct and the arguments that a name is the instance of
instanceOf :: Name -> Maybe (Name, [Arg])
instanceOf name =
    case break (== '<') name of
        (base, '<' : rest) | not (null base), not (null rest), last rest == '>' -> mapM readArg (splitArgs (init rest)) >>= \args -> Just (base, args)
        _ -> Nothing
  where
    readArg text
        | text == "?" = Just (ArgSize SizeAny)
        | not (null text) && all isDigit text = Just (ArgSize (SizeConst (read text)))
        | ('_' : digits) <- text, not (null digits), all isDigit digits = Just (ArgSize (SizeVar (read digits)))
        | all isAlphaNum text, c : _ <- text, isLower c = Just (ArgSize (SizeParam text))
        | otherwise = case readType text of
            Just (ty, "") -> Just (ArgType ty)
            _ -> Nothing

-- The pieces of the arguments of an instance, which a comma separates where no < > or ( ) is open
splitArgs :: String -> [String]
splitArgs = go (0 :: Int) ""
  where
    go _ acc [] = [reverse acc]
    go depth acc ('-' : '>' : rest) = go depth ('>' : '-' : acc) rest
    go depth acc (c : rest)
        | c `elem` "<(" = go (depth + 1) (c : acc) rest
        | c `elem` ">)" = go (depth - 1) (c : acc) rest
        | c == ',' && depth == 0 = reverse acc : go depth "" (dropWhile (== ' ') rest)
        | otherwise = go depth (c : acc) rest

-- A type from the text that typeText wrote, and what follows it
readType :: String -> Maybe (Type, String)
readType text =
    case text of
        '&' : rest -> (\(t, r) -> (TRef t, r)) <$> readType rest
        '\'' : rest -> let (name, r) = span isAlphaNum rest in if null name then Nothing else Just (TParam name, r)
        '`' : rest -> let (name, r) = span isAlphaNum rest in if null name then Nothing else Just (TNamed name, r)
        '?' : rest -> let (digits, r) = span isDigit rest in if null digits then Nothing else Just (TVar (read digits), r)
        'f' : 'n' : '(' : rest -> do
            (args, afterArgs) <- readTypes rest
            ret <- stripPrefix' ") -> " afterArgs
            (t, r) <- readType ret
            Just (TFn args t, r)
        _ -> do
            let (name, afterName) = span (\c -> isAlphaNum c || c == ':') text
            if null name
                then Nothing
                else case afterName of
                    '<' : _ -> do
                        let (inner, afterInner) = bracketed afterName
                        let full = name ++ inner
                        case name of
                            "List" -> readOne inner >>= \t -> Just (TList t, afterInner)
                            "Box" -> readOne inner >>= \t -> Just (TBox t, afterInner)
                            "Array" -> readArray inner >>= \t -> Just (t, afterInner)
                            _ -> Just (TNamed full, afterInner)
                    _ -> case name of
                        "Int" -> Just (TInt, afterName)
                        "Byte" -> Just (TByte, afterName)
                        "Bool" -> Just (TBool, afterName)
                        _ | "::" `isInfixOf'` name -> Just (TVariant name, afterName)
                        _ -> Just (TNamed name, afterName)
  where
    isInfixOf' needle hay = any (isPrefixOf needle) (tails' hay)
    tails' [] = [[]]
    tails' s@(_ : t) = s : tails' t
    stripPrefix' prefix s = if prefix `isPrefixOf` s then Just (drop (length prefix) s) else Nothing
    -- the text of a < > group from its first < to its matching >, and what follows
    bracketed s = go (0 :: Int) "" s
      where
        go _ acc [] = (reverse acc, [])
        go depth acc ('-' : '>' : rest) = go depth ('>' : '-' : acc) rest
        go depth acc (c : rest)
            | c == '<' = go (depth + 1) (c : acc) rest
            | c == '>' = if depth == 1 then (reverse (c : acc), rest) else go (depth - 1) (c : acc) rest
            | otherwise = go depth (c : acc) rest
    readOne inner = case readType (init (drop 1 inner)) of
        Just (t, "") -> Just t
        _ -> Nothing
    readArray inner = case splitArgs (init (drop 1 inner)) of
        [element, size] -> do
            (t, rest) <- readType element
            if null rest then Just (TArrayOf t (readSize size)) else Nothing
        _ -> Nothing
    readSize size
        | size == "?" = SizeAny
        | not (null size) && all isDigit size = SizeConst (read size)
        | ('_' : digits) <- size, not (null digits), all isDigit digits = SizeVar (read digits)
        | otherwise = SizeParam size
    readTypes s = case s of
        ')' : rest -> Just ([], ')' : rest)
        _ -> do
            (t, rest) <- readType s
            case rest of
                ',' : ' ' : more -> readTypes more >>= \(ts, r) -> Just (t : ts, r)
                _ -> Just ([t], rest)

-- The fields of a struct with parameters, for the arguments it is given: the sizes and the types are put where the parameters are.
-- Nothing if there are not as many, or one is a size where a type is wanted.
instanceFields :: [Variable] -> [Arg] -> [(Variable, Type)] -> Maybe [(Variable, Type)]
instanceFields params args fields
    | length params /= length args = Nothing
    | otherwise = do
        pairs <- mapM pair (zip params args)
        let sizes = [(p, s) | (p, Left s) <- pairs]
            types = [(p, t) | (p, Right t) <- pairs]
        Just [(f, substitute sizes types t) | (f, t) <- fields]
  where
    pair (p, ArgSize s) | not (isTypeName p) = Just (p, Left s)
    pair (p, ArgType t) | isTypeName p = Just (p, Right t)
    pair _ = Nothing

-- Whether a type mentions a size parameter or a type parameter, and so is a name that a function with them has
mentionsParameter :: Type -> Bool
mentionsParameter ty = case ty of
    TParam _ -> True
    TList t -> mentionsParameter t
    TBox t -> mentionsParameter t
    TRef t -> mentionsParameter t
    TArrayOf t size -> mentionsParameter t || sizeParam size
    TFn args ret -> any mentionsParameter (ret : args)
    TNamed name | Just (_, args) <- instanceOf name -> any argParameter args
    _ -> False
  where
    sizeParam (SizeParam _) = True
    sizeParam _ = False
    argParameter (ArgSize size) = sizeParam size
    argParameter (ArgType t) = mentionsParameter t

-- The type with each size parameter of the list replaced by the size (also in the name of an instance of a struct with sizes)
substSizes :: [(Variable, Size)] -> Type -> Type
substSizes sizes = substitute sizes []

-- The type with each size parameter and each type parameter of the lists replaced by what a call gave
substitute :: [(Variable, Size)] -> [(Variable, Type)] -> Type -> Type
substitute sizes types = go
  where
    go ty = case ty of
        TList t -> TList (go t)
        TArrayOf t size -> TArrayOf (go t) (sized size)
        TBox t -> TBox (go t)
        TRef t -> TRef (go t)
        TFn args ret -> TFn (map go args) (go ret)
        TParam name | Just t <- lookup name types -> t
        TForall ss ts t -> TForall ss ts (substitute [(n, s) | (n, s) <- sizes, n `notElem` ss] [(n, u) | (n, u) <- types, n `notElem` ts] t)
        TNamed name | Just (base, args) <- instanceOf name -> TNamed (instanceName base (map arg args))
        _ -> ty
    arg (ArgSize size) = ArgSize (sized size)
    arg (ArgType t) = ArgType (go t)
    sized (SizeParam n) | Just size <- lookup n sizes = size
    sized size = size

-- An array of a size that is a constant, which is every array there can be in a program that runs
pattern TArray :: Type -> Integer -> Type
pattern TArray t n = TArrayOf t (SizeConst n)

-- The declared parameter types and return type of a user function, its size parameters, which are the last parameters (of type Int),
-- given by the call and not written in it, and its type parameters, which a call gives too
data Signature = Signature [Type] Type [Variable] [Variable] deriving (Show, Eq, Ord)

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
    | -- struct Name<sizes> { field: Type, ... }; it only matters to the type checker. A struct with sizes (`struct Packet<n> { body:
      -- Array<Int, n> }`) is a type for each list of sizes, `Packet<4>`: see instanceName. The last field is the invariant, `struct Vec<T> {
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
      ImplDef (Maybe Name) [Arg] Name Name [Statement]
    | -- fn f<S: Sequence<Int>, T>(...) ...: a function whose type parameters have bounds (`BoundedDef [(S, Sequence, [Int])] (the function)`),
      -- which the type checker keeps as a template and makes a function of for each type it is called with (see TypeCheck.templateCall).
      -- It does not reach the lowering.
      BoundedDef [Bound] Statement
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
