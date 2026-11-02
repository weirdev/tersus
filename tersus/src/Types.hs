{-# LANGUAGE PatternSynonyms #-}

module Types where

import Data.Char (isAlphaNum, isDigit, isLower, isUpper)
import Data.List (intercalate, stripPrefix)

type Variable = String
type Name = String

-- This will need to be made more robust, for now A=abstract, C=concrete, FApp = Iota1 = Funct(Iota2)
data Rel = Eq | NotEq | Lt | Gt | LtEq | GtEq deriving (Eq, Ord, Show, Read)

-- Ctor builds a struct from its fields, given in declaration order, and Field reads one by name. The Field of a `..base` update names the struct the base must be.
-- A struct literal is the application of its Ctor, so the proof engine sees structs as ordinary terms.
data BuiltinFunct
    = Size | First | Last | Get | Push | Pop | Set | Plus | Minus | Times | Div | Mod
    | -- NewArray n x: an array of n copies of x, n being a constant. ArrayFrom is the array that a literal list of constants makes (`#[1, 2]`).
      NewArray | ArrayFrom | ArrayFromList
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
    | -- CloneOf x: clone(x), a copy of x, which has its value. It is the one place a program says that a value is copied.
      CloneOf
    | -- References (REFERENCES.md, stages 2 and 3): BorrowOf place is `&place`, a read reference to a place; BorrowMutOf
      -- place is `&mut place`, the exclusive reference to it; DerefOf r is `*r`, the value at the place a reference is to.
      -- Only the checker writes them. A place is a variable, a field of one, an element of one, or through a reference.
      BorrowOf
    | BorrowMutOf
    | DerefOf
    | -- OldOf e in a postcondition is `old(e)`: the entry value of the place e is of, which only a contract may write.
      -- The checker replaces it with the entry snapshot of an update parameter before the lowering sees it.
      OldOf
    | -- Addresses and permissions (POINTERS.md). An address is a word that allows nothing by itself; every operation on memory is given
      -- the permission to it (a Block, a ghost value), and its contract says what the permission has to allow and what the new one says.
      -- These need no permission: the null address, an address i slots further on, the same address of another type, and an address as
      -- a number and back.
      AddrNull
    | AddrOffset
    | AddrCast
    | AddrToInt
    | AddrFromInt
    | -- The operations on memory, as the MIR has them: n new slots (the address; BlockNew is the permission), the value in a slot (a view of
      -- the permission), a value written into an empty slot (the permission after), a value taken out of a slot (BlockTaken is the
      -- permission after), the value in a slot or in a run of slots dropped where it is (the permission after), the slots moved to an
      -- allocation of another size (the address; BlockResized is the permission), and an allocation given back (0).
      AddrAlloc
    | AddrGet
    | AddrWrite
    | AddrTake
    | AddrDropValue
    | AddrDropRange
    | AddrResize
    | AddrFree
    | -- What a program writes for those that give two things, `(p, b) = Addr::alloc(n)`: the lowering makes each the two operations and a tuple.
      -- Block::split is the same of two ghost operations.
      AllocPair
    | TakePair
    | ResizePair
    | SplitPair
    | -- The ghost operations, which make a permission and do nothing when the program runs (they are erased with the permissions)
      BlockNew
    | BlockTaken
    | BlockResized
    | BlockSplitLo
    | BlockSplitHi
    | BlockJoin
    | BlockAssume
    | BlockCast
    | -- What the validator knows of a permission, which a contract or an affirm says (`base(b)`, `cap(b)`, `filled(b, i)` is
      -- get(BlockFilled(b), i) and `at(b, i)` get(BlockContents(b), i), so what is known of arrays is known of them, `origin(b)`, and the
      -- place of the block in its allocation and the size of the allocation, of which `whole(b)` is made). They cannot be called in code.
      BlockBase
    | BlockCap
    | BlockFilled
    | BlockContents
    | BlockOrigin
    | BlockStart
    | BlockExtent
    | -- count(b): the number of slots of the block that are filled, which every operation keeps, so that a block known to have none
      -- filled (to be freed) is a sum and not a forall
      BlockCount
    | -- Uninit<T> (POINTERS.md): Uninit::empty(), Uninit::new(x), Uninit::get(u) (a view, of one that is filled), Uninit::take(u) (the value of
      -- one that is filled, which is moved out) and Uninit::discard(u) (an empty one, used up); filled(u) and at(u) are what a proof knows of one
      UninitEmpty
    | UninitNew
    | UninitGet
    | UninitTake
    | UninitDiscard
    | UninitFilled
    | UninitAt
    | -- ToWord signed bits x: I32::from(x) and the others, the Int x as a fixed-width integer (x in its range). toInt widens one back (FromByte).
      ToWord Bool Integer
    | -- replace(a, i, x): x put in element i of a list or an array, and the element that was there, as a tuple (set(a, i, x), get(a, i))
      Replace
    | Rel Rel
    | -- a && b, a || b and !a: the connectives of a condition. The lowering turns them into the jumps they stand for (a && b does not
      -- evaluate b when a is false), so only the checker, the evaluation of a constant and the printer see them.
      And
    | Or
    | Not
    | -- Within a b: a is a field of b, or a field of a field, and so on. Never parsed: it is how the validator checks
      -- that what a loop or function says shrinks has done so.
      Within
    | Ctor Name [Arg] [Variable]
    | Field (Maybe Name) Variable
    | -- Is Ctor tests which variant an enum value is; Project Ctor reads a field of a value known to be that variant
      Is Name
    | Project Name Variable
    | -- Cast Ctor reinterprets an enum value as that variant so its fields can be read. The validator demands the proof
      -- that the value is that variant; evaluation does nothing, and a wrong cast is undefined behaviour.
      Cast Name
    deriving (Show, Eq, Ord, Read)

-- The builtins whose value is something outside the program (the input, the arguments): a call of one is not a function of its arguments,
-- so a validator does not say that two calls are the same value, and a proof may not call one
readsWorld :: BuiltinFunct -> Bool
-- An allocation is new each time, so a call of one that makes one is not a function of its arguments either (two blocks of 4 slots are not the same).
readsWorld b = b `elem` [ReadByte, ArgCount, ArgByte, PathByte, FileLoad, FileByte, StoreByte, FileStore, AddrAlloc, AddrResize, BlockAssume]

-- The builtins of permissions that give a ghost value or speak of one: they are not in the program that runs
ghostBuiltin :: BuiltinFunct -> Bool
ghostBuiltin b = b `elem` [BlockNew, BlockTaken, BlockResized, BlockSplitLo, BlockSplitHi, BlockJoin, BlockAssume, BlockCast, BlockBase, BlockCap, BlockFilled, BlockContents, BlockOrigin, BlockStart, BlockExtent, BlockCount]


-- The types the checker (TypeCheck) knows. They are erased after checking: validation and evaluation never
-- look at them. TVar is the checker's own unknown and is never written by a program.
-- TArrayOf element size: a sequence of that many elements held inline, wherever the array is made (a local, a parameter, a result
-- or an element of a bigger array), with no pointer to it. The size is part of the type.
data Type = TInt | TByte | TBool
    | -- A fixed-width integer (POINTERS.md, Layout): TWord signed bits is I8, I16, I32 (signed) or U16, U32. Arithmetic and order are on Int:
      -- toInt widens one, and I32::from(x) and the others narrow an Int with its range proved, as toByte does. Natively it is as many bytes in
      -- memory, and a word in a register.
      TWord Bool Integer
    | TList Type | TArrayOf Type Size | TBox Type | TFn [Type] Type | TNamed Name [Arg] | TVariant Name | TVar Int
    | -- A function with size parameters (`fn dot<n>(a: Array<Int, n>, ...)`): the type of the function for any values of the sizes. A call
      -- gives each its value, so a use of one that is not a call has no type.
      TForall [Variable] [Variable] Type
    | -- A type parameter of a function (`T` in `fn first<T>(a: &List<T>) -> T`): a type that the function knows nothing of, which a call gives
      TParam Name
    | -- The address of a T, or null (POINTERS.md): a word that can be copied, compared, offset and kept anywhere, and allows nothing by itself
      TAddr Type
    | -- The permission to a run of slots of T: a ghost value, which only the validator has (it is erased before the program runs), and linear, so
      -- there is only ever one for a piece of memory. Every operation on memory needs it.
      TBlock Type
    | -- Room for one T that may hold nothing (POINTERS.md, Uninit): laid out as a T, with no tag and no drop of its own. What the validator
      -- knows of it is whether it is filled and what it holds. One of a T that owns something is linear.
      TUninit Type
    | -- A parameter that the function only reads, so a call does not give it a copy (`fn sum(a: &List<Int>)`). Only a parameter has one:
      -- in the function it is its type, a value it cannot assign, and a call gives it the value as it is.
      TRef Type
    | -- A reference that may update its referent (REFERENCES.md): as a parameter it is lent exclusively, as a local it is
      -- made by `&mut place`. It is never a result, a field or an element in stages 1 to 3 (escaping references are stage 4).
      TMutRef Type
    deriving (Show, Eq, Ord, Read)

-- The size argument of a type: a constant, or `?`, a size that the type does not say. A type with a `?` is unsized: its size is
-- known only to something that holds a pointer to it and carries the size along (a Box, later), so it cannot be held by value.
-- `Array<Int>` is `Array<Int, ?>`: a size that is left out is `?`.
-- A name is a size parameter of the function (`n` in `fn dot<n>`), which stands for a constant that its callers give; SizeVar is the
-- checker's own unknown, for the size a call gives a parameter, and is never written by a program.
data Size = SizeConst Integer | SizeAny | SizeParam Name | SizeVar Int
    deriving (Show, Eq, Ord, Read)

-- What a struct with parameters is given: a size, or a type
data Arg = ArgSize Size | ArgType Type
    deriving (Show, Eq, Ord, Read)

-- A parameter that starts with a capital letter is a type, and any other is a size
isTypeName :: Variable -> Bool
isTypeName name = case name of
    c : _ -> isUpper c
    [] -> False

-- The type that a struct with parameters is for a list of sizes and types (`Packet<4>`, `Vec<Int, 3>`, and `Vec<'T, n>` in a function that has
-- the type T and the size n) is a struct of its own, carrying its arguments structurally: `TNamed "Vec" [ArgType TInt, ArgSize (SizeConst 3)]`.
-- Everything after the checker sees an ordinary struct; the base and arguments are how the checker and MirMono find the declaration again.
-- The rendered name of an instance, for map keys, data names and human-readable messages. It is never parsed back.
instanceName :: Name -> [Arg] -> Name
instanceName base [] = base
instanceName base args = base ++ "<" ++ intercalate ", " (map renderArg args) ++ ">"

renderArg :: Arg -> String
renderArg (ArgSize size) = renderSizeForName size
renderArg (ArgType ty) = renderTypeForName ty

renderSizeForName :: Size -> String
renderSizeForName (SizeConst n) = show n
renderSizeForName SizeAny = "?"
renderSizeForName (SizeParam name) = name
renderSizeForName (SizeVar n) = "_" ++ show n

-- A type as the rendered name of an instance writes it (a type parameter has a ' before it, so that it is not a struct, and an unknown has a ?)
renderTypeForName :: Type -> String
renderTypeForName ty = case ty of
    TInt -> "Int"
    TByte -> "Byte"
    TBool -> "Bool"
    TWord signed bits -> wordName signed bits
    TList t -> "List<" ++ renderTypeForName t ++ ">"
    TBox t -> "Box<" ++ renderTypeForName t ++ ">"
    TAddr t -> "Addr<" ++ renderTypeForName t ++ ">"
    TBlock t -> "Block<" ++ renderTypeForName t ++ ">"
    TUninit t -> "Uninit<" ++ renderTypeForName t ++ ">"
    TRef t -> "&" ++ renderTypeForName t
    TMutRef t -> "&mut " ++ renderTypeForName t
    TArrayOf t size -> "Array<" ++ renderTypeForName t ++ ", " ++ renderSizeForName size ++ ">"
    TFn args ret -> "fn(" ++ intercalate ", " (map renderTypeForName args) ++ ") -> " ++ renderTypeForName ret
    -- (a name that starts with a small letter has a ` before it, so that it is not read as a size)
    TNamed base args -> if null args && bareLower base then '`' : base else instanceName base args
    TVariant name -> name
    TParam name -> '\'' : name
    TVar n -> '?' : show n
    TForall _ _ t -> renderTypeForName t

bareLower :: Name -> Bool
bareLower name = case name of
    c : rest -> isLower c && all isAlphaNum rest
    [] -> False

-- The base of a rendered instance name or of any name, without parsing its arguments
baseNameOf :: Name -> Name
baseNameOf = takeWhile (/= '<')

-- Whether a type is the named type a rendered name denotes
namedMatches :: Type -> Name -> Bool
namedMatches (TNamed base args) name = instanceName base args == name
namedMatches _ _ = False

-- A tuple, `(A, B)`, is an instance of a struct that the language declares for each number of parts, `Tuple2<A, B>`, whose fields are
-- named by their places, `0` and `1` (read as `t.0`). Its literal `(a, b)` is a literal of that struct whose types are those of the parts.
tupleBase :: Int -> Name
tupleBase n = "Tuple" ++ show n

tupleType :: [Type] -> Type
tupleType parts = TNamed (tupleBase (length parts)) (map ArgType parts)

-- The parameters and fields of the struct of the tuples of a number of parts, by its name
tupleGeneric :: Name -> Maybe ([Variable], [(Variable, Type)])
tupleGeneric base = case stripPrefix "Tuple" base of
    Just digits | not (null digits), all isDigit digits, take 1 digits /= "0", n <- read digits, n >= (2 :: Int), n <= 16 ->
        let params = ["T" ++ show i | i <- [0 .. n - 1]]
         in Just (params, [(show i, TParam p) | (i, p) <- zip [0 :: Int ..] params])
    _ -> Nothing

-- The types of the parts of a tuple type
tupleParts :: Type -> Maybe [Type]
tupleParts (TNamed base args)
    | Just _ <- tupleGeneric base = mapM argType args
  where
    argType (ArgType t) = Just t
    argType _ = Nothing
tupleParts _ = Nothing

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
    TAddr t -> mentionsParameter t
    TBlock t -> mentionsParameter t
    TUninit t -> mentionsParameter t
    TRef t -> mentionsParameter t
    TMutRef t -> mentionsParameter t
    TArrayOf t size -> mentionsParameter t || sizeParam size
    TFn args ret -> any mentionsParameter (ret : args)
    TNamed _ args -> any argParameter args
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
        TAddr t -> TAddr (go t)
        TBlock t -> TBlock (go t)
        TUninit t -> TUninit (go t)
        TRef t -> TRef (go t)
        TMutRef t -> TMutRef (go t)
        TFn args ret -> TFn (map go args) (go ret)
        TParam name | Just t <- lookup name types -> t
        TForall ss ts t -> TForall ss ts (substitute [(n, s) | (n, s) <- sizes, n `notElem` ss] [(n, u) | (n, u) <- types, n `notElem` ts] t)
        TNamed base args -> TNamed base (map arg args)
        _ -> ty
    arg (ArgSize size) = ArgSize (sized size)
    arg (ArgType t) = ArgType (go t)
    sized (SizeParam n) | Just size <- lookup n sizes = size
    sized size = size

-- The name of a fixed-width integer type, and the type of a name (I64 is Int and U8 is Byte)
wordName :: Bool -> Integer -> String
wordName signed bits = (if signed then "I" else "U") ++ show bits

wordType :: String -> Maybe Type
wordType name = case name of
    "I8" -> Just (TWord True 8)
    "I16" -> Just (TWord True 16)
    "I32" -> Just (TWord True 32)
    "I64" -> Just TInt
    "U8" -> Just TByte
    "U16" -> Just (TWord False 16)
    "U32" -> Just (TWord False 32)
    _ -> Nothing

-- The values of a fixed-width integer type: the least, and one more than the greatest
wordRange :: Bool -> Integer -> (Integer, Integer)
wordRange signed bits = if signed then (negate (2 ^ (bits - 1)), 2 ^ (bits - 1)) else (0, 2 ^ bits)

-- An array of a size that is a constant, which is every array there can be in a program that runs
pattern TArray :: Type -> Integer -> Type
pattern TArray t n = TArrayOf t (SizeConst n)

-- The declared parameter types and return type of a user function, its size parameters, which are the last parameters (of type Int),
-- given by the call and not written in it, and its type parameters, which a call gives too
data Signature = Signature [Type] Type [Variable] [Variable] [Variable] [Variable] deriving (Show, Eq, Ord, Read) -- parameter types, return type, size parameters, type parameters, writes footprint, and the parameters a reference result is from (REFERENCES.md)

