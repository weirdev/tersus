module LlvmEmit
    ( emitProgram
    ) where

import Data.List (elemIndex, intercalate, nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)

import Mir
import MirOwnership (insertOwnership)
import MirVerify (verifyProgram)
import Pretty (renderType)
import TersusTypes (Name, Rel (..), Type (..), Variable)
import Utils

-- Lowers the MIR to LLVM IR as text (a .ll file), which clang compiles together with the runtime of LlvmRuntime.
--
-- Every local is a stack slot (alloca) that the statements load and store, so the blocks need no phis and `mem2reg` builds
-- them. A function of the program is an internal function `@"fn.<name>"`; the statements of `main` are `@tersus_main`, which
-- the C-level `@main` runs and then prints what it returns.
--
-- Contracts the validator proved (a divisor that is not 0, an index in range, a list that is not empty) are not checked: the
-- operations assume them, as `unreachable` would. What the language itself defines does stop the program: an Int that
-- leaves its 64 bits, with the same message as the executor of the MIR.
--
-- A program that ends without a `return` on some path (`if c { return 1; };`) returns nothing on that path, so the function
-- of `main` returns the value with a flag that says whether `_0` was assigned, and only then is the value printed.
--
-- Int is i64 and Bool is i1. A list is a pointer to `{ rc, len, cap, elements }` (24 bytes of header, then one 8-byte slot per
-- element: an Int, a Bool as 0 or 1, or a pointer), made by the runtime, which `push` and `set` copy. A struct or an enum value
-- is a pointer to `{ rc, tag, fields }` (16 bytes of header, then a slot per field of its variant; the tag is the position of
-- the variant in the enum, and 0 for a struct), so that a type that contains itself needs no layout of its own. A function
-- value is the address of the function. An array is not a value of the heap: it is the words of its elements in the slot of
-- its local (`[N x i64]`), its value is the address of the first, and it is copied by `memcpy`; a function copies an array it is
-- given, and writes an array it returns into room the caller gives (the first parameter). The runtime prints, compares, copies and frees values by a descriptor of their type, a
-- constant global `@"type.<type>"`.
--
-- The program is the owned MIR of MirOwnership, which says who owns each value of the heap. A local that holds a value it
-- owns is a pointer that is null when it holds none: `Move` reads it and stores null, `Drop` frees what it holds and stores
-- null, and assigning a local frees what it held. A `Peek` local only looks at a value, and is neither freed nor assigned
-- over.

-- The program is given as the validated MIR; who owns each value is added here (MirOwnership), since the code that is made
-- frees values and changes lists in place on the strength of it
emitProgram :: Program -> Result String String
emitProgram validated =
    verifyProgram (insertOwnership validated) `bindResult` \_ -> emitOwned (insertOwnership validated)

emitOwned :: Program -> Result String String
emitOwned program =
    flatResultMap (\(name, fn) -> emitFunction program False (functionSymbol name) fn) (Map.toList (progFunctions program))
        `bindResult` \functions ->
            emitFunction program True "@tersus_main" (progMain program) `bindResult` \mainFunction ->
                entryPoint program (progMain program) `bindResult` \(entry, entryTypes) ->
                    let bodies = map fst functions ++ [fst mainFunction, entry]
                        types = closeTypes program (concatMap snd functions ++ snd mainFunction ++ entryTypes)
                     in Ok (unlines (concat (declarations : typeDescriptors program types : map (++ [""]) bodies)))

declarations :: [String]
declarations =
    [ "declare {i64, i1} @llvm.sadd.with.overflow.i64(i64, i64)"
    , "declare {i64, i1} @llvm.ssub.with.overflow.i64(i64, i64)"
    , "declare {i64, i1} @llvm.smul.with.overflow.i64(i64, i64)"
    , "declare void @tersus_overflow() noreturn"
    , "declare void @tersus_print(ptr, i64)"
    , "declare i32 @tersus_equal(ptr, i64, i64)"
    , "declare ptr @tersus_list_new(i64)"
    , "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)"
    , "declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)"
    , "declare ptr @tersus_list_push(ptr, i64)"
    , "declare ptr @tersus_list_set(ptr, i64, i64, ptr)"
    , "declare ptr @tersus_clone(ptr, ptr)"
    , "declare void @tersus_drop(ptr, ptr)"
    , "declare ptr @tersus_data_new(i64, i64)"
    , ""
    ]

-- The C-level main: runs the program and prints its return value, if it returned one
entryPoint :: Program -> Function -> Result ([String], [Type]) String
entryPoint program fn =
    case fnReturns fn of
        Nothing -> Ok (wrap ["call void @tersus_main()", "ret i32 0"], [])
        -- an array is made in a frame, so the program is given room for it, and prints it from there
        Just ty | isArray ty ->
            Ok
                ( wrap
                    [ "%out = alloca [" ++ show (slotsOf ty) ++ " x i64]"
                    , "%ok = call i1 @tersus_main(ptr %out)"
                    , "br i1 %ok, label %print, label %done"
                    , "print:"
                    , "%w = ptrtoint ptr %out to i64"
                    , "call void @tersus_print(ptr " ++ typeSymbol program ty ++ ", i64 %w)"
                    , "br label %done"
                    , "done:"
                    , "ret i32 0"
                    ]
                , [ty]
                )
        Just ty ->
            llvmType ty `bindResult` \t ->
                let result = resultStruct t
                    (convert, word) = case ty of
                        TInt -> ([], "%v")
                        TBool -> (["%w = zext i1 %v to i64"], "%w")
                        _ -> (["%w = ptrtoint ptr %v to i64"], "%w")
                 in Ok
                        ( wrap
                            ( [ "%r = call " ++ result ++ " @tersus_main()"
                              , "%ok = extractvalue " ++ result ++ " %r, 1"
                              , "br i1 %ok, label %print, label %done"
                              , "print:"
                              , "%v = extractvalue " ++ result ++ " %r, 0"
                              ]
                                ++ convert
                                ++ ["call void @tersus_print(ptr " ++ typeSymbol program ty ++ ", i64 " ++ word ++ ")"]
                                ++ ["call void @tersus_drop(ptr " ++ typeSymbol program ty ++ ", ptr %v)" | isPointer ty]
                                ++ ["br label %done", "done:", "ret i32 0"]
                            )
                        , [ty]
                        )
  where
    wrap body = ["define i32 @main() {"] ++ map indent body ++ ["}"]
    indent l = if last l == ':' then l else "    " ++ l

-- What the function of `main` returns when the program can return a value: the value, and whether it was assigned
resultStruct :: String -> String
resultStruct t = "{ " ++ t ++ ", i1 }"

-- The types the runtime needs a descriptor of, and the types inside them (a type that contains itself is there once)
closeTypes :: Program -> [Type] -> [Type]
closeTypes program = go [] . map (canonical program)
  where
    go seen [] = reverse seen
    go seen (ty : rest)
        | ty `elem` seen = go seen rest
        | otherwise = go (ty : seen) (parts ty ++ rest)
    parts (TList t) = [canonical program t]
    parts (TArray t _) = [canonical program t]
    parts (TNamed n) = [canonical program t | (_, fields) <- variantsOf program n, (_, t) <- fields]
    parts _ = []

-- A value of a variant has the representation of its enum, so one descriptor serves both
canonical :: Program -> Type -> Type
canonical program (TVariant v) = maybe (TVariant v) TNamed (enumOf program v)
canonical _ ty = ty

-- A constant global for each type: its kind (0 Int, 1 Bool, 2 List, 3 struct or enum, 4 function) and what the runtime
-- needs to walk a value: the descriptor of the elements of a list, or the variants of a struct or enum with the names and
-- the descriptors of their fields
typeDescriptors :: Program -> [Type] -> [String]
typeDescriptors program types =
    ["%tersus.type = type { i64, ptr }"]
        ++ [typeSymbol program ty ++ " = private constant %tersus.type " ++ body ty | ty <- types]
        ++ concat [dataDescriptor n | TNamed n <- types]
        ++ [ global "array." (renderType ty) ++ " = private constant { i64, ptr } { i64 " ++ show n ++ ", ptr " ++ typeSymbol program t ++ " }"
           | ty@(TArray t n) <- types
           ]
        ++ [ global "str." name ++ " = private constant [" ++ show (byteLength name + 1) ++ " x i8] c\"" ++ escaped name ++ "\\00\""
           | name <- nub (concat [v : map fst fields | TNamed n <- types, (v, fields) <- variantsOf program n])
           ]
        ++ [""]
  where
    body TInt = "{ i64 0, ptr null }"
    body TBool = "{ i64 1, ptr null }"
    body (TList t) = "{ i64 2, ptr " ++ typeSymbol program t ++ " }"
    body ty@TArray{} = "{ i64 5, ptr " ++ global "array." (renderType ty) ++ " }"
    body (TNamed n) = "{ i64 3, ptr " ++ global "data." n ++ " }"
    body (TFn _ _) = "{ i64 4, ptr null }"
    body _ = "{ i64 -1, ptr null }"
    dataDescriptor n =
        let variants = variantsOf program n
         in [ global "data." n ++ " = private constant { i64, ptr } { i64 " ++ show (length variants) ++ ", ptr " ++ global "variants." n ++ " }"
            , global "variants." n ++ " = private constant [" ++ show (length variants) ++ " x { ptr, i64, ptr }] ["
                ++ intercalate ", " ["{ ptr, i64, ptr } { ptr " ++ global "str." v ++ ", i64 " ++ show (length fields) ++ ", ptr " ++ (if null fields then "null" else global "fields." v) ++ " }" | (v, fields) <- variants]
                ++ "]"
            ]
                ++ [ global "fields." v ++ " = private constant [" ++ show (length fields) ++ " x { ptr, ptr }] ["
                        ++ intercalate ", " ["{ ptr, ptr } { ptr " ++ global "str." f ++ ", ptr " ++ typeSymbol program t ++ " }" | (f, t) <- fields]
                        ++ "]"
                   | (v, fields) <- variants
                   , not (null fields)
                   ]

typeSymbol :: Program -> Type -> String
typeSymbol program ty = global "type." (renderType (canonical program ty))

-- The name of a global: quoted, so that any name will do
global :: String -> String -> String
global prefix name = "@\"" ++ prefix ++ escaped name ++ "\""

-- A name as LLVM writes it in quotes and in a string: its UTF-8 bytes, those that are printable ASCII as they are and the
-- others (and `"` and `\`) as `\hh`. The program may name things with any letter, and the file is ASCII whatever the encoding.
escaped :: String -> String
escaped = concatMap byteText . concatMap utf8
  where
    byteText b
        | b >= 32 && b < 127 && b /= 34 && b /= 92 = [toEnum b]
        | otherwise = ['\\', hexDigit (b `div` 16), hexDigit (b `mod` 16)]
    hexDigit d = "0123456789ABCDEF" !! d

-- The number of bytes of a name
byteLength :: String -> Int
byteLength = length . concatMap utf8

utf8 :: Char -> [Int]
utf8 c
    | n < 0x80 = [n]
    | n < 0x800 = [0xC0 + n `div` 64, continuation n]
    | n < 0x10000 = [0xE0 + n `div` 4096, continuation (n `div` 64), continuation n]
    | otherwise = [0xF0 + n `div` 262144, continuation (n `div` 4096), continuation (n `div` 64), continuation n]
  where
    n = fromEnum c
    continuation x = 0x80 + x `mod` 64

-- The variants of a struct or an enum: a struct is one variant, named as it is
variantsOf :: Program -> Name -> [(Name, [(Variable, Type)])]
variantsOf program n =
    case Map.lookup n (progTypes program) of
        Just (StructDecl fields) -> [(n, fields)]
        Just (EnumDecl variants) -> variants
        Nothing -> []

-- The tag and the fields of what builds a value: a struct, or a variant (Enum::Variant)
constructor :: Program -> Name -> Maybe (Int, [(Variable, Type)])
constructor program name =
    case Map.lookup name (progTypes program) of
        Just (StructDecl fields) -> Just (0, fields)
        _ -> listToMaybe [(i, fields) | EnumDecl variants <- Map.elems (progTypes program), (i, (v, fields)) <- zip [0 ..] variants, v == name]

-- The enum that has the variant
enumOf :: Program -> Name -> Maybe Name
enumOf program v = listToMaybe [n | (n, EnumDecl variants) <- Map.toList (progTypes program), v `elem` map fst variants]

-- The type of a value that a struct or a variant builds
constructedType :: Program -> Name -> Type
constructedType program name =
    case Map.lookup name (progTypes program) of
        Just StructDecl{} -> TNamed name
        _ -> TVariant name

-- Generating the code of one function: a counter for the names of temporaries and labels, the lines so far (last first),
-- and the types whose descriptors the code refers to
data S = S {sCount :: Int, sLines :: [String], sTypes :: [Type], sProgram :: Program, sGlobals :: [String], sOwner :: Name}

newtype G a = G {runG :: S -> Result (a, S) String}

instance Functor G where
    fmap f (G g) = G (\s -> mapResult (\(a, s') -> (f a, s')) (g s))

instance Applicative G where
    pure a = G (\s -> Ok (a, s))
    G f <*> G g = G (\s -> f s `bindResult` \(h, s') -> mapResult (\(a, s'') -> (h a, s'')) (g s'))

instance Monad G where
    G g >>= f = G (\s -> g s `bindResult` \(a, s') -> runG (f a) s')

failG :: String -> G a
failG e = G (\_ -> Error e)

-- An instruction
emit :: String -> G ()
emit line = G (\s -> Ok ((), s{sLines = ("    " ++ line) : sLines s}))

-- The start of a block
label :: String -> G ()
label name = G (\s -> Ok ((), s{sLines = (name ++ ":") : sLines s}))

-- A name for a label that no other has
freshLabel :: String -> G String
freshLabel base = G (\s -> Ok (base ++ show (sCount s), s{sCount = sCount s + 1}))

-- An instruction that gives a value, and the name of that value
ins :: String -> String -> G String
ins base text = G (\s -> let name = "%" ++ base ++ show (sCount s) in Ok (name, s{sCount = sCount s + 1, sLines = ("    " ++ name ++ " = " ++ text) : sLines s}))

-- The descriptor of a type, which the program will have
descriptor :: Type -> G String
descriptor ty = G (\s -> Ok (typeSymbol (sProgram s) ty, s{sTypes = ty : sTypes s}))

programG :: G Program
programG = G (\s -> Ok (sProgram s, s))

-- The function of `main` (the entry) also keeps whether the return slot was assigned
emitFunction :: Program -> Bool -> String -> Function -> Result ([String], [Type]) String
emitFunction program entry symbol fn =
    inFunction (flatResultMap (localLlvmType fn) (fnParams fn)) `bindResult` \paramTypes ->
        inFunction (maybe (Ok "void") llvmType (fnReturns fn)) `bindResult` \valueType ->
            let returnsArray = maybe False isArray (fnReturns fn)
                -- (an array comes back in room that the caller gives, as the first parameter)
                returnType
                    | returnsArray = if entry then "i1" else "void"
                    | entry && fnReturns fn /= Nothing = resultStruct valueType
                    | otherwise = valueType
             in inFunction (flatResultMap (\(l, d) -> mapResult ((,) l) (storageType (localType d))) (Map.toList (fnLocals fn))) `bindResult` \localTypes ->
                    let params = intercalate ", " (["ptr %ret" | returnsArray] ++ [t ++ " %p." ++ localNumber p | (p, t) <- zip (fnParams fn) paramTypes])
                        header = "define internal " ++ returnType ++ " " ++ symbol ++ "(" ++ params ++ ") {"
                        prologue =
                            ["entry:"]
                                ++ ["    " ++ slot l ++ " = alloca " ++ t | (l, t) <- localTypes]
                                ++ ["    store ptr null, ptr " ++ slot l | (l, d) <- Map.toList (fnLocals fn), isPointer (localType d), l `notElem` fnParams fn]
                                ++ concat
                                    [ case Map.lookup p (fnLocals fn) of
                                        -- (an array is given by its address, and the function works on its own copy)
                                        Just d | isArray (localType d) -> ["    " ++ memcpyText (slot p) ("%p." ++ localNumber p) (8 * slotsOf (localType d))]
                                        _ -> ["    store " ++ t ++ " %p." ++ localNumber p ++ ", ptr " ++ slot p]
                                    | (p, t) <- zip (fnParams fn) paramTypes
                                    ]
                                ++ entryPrologue
                                ++ ["    br label %bb" ++ blockNumber (BlockId 0)]
                        entryPrologue =
                            if entry && fnReturns fn /= Nothing
                                then ["    %returned = alloca i1", "    store i1 false, ptr %returned"] ++ ["    store " ++ valueType ++ " " ++ zeroOf valueType ++ ", ptr " ++ slot (Local 0) | not returnsArray]
                                else []
                     in case runG (mapM_ (emitBlock program entry fn) (Map.toList (fnBlocks fn))) (S 0 [] [] program [] (fnName fn)) of
                            Error e -> Error ("In " ++ fnName fn ++ ": " ++ e)
                            Ok (_, s) ->
                                Ok (reverse (sGlobals s) ++ [header] ++ prologue ++ reverse (sLines s) ++ overflowBlock ++ ["}"], sTypes s)
  where
    inFunction r = case r of
        Error e -> Error ("In " ++ fnName fn ++ ": " ++ e)
        Ok a -> Ok a
    overflowBlock = ["overflow:", "    call void @tersus_overflow()", "    unreachable"]

-- The value a slot holds before anything is assigned to it
zeroOf :: String -> String
zeroOf "i1" = "false"
zeroOf "ptr" = "null"
zeroOf _ = "0"

emitBlock :: Program -> Bool -> Function -> (BlockId, BasicBlock) -> G ()
emitBlock program entry fn (b, BasicBlock stmts term) = do
    label ("bb" ++ blockNumber b)
    mapM_ (emitStatement entry fn) stmts
    emitTerminator program entry fn term

emitStatement :: Bool -> Function -> Statement -> G ()
emitStatement _ _ (Ghost _ _) = pure ()
emitStatement _ fn (Drop l) = do
    ty <- localTypeG fn l
    if isPointer ty
        then do
            dropSlot ty l
            emit ("store ptr null, ptr " ++ slot l)
        else pure ()
emitStatement _ fn (Peek dest rv) = do
    destType <- localTypeG fn dest
    result <- rvalue fn destType rv
    t <- typeG destType
    emit ("store " ++ t ++ " " ++ result ++ ", ptr " ++ slot dest)
emitStatement entry fn (Assign dest rv) = do
    destType <- localTypeG fn dest
    if isArray destType
        then do
            assignArray fn dest destType rv
            -- (in the entry, the return slot being assigned is what makes the program return a value)
            if entry && dest == Local 0 then emit "store i1 true, ptr %returned" else pure ()
        else do
            result <- rvalue fn destType rv
            storeResult entry fn dest result

-- The value of an rvalue, given the type of the local it is for (which says what a constant list holds)
rvalue :: Function -> Type -> Rvalue -> G String
rvalue fn destType rv =
    case rv of
        Use o -> operandAt fn destType o
        BinaryOp op a b -> do
            ty <- sharedType fn [a, b]
            x <- operandAt fn ty a
            y <- operandAt fn ty b
            binary op ty x y
        MakeList os -> case destType of
            TList t -> do
                list <- newList (length os)
                mapM_ (\(i, o) -> operandAt fn t o >>= storeElement t list (show i)) (zip [0 :: Int ..] os)
                pure list
            _ -> failG "A list literal must make a list"
        ListOp op os@(first : _) | isArrayOperand fn first -> arrayRead fn destType op os
        ListOp op os -> listOperation fn destType op os
        MakeData name fields -> do
            program <- programG
            (tag, declared) <- constructorG program name
            object <- newData tag (length declared)
            mapM_
                ( \(i, (f, t)) -> case lookup f fields of
                    Just o -> operandAt fn t o >>= storeSlot t object (dataHeader + 8 * i)
                    Nothing -> failG ("A field is missing: " ++ name ++ "." ++ f)
                )
                (zip [0 ..] declared)
            pure object
        ReadField o name field -> do
            program <- programG
            (_, declared) <- constructorG program name
            case elemIndex field (map fst declared) of
                Nothing -> failG ("Variant " ++ name ++ " has no field " ++ field)
                Just i -> do
                    object <- operandAt fn (constructedType program name) o
                    loadSlot (snd (declared !! i)) object (dataHeader + 8 * i)
        IsVariant o name -> do
            program <- programG
            (tag, _) <- constructorG program name
            object <- operandAt fn (constructedType program name) o
            p <- ins "p" ("getelementptr i8, ptr " ++ object ++ ", i64 8")
            found <- ins "t" ("load i64, ptr " ++ p)
            ins "c" ("icmp eq i64 " ++ found ++ ", " ++ show tag)
        -- the same value; the validator proved the variant
        AsVariant o name -> do
            program <- programG
            operandAt fn (constructedType program name) o
        Clone o -> do
            ty <- sharedType fn [o]
            value <- operandAt fn ty o
            d <- descriptor ty
            ins "k" ("call ptr @tersus_clone(ptr " ++ d ++ ", ptr " ++ value ++ ")")
        -- the field is moved out of the value: what it held is left holding nothing
        TakeField s name field -> do
            program <- programG
            (_, declared) <- constructorG program name
            case elemIndex field (map fst declared) of
                Nothing -> failG ("Variant " ++ name ++ " has no field " ++ field)
                Just i -> do
                    object <- operandAt fn (constructedType program name) (Copy s)
                    taken <- loadSlot (snd (declared !! i)) object (dataHeader + 8 * i)
                    p <- ins "p" ("getelementptr i8, ptr " ++ object ++ ", i64 " ++ show (dataHeader + 8 * i))
                    emit ("store ptr null, ptr " ++ p)
                    pure taken

newList :: Int -> G String
newList n = ins "l" ("call ptr @tersus_list_new(i64 " ++ show n ++ ")")

-- A struct or an enum value with room for its fields, which the caller fills in
newData :: Int -> Int -> G String
newData tag fields = ins "d" ("call ptr @tersus_data_new(i64 " ++ show tag ++ ", i64 " ++ show fields ++ ")")

-- The bytes before the first field of a struct or an enum value: the count and the tag
dataHeader :: Int
dataHeader = 16

constructorG :: Program -> Name -> G (Int, [(Variable, Type)])
constructorG program name = maybe (failG ("Unknown struct or variant: " ++ name)) pure (constructor program name)

-- A list operation, given the type of its result, which says what the list holds even when the operand is an empty constant.
-- The contracts (an index in range, a list that is not empty) are assumed.
listOperation :: Function -> Type -> ListOp -> [Operand] -> G String
listOperation fn destType op os =
    case (op, os) of
        (Length, [l]) -> listArg l >>= \(_, list) -> lengthOf list
        (First, [l]) -> listArg l >>= \(t, list) -> elementPtr list "0" >>= loadElement t
        (Last, [l]) -> do
            (t, list) <- listArg l
            n <- lengthOf list
            i <- ins "i" ("sub i64 " ++ n ++ ", 1")
            elementPtr list i >>= loadElement t
        (Get, [l, i]) -> do
            (t, list) <- listArg l
            index <- operandAt fn TInt i
            elementPtr list index >>= loadElement t
        (Push, [l, x]) -> do
            (t, list) <- listArg l
            word <- operandAt fn t x >>= toWord t
            ins "l" ("call ptr @tersus_list_push(ptr " ++ list ++ ", i64 " ++ word ++ ")")
        (Set, [l, i, x]) -> do
            (t, list) <- listArg l
            index <- operandAt fn TInt i
            word <- operandAt fn t x >>= toWord t
            d <- descriptor t
            ins "l" ("call ptr @tersus_list_set(ptr " ++ list ++ ", i64 " ++ index ++ ", i64 " ++ word ++ ", ptr " ++ d ++ ")")
        _ -> failG ("Native code does not support " ++ renderRvalue (ListOp op os) ++ " yet")
  where
    listArg o = do
        ty <- case op of
            Push -> pure destType
            Set -> pure destType
            Length -> sharedType fn [o]
            _ -> pure (TList destType)
        case ty of
            TList t -> operandAt fn ty o >>= \list -> pure (t, list)
            _ -> failG "A list operation needs a list"
    lengthOf list = do
        p <- ins "p" ("getelementptr i8, ptr " ++ list ++ ", i64 8")
        ins "n" ("load i64, ptr " ++ p)

-- Arrays. An array is held inline: the words of its elements one after another in the slot of the local that has it (an
-- element that is an array is its words, in line), and its value, wherever one is wanted, is the address of the first. It
-- is copied by copying the words, and there is nothing in it to free: its elements are plain.

isArray :: Type -> Bool
isArray TArray{} = True
isArray _ = False

-- The 8-byte words of a value held inline: an Int or a Bool is one, and an array is its elements'
slotsOf :: Type -> Integer
slotsOf (TArray t n) = n * slotsOf t
slotsOf _ = 1

memcpyText :: String -> String -> Integer -> String
memcpyText to from bytes = "call void @llvm.memcpy.p0.p0.i64(ptr " ++ to ++ ", ptr " ++ from ++ ", i64 " ++ show bytes ++ ", i1 false)"

-- Copies the words of an array to where another is (nothing to do when it is where it is)
copyWords :: String -> String -> Integer -> G ()
copyWords to from bytes = if to == from || bytes == 0 then pure () else emit (memcpyText to from bytes)

-- Whether an operand is an array
isArrayOperand :: Function -> Operand -> Bool
isArrayOperand fn o = case o of
    Copy l -> arrayLocal l
    Move l -> arrayLocal l
    Const CArray{} -> True
    Const _ -> False
  where
    arrayLocal l = maybe False (isArray . localType) (Map.lookup l (fnLocals fn))

-- The address of the words of an array operand: a local, or a constant that is a global
arrayPtr :: Operand -> G String
arrayPtr (Copy l) = pure (slot l)
arrayPtr (Move l) = pure (slot l)
arrayPtr (Const (CArray cs)) = constantWords cs
arrayPtr o = failG ("Not an array: " ++ renderOperand' o)

-- The number of elements of an array operand
arrayLength :: Function -> Operand -> G Integer
arrayLength fn o = case o of
    Const (CArray cs) -> pure (toInteger (length cs))
    Copy l -> ofLocal l
    Move l -> ofLocal l
    Const _ -> failG ("Not an array: " ++ renderOperand' o)
  where
    ofLocal l = localTypeG fn l >>= \ty -> case ty of
        TArray _ n -> pure n
        _ -> failG ("Not an array: " ++ show l)

-- The words of a constant array as a global that the code only reads, and its name
constantWords :: [Constant] -> G String
constantWords cs = do
    k <- G (\s -> let name = global "const." (sOwner s ++ "#" ++ show (sCount s)) in Ok (name, s{sCount = sCount s + 1}))
    let words' = concatMap flatten cs
        flatten c = case c of
            CInt i -> [show i]
            CBool b -> [if b then "1" else "0"]
            CArray inner -> concatMap flatten inner
            _ -> []
        body
            | null words' = "zeroinitializer"
            | otherwise = "[" ++ intercalate ", " ["i64 " ++ w | w <- words'] ++ "]"
    G (\s -> Ok ((), s{sGlobals = (k ++ " = private constant [" ++ show (length words') ++ " x i64] " ++ body) : sGlobals s}))
    pure k

-- The address of the element at an index, an element being so many bytes
elementAddress :: String -> String -> Integer -> G String
elementAddress base index bytes = do
    offset <- ins "o" ("mul i64 " ++ index ++ ", " ++ show bytes)
    ins "p" ("getelementptr i8, ptr " ++ base ++ ", i64 " ++ offset)

-- What an array operand's element is, ready to be written: the word, or for an array the address of its words
elementValue :: Function -> Type -> Operand -> G String
elementValue fn elementTy o = if isArray elementTy then arrayPtr o else operandAt fn elementTy o

writeElement :: Type -> String -> String -> String -> G ()
writeElement elementTy base index value = do
    p <- elementAddress base index (8 * slotsOf elementTy)
    if isArray elementTy then copyWords p value (8 * slotsOf elementTy) else storeAt elementTy p value

-- The statement that gives an array to a local. The array is made where the local is, with no pointer to it: `set` on the local
-- that is the array is a store into its slot, and on another it is a copy and a store. The contracts (an index in range) are
-- assumed.
assignArray :: Function -> Local -> Type -> Rvalue -> G ()
assignArray fn dest ty rv =
    case ty of
        TArray elementTy n -> do
            let target = slot dest
                bytes = 8 * slotsOf ty
            case rv of
                Use o -> arrayPtr o >>= \src -> copyWords target src bytes
                ListOp NewArray [_, x] -> fillArray fn target elementTy n x
                ListOp Set [a, i, x] -> do
                    src <- arrayPtr a
                    index <- operandAt fn TInt i
                    value <- elementValue fn elementTy x
                    copyWords target src bytes
                    writeElement elementTy target index value
                -- an element that is an array
                ListOp Get [a, i] -> do
                    src <- arrayPtr a
                    index <- operandAt fn TInt i
                    elementAddress src index bytes >>= \p -> copyWords target p bytes
                ListOp First [a] -> arrayPtr a >>= \src -> copyWords target src bytes
                ListOp Last [a] -> do
                    count <- arrayLength fn a
                    src <- arrayPtr a
                    elementAddress src (show (count - 1)) bytes >>= \p -> copyWords target p bytes
                _ -> failG ("Native code does not support " ++ renderRvalue rv ++ " for an array yet")
        _ -> failG "An array is assigned to something that is not an array"

-- n copies of an element: one store of zeros when it is a zero, and a loop otherwise
fillArray :: Function -> String -> Type -> Integer -> Operand -> G ()
fillArray fn target elementTy n x
    | n == 0 = pure ()
    | zero x && not (isArray elementTy) = emit ("call void @llvm.memset.p0.i64(ptr " ++ target ++ ", i8 0, i64 " ++ show (8 * n) ++ ", i1 false)")
    | otherwise = do
        value <- elementValue fn elementTy x
        k <- freshLabel "fill"
        let before = k ++ ".before"
            header = k ++ ".header"
            body = k ++ ".body"
            done = k ++ ".done"
            i = "%" ++ k ++ ".i"
            next = "%" ++ k ++ ".next"
        emit ("br label %" ++ before)
        label before
        emit ("br label %" ++ header)
        label header
        emit (i ++ " = phi i64 [ 0, %" ++ before ++ " ], [ " ++ next ++ ", %" ++ body ++ " ]")
        c <- ins "c" ("icmp slt i64 " ++ i ++ ", " ++ show n)
        emit ("br i1 " ++ c ++ ", label %" ++ body ++ ", label %" ++ done)
        label body
        writeElement elementTy target i value
        emit (next ++ " = add i64 " ++ i ++ ", 1")
        emit ("br label %" ++ header)
        label done
  where
    zero (Const (CInt 0)) = True
    zero (Const (CBool False)) = True
    zero _ = False

-- An element of an array, or its length, as a word
arrayRead :: Function -> Type -> ListOp -> [Operand] -> G String
arrayRead fn destType op os =
    case (op, os) of
        (Length, [a]) -> show <$> arrayLength fn a
        (First, [a]) -> arrayPtr a >>= \base -> loadElement destType base
        (Last, [a]) -> do
            count <- arrayLength fn a
            base <- arrayPtr a
            elementAddress base (show (count - 1)) 8 >>= loadElement destType
        (Get, [a, i]) -> do
            base <- arrayPtr a
            index <- operandAt fn TInt i
            elementAddress base index 8 >>= loadElement destType
        _ -> failG ("Native code does not support " ++ renderRvalue (ListOp op os) ++ " for an array yet")

-- The address of an element: a list is 24 bytes of header (count, length, capacity) and then a slot of 8 bytes per element
elementPtr :: String -> String -> G String
elementPtr list index = do
    elements <- ins "e" ("getelementptr i8, ptr " ++ list ++ ", i64 24")
    ins "p" ("getelementptr i64, ptr " ++ elements ++ ", i64 " ++ index)

storeElement :: Type -> String -> String -> String -> G ()
storeElement t list index value = do
    p <- elementPtr list index
    storeAt t p value

loadElement :: Type -> String -> G String
loadElement = loadAt

-- A slot of a struct or an enum value, at a byte offset
storeSlot :: Type -> String -> Int -> String -> G ()
storeSlot t object offset value = do
    p <- ins "p" ("getelementptr i8, ptr " ++ object ++ ", i64 " ++ show offset)
    storeAt t p value

loadSlot :: Type -> String -> Int -> G String
loadSlot t object offset = do
    p <- ins "p" ("getelementptr i8, ptr " ++ object ++ ", i64 " ++ show offset)
    loadAt t p

-- Every slot is 8 bytes: an Int, a Bool as 0 or 1, or a pointer
storeAt :: Type -> String -> String -> G ()
storeAt t p value =
    case t of
        TInt -> emit ("store i64 " ++ value ++ ", ptr " ++ p)
        TBool -> do
            w <- ins "w" ("zext i1 " ++ value ++ " to i64")
            emit ("store i64 " ++ w ++ ", ptr " ++ p)
        _ -> emit ("store ptr " ++ value ++ ", ptr " ++ p)

loadAt :: Type -> String -> G String
loadAt t p =
    case t of
        TInt -> ins "v" ("load i64, ptr " ++ p)
        TBool -> do
            w <- ins "w" ("load i64, ptr " ++ p)
            ins "b" ("icmp ne i64 " ++ w ++ ", 0")
        _ -> ins "v" ("load ptr, ptr " ++ p)

-- Whether a value is the address of an object (what the runtime compares by the descriptor of its type)
isPointer :: Type -> Bool
isPointer TList{} = True
isPointer TNamed{} = True
isPointer TVariant{} = True
isPointer _ = False

-- A value as the word the runtime takes: an Int as it is, a Bool as 0 or 1, a list as its address
toWord :: Type -> String -> G String
toWord TInt value = pure value
toWord TBool value = ins "w" ("zext i1 " ++ value ++ " to i64")
toWord _ value = ins "w" ("ptrtoint ptr " ++ value ++ " to i64")

binary :: BinOp -> Type -> String -> String -> G String
binary Add _ x y = checked "sadd" x y
binary Sub _ x y = checked "ssub" x y
binary Mul _ x y = checked "smul" x y
binary Div _ x y = do
    -- the one quotient that does not fit, which sdiv does not define
    isMin <- ins "c" ("icmp eq i64 " ++ x ++ ", " ++ show intMin)
    isMinusOne <- ins "c" ("icmp eq i64 " ++ y ++ ", -1")
    overflows <- ins "c" ("and i1 " ++ isMin ++ ", " ++ isMinusOne)
    stopOn overflows
    -- sdiv rounds toward 0 and `/` rounds down
    q <- ins "q" ("sdiv i64 " ++ x ++ ", " ++ y)
    r <- ins "r" ("srem i64 " ++ x ++ ", " ++ y)
    adjust <- roundsTheOtherWay r y
    lower <- ins "q" ("sub i64 " ++ q ++ ", 1")
    ins "q" ("select i1 " ++ adjust ++ ", i64 " ++ lower ++ ", i64 " ++ q)
binary Mod _ x y = do
    -- x % -1 is 0, and srem does not define it for the smallest Int
    isMinusOne <- ins "c" ("icmp eq i64 " ++ y ++ ", -1")
    divisor <- ins "d" ("select i1 " ++ isMinusOne ++ ", i64 1, i64 " ++ y)
    r <- ins "r" ("srem i64 " ++ x ++ ", " ++ divisor)
    -- srem takes the sign of the dividend and `%` the sign of the divisor
    adjust <- roundsTheOtherWay r y
    shifted <- ins "r" ("add i64 " ++ r ++ ", " ++ y)
    ins "r" ("select i1 " ++ adjust ++ ", i64 " ++ shifted ++ ", i64 " ++ r)
binary (Compare rel) ty x y | isPointer ty || isArray ty = do
    -- structural equality, which the runtime does by the descriptor of the type
    d <- descriptor ty
    a <- toWord ty x
    b <- toWord ty y
    r <- ins "e" ("call i32 @tersus_equal(ptr " ++ d ++ ", i64 " ++ a ++ ", i64 " ++ b ++ ")")
    ins "c" ("icmp " ++ (if predicate rel == "ne" then "eq" else "ne") ++ " i32 " ++ r ++ ", 0")
binary (Compare rel) ty x y = do
    t <- typeG ty
    ins "c" ("icmp " ++ predicate rel ++ " " ++ t ++ " " ++ x ++ ", " ++ y)

predicate :: Rel -> String
predicate Eq = "eq"
predicate NotEq = "ne"
predicate Lt = "slt"
predicate Gt = "sgt"
predicate LtEq = "sle"
predicate GtEq = "sge"

-- Arithmetic that stops the program when the result does not fit in an Int
checked :: String -> String -> String -> G String
checked name x y = do
    result <- ins "o" ("call {i64, i1} @llvm." ++ name ++ ".with.overflow.i64(i64 " ++ x ++ ", i64 " ++ y ++ ")")
    value <- ins "r" ("extractvalue {i64, i1} " ++ result ++ ", 0")
    overflowed <- ins "f" ("extractvalue {i64, i1} " ++ result ++ ", 1")
    stopOn overflowed
    return value

-- Goes to the overflow block when the flag is set, and carries on in a new block otherwise
stopOn :: String -> G ()
stopOn flag = do
    next <- freshLabel "ok"
    emit ("br i1 " ++ flag ++ ", label %overflow, label %" ++ next)
    label next

-- Whether a remainder and the divisor have opposite signs and the remainder is not 0, which is when truncating and
-- rounding down differ
roundsTheOtherWay :: String -> String -> G String
roundsTheOtherWay r divisor = do
    nonZero <- ins "c" ("icmp ne i64 " ++ r ++ ", 0")
    signs <- ins "x" ("xor i64 " ++ r ++ ", " ++ divisor)
    differ <- ins "c" ("icmp slt i64 " ++ signs ++ ", 0")
    ins "c" ("and i1 " ++ nonZero ++ ", " ++ differ)

emitTerminator :: Program -> Bool -> Function -> Terminator -> G ()
emitTerminator _ _ _ (Goto b) = emit ("br label %bb" ++ blockNumber b)
emitTerminator _ _ fn (SwitchBool o yes no) = do
    v <- operandAt fn TBool o
    emit ("br i1 " ++ v ++ ", label %bb" ++ blockNumber yes ++ ", label %bb" ++ blockNumber no)
emitTerminator program entry fn (Call (Const (CFn name)) args dest next) =
    case Map.lookup name (progFunctions program) of
        Nothing -> failG ("Call of a function that does not exist: " ++ name)
        Just callee -> do
            argTypes <- mapM (localTypeG callee) (fnParams callee)
            returnType <- maybe (failG ("Function without a result: " ++ name)) pure (fnReturns callee)
            call entry fn (functionSymbol name) argTypes returnType args dest next
emitTerminator _ entry fn (Call callee args dest next) = do
    -- a function value: the address of a function, with the types its type says
    ty <- sharedType fn [callee]
    case ty of
        TFn argTypes returnType -> do
            target <- operandAt fn ty callee
            call entry fn target argTypes returnType args dest next
        _ -> failG ("Call of something that is not a function: " ++ renderOperand' callee)
emitTerminator _ entry fn Return =
    case fnReturns fn of
        Nothing -> emit "ret void"
        Just ty | isArray ty -> do
            copyWords "%ret" (slot (Local 0)) (8 * slotsOf ty)
            if entry
                then ins "f" "load i1, ptr %returned" >>= \returned -> emit ("ret i1 " ++ returned)
                else emit "ret void"
        Just ty -> do
            t <- typeG ty
            v <- ins "v" ("load " ++ t ++ ", ptr " ++ slot (Local 0))
            if entry
                then do
                    returned <- ins "f" "load i1, ptr %returned"
                    withValue <- ins "w" ("insertvalue " ++ resultStruct t ++ " undef, " ++ t ++ " " ++ v ++ ", 0")
                    both <- ins "w" ("insertvalue " ++ resultStruct t ++ " " ++ withValue ++ ", i1 " ++ returned ++ ", 1")
                    emit ("ret " ++ resultStruct t ++ " " ++ both)
                else emit ("ret " ++ t ++ " " ++ v)
emitTerminator _ _ _ Unreachable = emit "unreachable"

-- A call of a function, given its symbol or the address of it, the types of its parameters and of its result
call :: Bool -> Function -> String -> [Type] -> Type -> [Operand] -> Local -> BlockId -> G ()
call entry fn target argTypes returnType args dest next = do
    values <- sequence (zipWith (operandAt fn) argTypes args)
    paramTypes <- mapM typeG argTypes
    result <- typeG returnType
    let arguments = zipWith (\t v -> t ++ " " ++ v) paramTypes values
    if isArray returnType
        then do
            -- the callee makes an array in the room it is given: the slot of the local that gets it (it has copied its arguments
            -- by the time it writes, so the local may be one of them)
            emit ("call void " ++ target ++ "(" ++ intercalate ", " (("ptr " ++ slot dest) : arguments) ++ ")")
            if entry && dest == Local 0 then emit "store i1 true, ptr %returned" else pure ()
        else do
            r <- ins "c" ("call " ++ result ++ " " ++ target ++ "(" ++ intercalate ", " arguments ++ ")")
            storeResult entry fn dest r
    emit ("br label %bb" ++ blockNumber next)

renderOperand' :: Operand -> String
renderOperand' o = renderRvalue (Use o)

-- The text that stands for an operand where a value of the type is wanted: the value loaded from the slot of a local, a
-- number or a Bool, or a list made from a constant (the type says what an empty one holds)
operandAt :: Function -> Type -> Operand -> G String
operandAt fn _ (Copy l) = do
    ty <- localTypeG fn l
    t <- typeG ty
    -- (an array is the address of the words it is made of)
    if isArray ty then pure (slot l) else ins "v" ("load " ++ t ++ ", ptr " ++ slot l)
operandAt fn _ (Move l) = do
    ty <- localTypeG fn l
    t <- typeG ty
    if isArray ty
        then pure (slot l)
        else do
            v <- ins "v" ("load " ++ t ++ ", ptr " ++ slot l)
            emit ("store " ++ t ++ " " ++ zeroOf t ++ ", ptr " ++ slot l)
            pure v
operandAt _ ty (Const c) = constantValue ty c

constantValue :: Type -> Constant -> G String
constantValue _ (CInt i) = pure (show i)
constantValue _ (CBool b) = pure (if b then "true" else "false")
constantValue _ (CArray cs) = constantWords cs
constantValue (TList t) (CList cs) = do
    list <- newList (length cs)
    mapM_ (\(i, c) -> constantValue t c >>= storeElement t list (show i)) (zip [0 :: Int ..] cs)
    pure list
constantValue _ (CData name fields) = do
    program <- programG
    (tag, declared) <- constructorG program name
    object <- newData tag (length declared)
    mapM_
        ( \(i, (f, t)) -> case lookup f fields of
            Just c -> constantValue t c >>= storeSlot t object (dataHeader + 8 * i)
            Nothing -> failG ("A field is missing: " ++ name ++ "." ++ f)
        )
        (zip [0 ..] declared)
    pure object
-- a function is its address
constantValue _ (CFn name) = pure (functionSymbol name)
constantValue ty c = failG ("A constant of the wrong type: " ++ renderRvalue (Use (Const c)) ++ " is not a " ++ renderType ty)

-- The type that the operands of an operation share. A local has a type; a constant has one only where it holds a number or a
-- Bool, and the nesting of an empty list is all it says of its elements (`[[]]` is a list of lists), so the type of a local
-- comes first, then that of a constant that shows its leaves, then the shape of one that does not, with Int for the leaf.
sharedType :: Function -> [Operand] -> G Type
sharedType fn os = do
    program <- programG
    pure $ case [ty | Just ty <- map local os] ++ [constantShape program c | Const c <- os, constantKnown c] ++ [constantShape program c | Const c <- os] of
        ty : _ -> ty
        [] -> TList TInt
  where
    local (Copy l) = localType <$> Map.lookup l (fnLocals fn)
    local (Move l) = localType <$> Map.lookup l (fnLocals fn)
    local (Const _) = Nothing

-- The type of a constant, as far as its contents say: an empty list of lists is a List<List<Int>>
constantShape :: Program -> Constant -> Type
constantShape _ (CBool _) = TBool
constantShape program (CList cs) =
    case [c | c <- cs, constantKnown c] ++ cs of
        c : _ -> TList (constantShape program c)
        [] -> TList TInt
constantShape program (CArray cs) =
    case [c | c <- cs, constantKnown c] ++ cs of
        c : _ -> TArray (constantShape program c) (toInteger (length cs))
        [] -> TArray TInt 0
constantShape program (CData name _) = constructedType program name
constantShape program (CFn name) =
    case Map.lookup name (progFunctions program) of
        Just f -> TFn [maybe TInt localType (Map.lookup p (fnLocals f)) | p <- fnParams f] (maybe TInt id (fnReturns f))
        Nothing -> TInt
constantShape _ _ = TInt

-- Whether the contents of a constant say what it is made of: a number or a Bool is, and a list is when one element is
constantKnown :: Constant -> Bool
constantKnown (CList cs) = any constantKnown cs
constantKnown (CArray cs) = any constantKnown cs
constantKnown _ = True

-- Stores the result of a statement; in the entry, the return slot being assigned is what makes the program return a value
storeResult :: Bool -> Function -> Local -> String -> G ()
storeResult entry fn dest value = do
    store fn dest value
    if entry && dest == Local 0 then emit "store i1 true, ptr %returned" else pure ()

-- A local that owns a value frees the one it held when it is given another
store :: Function -> Local -> String -> G ()
store fn dest value = do
    ty <- localTypeG fn dest
    t <- typeG ty
    if isPointer ty then dropSlot ty dest else pure ()
    emit ("store " ++ t ++ " " ++ value ++ ", ptr " ++ slot dest)

-- Frees the value a local holds (nothing, if it holds none)
dropSlot :: Type -> Local -> G ()
dropSlot ty l = do
    old <- ins "o" ("load ptr, ptr " ++ slot l)
    d <- descriptor ty
    emit ("call void @tersus_drop(ptr " ++ d ++ ", ptr " ++ old ++ ")")

localTypeG :: Function -> Local -> G Type
localTypeG fn l = maybe (failG ("Undeclared local " ++ show l)) (pure . localType) (Map.lookup l (fnLocals fn))

localLlvmType :: Function -> Local -> Result String String
localLlvmType fn l = maybe (Error ("Undeclared local " ++ show l)) (llvmType . localType) (Map.lookup l (fnLocals fn))

typeG :: Type -> G String
typeG ty = either failG pure (toEither (llvmType ty))
  where
    toEither (Ok a) = Right a
    toEither (Error e) = Left e

llvmType :: Type -> Result String String
llvmType TInt = Ok "i64"
llvmType TBool = Ok "i1"
llvmType (TList t) = llvmType t `bindResult` \_ -> Ok "ptr"
-- (an array is passed and held as the address of its words)
llvmType (TArray t _) = llvmType t `bindResult` \_ -> Ok "ptr"
llvmType TNamed{} = Ok "ptr"
llvmType TVariant{} = Ok "ptr"
llvmType TFn{} = Ok "ptr"
llvmType ty = Error (unsupportedType ty)

-- What a local takes in the frame: a word, or for an array all the words it is made of
storageType :: Type -> Result String String
storageType ty@(TArray t _) = llvmType t `bindResult` \_ -> Ok ("[" ++ show (slotsOf ty) ++ " x i64]")
storageType ty = llvmType ty

unsupportedType :: Type -> String
unsupportedType ty = "Native code does not support " ++ renderType ty ++ " yet"

-- The stack slot of a local, and the parameter that starts in it (a dot, which no temporary has)
slot :: Local -> String
slot l = "%l." ++ localNumber l

localNumber :: Local -> String
localNumber (Local n) = show n

blockNumber :: BlockId -> String
blockNumber (BlockId n) = show n

-- The symbol of a function of the program. Quoted, since a lifted function is named outer::inner.
functionSymbol :: Name -> String
functionSymbol name = global "fn." name
