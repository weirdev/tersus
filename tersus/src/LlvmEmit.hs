{-# LANGUAGE PatternSynonyms #-}

module LlvmEmit
    ( emitProgram
    ) where

import Data.List (elemIndex, intercalate, nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)

import Mir
import MirOwnership (insertOwnership, needsDrop)
import MirVerify (verifyProgram)
import Pretty (renderType)
import TersusTypes (Name, Rel (..), Size (..), Type (..), Variable, pattern TArray)
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
    , "declare ptr @tersus_list_new_words(i64, i64)"
    , "declare ptr @tersus_list_push_words(ptr, ptr, i64)"
    , "declare ptr @tersus_list_set_words(ptr, i64, ptr, ptr)"
    , "declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)"
    , "declare void @llvm.memset.p0.i64(ptr, i8, i64, i1)"
    , "declare ptr @tersus_list_push(ptr, i64)"
    , "declare ptr @tersus_list_set(ptr, i64, i64, ptr)"
    , "declare void @tersus_clone(ptr, ptr, ptr)"
    , "declare void @tersus_drop(ptr, ptr)"
    , "declare ptr @tersus_box_new(i64)"
    , "declare void @tersus_box_free(ptr)"
    , ""
    ]

-- The C-level main: runs the program and prints its return value, if it returned one
entryPoint :: Program -> Function -> Result ([String], [Type]) String
entryPoint program fn =
    case fnReturns fn of
        Nothing -> Ok (wrap ["call void @tersus_main()", "ret i32 0"], [])
        -- a value held inline (an array, a struct, an enum) is made in a frame, so the program is given room for it, and prints it
        -- (and frees what it owns) from there
        Just ty | isAggregate ty ->
            Ok
                ( wrap
                    ( [ "%out = alloca [" ++ show (slotsOf program ty) ++ " x i64]"
                      , "%ok = call i1 @tersus_main(ptr %out)"
                      , "br i1 %ok, label %print, label %done"
                      , "print:"
                      , "%w = ptrtoint ptr %out to i64"
                      , "call void @tersus_print(ptr " ++ typeSymbol program ty ++ ", i64 %w)"
                      ]
                        ++ ["call void @tersus_drop(ptr " ++ typeSymbol program ty ++ ", ptr %out)" | needsDrop program ty]
                        ++ ["br label %done", "done:", "ret i32 0"]
                    )
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
                                ++ concat [["%slot = alloca i64", "store ptr %v, ptr %slot", "call void @tersus_drop(ptr " ++ typeSymbol program ty ++ ", ptr %slot)"] | isPointer ty]
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
    parts (TBox (TArrayOf t SizeAny)) = [canonical program t]
    parts (TBox t) = [canonical program t]
    parts (TNamed n) = [canonical program t | (_, fields) <- variantsOf program n, (_, t) <- fields]
    parts _ = []

-- A value of a variant has the representation of its enum, so one descriptor serves both
canonical :: Program -> Type -> Type
canonical program (TVariant v) = maybe (TVariant v) TNamed (ownerOf program v)
canonical _ ty = ty

-- A constant global for each type: its kind (0 Int, 1 Bool, 2 List, 3 struct or enum, 4 function, 5 array, 6 Box, 7 Box of an array
-- of no size) and what the
-- runtime needs to walk a value: the descriptor of the elements of a list, an array, a Box of an array of no size, or of what a Box holds, or the variants of a struct or enum
-- with the names and the descriptors of their fields, and whether the value starts with a word that says the variant (an enum)
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
    body (TBox (TArrayOf t SizeAny)) = "{ i64 7, ptr " ++ typeSymbol program t ++ " }"
    body (TBox t) = "{ i64 6, ptr " ++ typeSymbol program t ++ " }"
    body (TNamed n) = "{ i64 3, ptr " ++ global "data." n ++ " }"
    body (TFn _ _) = "{ i64 4, ptr null }"
    body _ = "{ i64 -1, ptr null }"
    dataDescriptor n =
        let variants = variantsOf program n
         in [ global "data." n ++ " = private constant { i64, ptr, i64 } { i64 " ++ show (length variants) ++ ", ptr " ++ global "variants." n ++ ", i64 " ++ (if isEnum n then "1" else "0") ++ " }"
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
    isEnum n = case Map.lookup n (progTypes program) of
        Just EnumDecl{} -> True
        _ -> False

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
-- (a struct is its own constructor, and a cast to it, `p as P`, has the type of a variant of it)
ownerOf :: Program -> Name -> Maybe Name
ownerOf program v =
    case Map.lookup v (progTypes program) of
        Just StructDecl{} -> Just v
        _ -> listToMaybe [n | (n, EnumDecl variants) <- Map.toList (progTypes program), v `elem` map fst variants]

-- The type of a value that a struct or a variant builds
constructedType :: Program -> Name -> Type
constructedType program name =
    case Map.lookup name (progTypes program) of
        Just StructDecl{} -> TNamed name
        _ -> TVariant name

-- Generating the code of one function: a counter for the names of temporaries and labels, the lines so far (last first),
-- and the types whose descriptors the code refers to
-- (sTemps are the rooms of the function that its code uses for values it builds, made at the start so that a loop does not grow the
-- frame)
data S = S {sCount :: Int, sLines :: [String], sTypes :: [Type], sProgram :: Program, sGlobals :: [String], sOwner :: Name, sTemps :: [String]}

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
            let returnsAggregate = maybe False isAggregate (fnReturns fn)
                -- (a value held inline comes back in room that the caller gives, as the first parameter)
                returnType
                    | returnsAggregate = if entry then "i1" else "void"
                    | entry && fnReturns fn /= Nothing = resultStruct valueType
                    | otherwise = valueType
             in inFunction (flatResultMap (\(l, d) -> mapResult ((,) l) (storageType program (localType d))) (Map.toList (fnLocals fn))) `bindResult` \localTypes ->
                    let params = intercalate ", " (["ptr %ret" | returnsAggregate] ++ [t ++ " %p." ++ localNumber p | (p, t) <- zip (fnParams fn) paramTypes])
                        header = "define internal " ++ returnType ++ " " ++ symbol ++ "(" ++ params ++ ") {"
                        prologue temps =
                            ["entry:"]
                                ++ ["    " ++ slot l ++ " = alloca " ++ t | (l, t) <- localTypes]
                                ++ temps
                                -- (a local that owns something holds nothing until it is given a value, so that it can be dropped)
                                ++ ["    store ptr null, ptr " ++ slot l | (l, d) <- Map.toList (fnLocals fn), isPointer (localType d), l `notElem` fnParams fn]
                                ++ [ "    call void @llvm.memset.p0.i64(ptr " ++ slot l ++ ", i8 0, i64 " ++ show (8 * slotsOf program (localType d)) ++ ", i1 false)"
                                   | (l, d) <- Map.toList (fnLocals fn)
                                   , isAggregate (localType d)
                                   , needsDrop program (localType d)
                                   , l `notElem` fnParams fn
                                   ]
                                ++ concat
                                    [ case Map.lookup p (fnLocals fn) of
                                        -- (a value held inline is given by its address, and the function works on its own copy)
                                        Just d | isAggregate (localType d) -> ["    " ++ memcpyText (slot p) ("%p." ++ localNumber p) (8 * slotsOf program (localType d))]
                                        _ -> ["    store " ++ t ++ " %p." ++ localNumber p ++ ", ptr " ++ slot p]
                                    | (p, t) <- zip (fnParams fn) paramTypes
                                    ]
                                ++ entryPrologue
                                ++ ["    br label %bb" ++ blockNumber (BlockId 0)]
                        entryPrologue =
                            if entry && fnReturns fn /= Nothing
                                then ["    %returned = alloca i1", "    store i1 false, ptr %returned"] ++ ["    store " ++ valueType ++ " " ++ zeroOf valueType ++ ", ptr " ++ slot (Local 0) | not returnsAggregate]
                                else []
                     in case runG (mapM_ (emitBlock program entry fn) (Map.toList (fnBlocks fn))) (S 0 [] [] program [] (fnName fn) []) of
                            Error e -> Error ("In " ++ fnName fn ++ ": " ++ e)
                            Ok (_, s) ->
                                Ok (reverse (sGlobals s) ++ [header] ++ prologue (reverse (sTemps s)) ++ reverse (sLines s) ++ overflowBlock ++ ["}"], sTypes s)
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
    owns <- ownsG ty
    if owns then dropSlot ty l else pure ()
emitStatement _ fn (Peek dest rv) = do
    destType <- localTypeG fn dest
    if isAggregate destType
        then assignAggregate False fn dest destType rv
        else do
            result <- rvalue fn destType rv
            t <- typeG destType
            emit ("store " ++ t ++ " " ++ result ++ ", ptr " ++ slot dest)
emitStatement entry fn (Assign dest rv) = do
    destType <- localTypeG fn dest
    case rv of
        Clone o -> cloneInto fn dest destType o >> returned
        _
            | isAggregate destType -> assignAggregate True fn dest destType rv >> returned
            | otherwise -> rvalue fn destType rv >>= storeResult entry fn dest
  where
    -- (in the entry, the return slot being assigned is what makes the program return a value; storeResult says it for a word)
    returned = if entry && dest == Local 0 then emit "store i1 true, ptr %returned" else pure ()

-- A copy of the value that a local owns, which shares nothing with it, given to another local (which frees the value it held)
cloneInto :: Function -> Local -> Type -> Operand -> G ()
cloneInto fn dest destType o = do
    source <- case o of
        Copy l -> pure (slot l)
        Move l -> pure (slot l)
        Const _ -> failG "Native code does not copy a constant"
    owns <- ownsG destType
    d <- descriptor destType
    if owns
        then do
            -- the copy is made before what the local held is freed, since it can be a part of it (`t = clone of t.next`)
            bytes <- bytesG destType
            room <- entryTemp (bytes `div` 8)
            emit ("call void @tersus_clone(ptr " ++ d ++ ", ptr " ++ room ++ ", ptr " ++ source ++ ")")
            dropSlot destType dest
            copyWords (slot dest) room bytes
        else emit ("call void @tersus_clone(ptr " ++ d ++ ", ptr " ++ slot dest ++ ", ptr " ++ source ++ ")")

-- The value of an rvalue that is a word (a number, a Bool, an address of a list or a Box or a function), given the type of the local
-- it is for (which says what a constant list holds). A value held inline is made where it goes: see assignAggregate.
rvalue :: Function -> Type -> Rvalue -> G String
rvalue fn destType rv =
    case rv of
        Use o -> operandAt fn destType o
        -- a Box has room of its own on the heap for what it holds, which is moved into it
        MakeBox o -> case destType of
            TBox held -> do
                count <- slotsG held
                block <- ins "x" ("call ptr @tersus_box_new(i64 " ++ show count ++ ")")
                if isAggregate held
                    then operandAddress fn held o >>= \from -> copyWords block from (8 * count)
                    else operandAt fn held o >>= storeAt held block
                pure block
            _ -> failG "A Box is made into a Box"
        -- what a Box holds that is a word is read from its room, which is freed when the Box is moved
        Unbox o -> do
            held <- operandLocalType fn o
            boxTy <- maybe (failG "Box::unbox was given a constant") pure held
            block <- operandAt fn boxTy o
            value <- loadAt destType block
            case o of
                Move _ -> emit ("call void @tersus_box_free(ptr " ++ block ++ ")")
                _ -> pure ()
            pure value
        BinaryOp op a b -> do
            ty <- sharedType fn [a, b]
            x <- operandAt fn ty a
            y <- operandAt fn ty b
            binary op ty x y
        MakeList os -> case destType of
            TList t -> do
                list <- slotsG t >>= newList (length os)
                mapM_ (\(i, o) -> elementValue fn t o >>= storeElement t list (show i)) (zip [0 :: Int ..] os)
                pure list
            _ -> failG "A list literal must make a list"
        ListOp op os@(first : _) | isArrayOperand fn first -> arrayRead fn destType op os
        ListOp op os -> listOperation fn destType op os
        ReadField o name field -> do
            program <- programG
            (_, declared) <- constructorG program name
            case elemIndex field (map fst declared) of
                Nothing -> failG ("Variant " ++ name ++ " has no field " ++ field)
                Just i -> do
                    base <- dataBase fn (constructedType program name) o
                    offset <- fieldOffsetG name declared i
                    loadSlot (snd (declared !! i)) base offset
        IsVariant o name -> do
            program <- programG
            (tag, _) <- constructorG program name
            -- (a struct has no tag, and a value of its type is that struct)
            if tagWords program name == 0
                then pure "true"
                else do
                    base <- dataBase fn (constructedType program name) o
                    found <- ins "t" ("load i64, ptr " ++ base)
                    ins "c" ("icmp eq i64 " ++ found ++ ", " ++ show tag)
        -- the field is moved out of the value: what it held is left holding nothing
        TakeField s name field -> do
            program <- programG
            (_, declared) <- constructorG program name
            case elemIndex field (map fst declared) of
                Nothing -> failG ("Variant " ++ name ++ " has no field " ++ field)
                Just i -> do
                    base <- dataBase fn (constructedType program name) (Copy s)
                    offset <- fieldOffsetG name declared i
                    taken <- loadSlot (snd (declared !! i)) base offset
                    p <- ins "p" ("getelementptr i8, ptr " ++ base ++ ", i64 " ++ show offset)
                    emit ("store i64 0, ptr " ++ p)
                    pure taken
        _ -> failG ("Native code makes " ++ renderRvalue rv ++ " where it is held inline, not as a word")

-- A list of n elements that are stride words each, which the caller fills in
newList :: Int -> Integer -> G String
newList n 1 = ins "l" ("call ptr @tersus_list_new(i64 " ++ show n ++ ")")
newList n stride = ins "l" ("call ptr @tersus_list_new_words(i64 " ++ show n ++ ", i64 " ++ show stride ++ ")")

-- The words that a struct or an enum takes, and the byte offset of the field at a position of a constructor: an enum value starts
-- with a word that says the variant, a struct with its first field. A field is a word, or the words of a value held inline.
tagWords :: Program -> Name -> Integer
tagWords program name =
    case Map.lookup name (progTypes program) of
        Just StructDecl{} -> 0
        _ -> 1

fieldOffsetG :: Name -> [(Variable, Type)] -> Int -> G Integer
fieldOffsetG name declared i = do
    program <- programG
    pure (8 * (tagWords program name + sum [slotsOf program t | (_, t) <- take i declared]))

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
        -- (an element held inline is moved in from where it is)
        (Push, [l, x]) -> do
            (t, list) <- listArg l
            if isAggregate t
                then do
                    count <- slotsG t
                    from <- operandAddress fn t x
                    ins "l" ("call ptr @tersus_list_push_words(ptr " ++ list ++ ", ptr " ++ from ++ ", i64 " ++ show count ++ ")")
                else do
                    word <- operandAt fn t x >>= toWord t
                    ins "l" ("call ptr @tersus_list_push(ptr " ++ list ++ ", i64 " ++ word ++ ")")
        (Set, [l, i, x]) -> do
            (t, list) <- listArg l
            index <- operandAt fn TInt i
            d <- descriptor t
            if isAggregate t
                then do
                    from <- operandAddress fn t x
                    ins "l" ("call ptr @tersus_list_set_words(ptr " ++ list ++ ", i64 " ++ index ++ ", ptr " ++ from ++ ", ptr " ++ d ++ ")")
                else do
                    word <- operandAt fn t x >>= toWord t
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

-- Values held inline. An array, a struct and an enum are not values of the heap but their words, one after another in the slot of
-- the local that has them (a field or an element that is held inline is its words, in line), and the value of one, wherever a value
-- is wanted, is the address of the first. One is copied by copying the words. A struct is its fields' words, an enum a word that
-- says the variant and then the fields of that variant (the room of the widest), an array its elements. What a value owns (a
-- list or a Box) is a word of it, and the words are cleared when the value is moved out, so that a drop of what is left frees
-- nothing.

isArray :: Type -> Bool
isArray TArray{} = True
isArray _ = False

-- A Box of an array, of a size or of any size: the array is on the heap, and the address of it is the first word of the Box
isBoxedArray :: Type -> Bool
isBoxedArray (TBox TArrayOf{}) = True
isBoxedArray _ = False

isAggregate :: Type -> Bool
isAggregate TArray{} = True
isAggregate TNamed{} = True
isAggregate TVariant{} = True
isAggregate ty = isFat ty

-- A Box of an array of no size is two words held inline, as an aggregate: the address of the elements and how many there are. (A Box of
-- anything that has a size is the one word, the address of what it holds.)
isFat :: Type -> Bool
isFat (TBox (TArrayOf _ SizeAny)) = True
isFat _ = False

-- The 8-byte words of a value held inline: an Int, a Bool or an address is one, and an array is its elements', a struct its fields' and
-- an enum a word and the widest of its variants'
slotsOf :: Program -> Type -> Integer
slotsOf program ty =
    case ty of
        _ | isFat ty -> 2
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

slotsG :: Type -> G Integer
slotsG ty = (`slotsOf` ty) <$> programG

bytesG :: Type -> G Integer
bytesG ty = (8 *) <$> slotsG ty

-- Whether a local of the type has something to free: a word that is the address of a list or a Box, or a value held inline that
-- holds one
ownsG :: Type -> G Bool
ownsG ty = (\program -> isPointer ty || (isAggregate ty && needsDrop program ty)) <$> programG

memcpyText :: String -> String -> Integer -> String
memcpyText to from bytes = "call void @llvm.memcpy.p0.p0.i64(ptr " ++ to ++ ", ptr " ++ from ++ ", i64 " ++ show bytes ++ ", i1 false)"

-- Copies the words of a value to where another is (nothing to do when it is where it is)
copyWords :: String -> String -> Integer -> G ()
copyWords to from bytes = if to == from || bytes == 0 then pure () else emit (memcpyText to from bytes)

-- Clears the words of a value that has been moved out
zeroWords :: String -> Integer -> G ()
zeroWords at bytes = if bytes == 0 then pure () else emit ("call void @llvm.memset.p0.i64(ptr " ++ at ++ ", i8 0, i64 " ++ show bytes ++ ", i1 false)")

-- Room in the frame of the function for a value it builds, made at its start
entryTemp :: Integer -> G String
entryTemp count = G (\s -> let name = "%t." ++ show (sCount s) in Ok (name, s{sCount = sCount s + 1, sTemps = ("    " ++ name ++ " = alloca [" ++ show count ++ " x i64]") : sTemps s}))

-- Whether an operand is an array
isArrayOperand :: Function -> Operand -> Bool
isArrayOperand fn o = case o of
    Copy l -> arrayLocal l
    Move l -> arrayLocal l
    Const CArray{} -> True
    Const _ -> False
  where
    arrayLocal l = maybe False (\d -> isArray (localType d) || isBoxedArray (localType d)) (Map.lookup l (fnLocals fn))

-- The address of the words of an array operand: a local, or a constant that is a global
arrayPtr :: Function -> Operand -> G String
arrayPtr fn o =
    case o of
        Copy l -> ofLocal l
        Move l -> ofLocal l
        Const (CArray cs) -> constantWords cs
        _ -> failG ("Not an array: " ++ renderOperand' o)
  where
    -- (a Box of an array holds the address of the elements in its first word, whether it carries the size too or not)
    ofLocal l = localTypeG fn l >>= \ty -> if isBoxedArray ty then ins "a" ("load ptr, ptr " ++ slot l) else pure (slot l)

-- The address of the words of a value held inline that an operand is, ready for something to take: a value that is moved out of a
-- local and owns something is copied to room of its own and the local is cleared, so that what takes it can copy it later with the
-- local already empty. A constant is built in room of its own.
operandAddress :: Function -> Type -> Operand -> G String
operandAddress fn ty o =
    case o of
        Copy l -> pure (slot l)
        Move l -> do
            localTy <- localTypeG fn l
            owns <- ownsG localTy
            if owns
                then do
                    bytes <- bytesG localTy
                    room <- entryTemp (bytes `div` 8)
                    copyWords room (slot l) bytes
                    zeroWords (slot l) bytes
                    pure room
                else pure (slot l)
        Const c -> constantAggregate ty c

-- The address of the words of a struct or an enum value that an operand is: a local holds them, and a Box holds a pointer to them
dataBase :: Function -> Type -> Operand -> G String
dataBase fn ty o =
    case o of
        Copy l -> local l
        Move l -> local l
        Const c -> constantAggregate ty c
  where
    local l = do
        localTy <- localTypeG fn l
        case localTy of
            TBox _ -> ins "b" ("load ptr, ptr " ++ slot l)
            _ -> pure (slot l)

-- The type of a local that an operand is
operandLocalType :: Function -> Operand -> G (Maybe Type)
operandLocalType fn o =
    case o of
        Copy l -> Just <$> localTypeG fn l
        Move l -> Just <$> localTypeG fn l
        Const _ -> pure Nothing

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

-- A constant that is held inline: an array literal is a global, and a struct or an enum is built in room of its own each time it
-- is wanted (it can hold a list, which is made then)
constantAggregate :: Type -> Constant -> G String
constantAggregate ty c =
    case c of
        CArray cs -> constantWords cs
        _ -> do
            count <- slotsG ty
            room <- entryTemp count
            writeConstant ty room c
            pure room

-- Writes a constant into the words at an address, of the type that it is
writeConstant :: Type -> String -> Constant -> G ()
writeConstant ty at c =
    case c of
        CInt i -> emit ("store i64 " ++ show i ++ ", ptr " ++ at)
        CBool b -> emit ("store i64 " ++ (if b then "1" else "0") ++ ", ptr " ++ at)
        CFn name -> emit ("store ptr " ++ functionSymbol name ++ ", ptr " ++ at)
        CList cs -> case ty of
            TList t -> do
                list <- constantList t cs
                emit ("store ptr " ++ list ++ ", ptr " ++ at)
            _ -> failG ("A constant list is not a " ++ renderType ty)
        CArray cs -> do
            from <- constantWords cs
            bytes <- bytesG ty
            copyWords at from bytes
        CData name fields -> do
            program <- programG
            (tag, declared) <- constructorG program name
            if tagWords program name == 1 then emit ("store i64 " ++ show tag ++ ", ptr " ++ at) else pure ()
            mapM_
                ( \(i, (f, t)) -> case lookup f fields of
                    Just e -> do
                        offset <- fieldOffsetG name declared i
                        p <- ins "p" ("getelementptr i8, ptr " ++ at ++ ", i64 " ++ show offset)
                        writeConstant t p e
                    Nothing -> failG ("A field is missing: " ++ name ++ "." ++ f)
                )
                (zip [0 ..] declared)

-- A list made from constants
constantList :: Type -> [Constant] -> G String
constantList t cs = do
    stride <- slotsG t
    list <- newList (length cs) stride
    mapM_ (\(i, c) -> elementSlot stride list (show (i :: Int)) >>= \p -> writeConstant t p c) (zip [0 ..] cs)
    pure list

-- The address of an element at an index, an element being so many bytes
elementAddress :: String -> String -> Integer -> G String
elementAddress base index bytes = do
    offset <- ins "o" ("mul i64 " ++ index ++ ", " ++ show bytes)
    ins "p" ("getelementptr i8, ptr " ++ base ++ ", i64 " ++ offset)

-- What an element of a list or an array is, ready to be written: the word, or for a value held inline the address of its words
elementValue :: Function -> Type -> Operand -> G String
elementValue fn elementTy o = if isAggregate elementTy then operandAddress fn elementTy o else operandAt fn elementTy o

writeElement :: Type -> String -> String -> String -> G ()
writeElement elementTy base index value = do
    bytes <- bytesG elementTy
    p <- elementAddress base index bytes
    if isAggregate elementTy then copyWords p value bytes else storeAt elementTy p value

-- The statement that gives a value held inline to a local, made where the local is, with no pointer to it. The value that the local
-- held is freed first if it owns something (unless the local only looks at a value, as a Peek does). The contracts (an index in
-- range) are assumed.
assignAggregate :: Bool -> Function -> Local -> Type -> Rvalue -> G ()
assignAggregate dropsOld fn dest ty rv = do
    program <- programG
    bytes <- bytesG ty
    owns <- ownsG ty
    let target = slot dest
        freeOld = if dropsOld && owns then dropSlot ty dest else pure ()
        -- the address of the element at an index of an array or of a list, the element being the value that is made
        elementOf container index
            | isArrayOperand fn container = arrayPtr fn container >>= \base -> elementAddress base index bytes
            | otherwise = operandAt fn (TList ty) container >>= \list -> slotsG ty >>= \stride -> elementSlot stride list index
        lengthOfList container = operandAt fn (TList ty) container >>= \list -> ins "p" ("getelementptr i8, ptr " ++ list ++ ", i64 8") >>= \p -> ins "n" ("load i64, ptr " ++ p)
        -- a value that is a part of another is copied out of it, and the other is left as it was or with the part cleared. When the
        -- local owns something it is copied into room of its own first, since the part can be a part of what the local held.
        fromPart address clear =
            if dropsOld && owns
                then do
                    room <- entryTemp (bytes `div` 8)
                    copyWords room address bytes
                    if clear then zeroWords address bytes else pure ()
                    freeOld
                    copyWords target room bytes
                else do
                    copyWords target address bytes
                    if clear then zeroWords address bytes else pure ()
    case rv of
        Use o -> operandAddress fn ty o >>= \src -> fromPart src False
        ListOp NewArray [_, x] | TArray elementTy n <- ty -> fillArray fn target elementTy n x
        ListOp Set [a, i, x] | TArray elementTy _ <- ty -> do
            src <- arrayPtr fn a
            index <- operandAt fn TInt i
            value <- elementValue fn elementTy x
            copyWords target src bytes
            writeElement elementTy target index value
        -- Array::boxed(n, x): room on the heap for n elements, filled with x; the Box holds where it is and n
        ListOp NewBoxed [n, x] | TBox (TArrayOf elementTy _) <- ty -> do
            count <- operandAt fn TInt n
            stride <- slotsG elementTy
            total <- if stride == 1 then pure count else checked "smul" count (show stride)
            block <- ins "x" ("call ptr @tersus_box_new(i64 " ++ total ++ ")")
            fillElements fn block elementTy count Nothing x
            freeOld
            emit ("store ptr " ++ block ++ ", ptr " ++ target)
            lengthSlot <- ins "p" ("getelementptr i8, ptr " ++ target ++ ", i64 8")
            emit ("store i64 " ++ count ++ ", ptr " ++ lengthSlot)
        -- a Box of an array of a size as a Box of an array of any size: the address, and the size the type had
        Unsize o -> do
            held <- operandLocalType fn o
            case held of
                Just boxTy@(TBox (TArray _ n)) -> do
                    block <- operandAt fn boxTy o
                    freeOld
                    emit ("store ptr " ++ block ++ ", ptr " ++ target)
                    lengthSlot <- ins "p" ("getelementptr i8, ptr " ++ target ++ ", i64 8")
                    emit ("store i64 " ++ show n ++ ", ptr " ++ lengthSlot)
                _ -> failG "unsize was given something that is not a Box of an array of a size"
        -- the elements of a Box that carries its size are changed where they are, and the Box is given back
        ListOp Set [a, i, x] | TBox (TArrayOf elementTy _) <- ty -> do
            src <- operandAddress fn ty a
            block <- ins "a" ("load ptr, ptr " ++ src)
            index <- operandAt fn TInt i
            value <- elementValue fn elementTy x
            writeElement elementTy block index value
            fromPart src False
        -- an element that is a value held inline, of an array or of a list
        ListOp Get [a, i] -> do
            index <- operandAt fn TInt i
            elementOf a index >>= \p -> fromPart p False
        ListOp First [a] -> elementOf a "0" >>= \p -> fromPart p False
        ListOp Last [a] -> do
            index <-
                if isArrayOperand fn a
                    then arrayLength fn a >>= \count -> lastIndex count
                    else lengthOfList a >>= \len -> ins "i" ("sub i64 " ++ len ++ ", 1")
            elementOf a index >>= \p -> fromPart p False
        -- a field that is held inline
        ReadField o name field -> do
            (_, declared) <- constructorG program name
            case elemIndex field (map fst declared) of
                Nothing -> failG ("Variant " ++ name ++ " has no field " ++ field)
                Just i -> do
                    base <- dataBase fn (constructedType program name) o
                    offset <- fieldOffsetG name declared i
                    p <- ins "p" ("getelementptr i8, ptr " ++ base ++ ", i64 " ++ show offset)
                    fromPart p False
        -- the field is moved out of the value: what it held is left holding nothing
        TakeField s name field -> do
            (_, declared) <- constructorG program name
            case elemIndex field (map fst declared) of
                Nothing -> failG ("Variant " ++ name ++ " has no field " ++ field)
                Just i -> do
                    base <- dataBase fn (constructedType program name) (Copy s)
                    offset <- fieldOffsetG name declared i
                    p <- ins "p" ("getelementptr i8, ptr " ++ base ++ ", i64 " ++ show offset)
                    fromPart p True
        MakeData name fields -> do
            (tag, declared) <- constructorG program name
            values <-
                mapM
                    ( \(f, t) -> case lookup f fields of
                        Just o -> (,) t <$> elementValue fn t o
                        Nothing -> failG ("A field is missing: " ++ name ++ "." ++ f)
                    )
                    declared
            freeOld
            if tagWords program name == 1 then emit ("store i64 " ++ show tag ++ ", ptr " ++ target) else pure ()
            mapM_ (\(i, (t, v)) -> fieldOffsetG name declared i >>= \offset -> storeSlot t target offset v) (zip [0 ..] values)
        -- the same value, known to be that variant (a Box that is cast is taken out of its room, which is freed)
        AsVariant o _ -> do
            held <- operandLocalType fn o
            case (held, o) of
                (Just boxTy@(TBox _), _) -> do
                    block <- operandAt fn boxTy o
                    freeOld
                    copyWords target block bytes
                    case o of
                        Move _ -> emit ("call void @tersus_box_free(ptr " ++ block ++ ")")
                        _ -> pure ()
                _ -> do
                    src <- operandAddress fn ty o
                    freeOld
                    copyWords target src bytes
        Unbox o -> do
            held <- operandLocalType fn o
            boxTy <- maybe (failG "Box::unbox was given a constant") pure held
            block <- operandAt fn boxTy o
            freeOld
            copyWords target block bytes
            case o of
                Move _ -> emit ("call void @tersus_box_free(ptr " ++ block ++ ")")
                _ -> pure ()
        _ -> failG ("Native code does not support " ++ renderRvalue rv ++ " for a value held inline yet")

-- n copies of an element: one store of zeros when it is a zero, and a loop otherwise
fillArray :: Function -> String -> Type -> Integer -> Operand -> G ()
fillArray fn target elementTy n = fillElements fn target elementTy (show n) (Just n)

-- The same for a number of elements that the text gives (a number, or a value of the program), known if the program says so
fillElements :: Function -> String -> Type -> String -> Maybe Integer -> Operand -> G ()
fillElements fn target elementTy count known x
    | known == Just 0 = pure ()
    | zero x && not (isAggregate elementTy) = do
        bytes <- maybe (ins "z" ("mul i64 " ++ count ++ ", 8")) (pure . show . (8 *)) known
        emit ("call void @llvm.memset.p0.i64(ptr " ++ target ++ ", i8 0, i64 " ++ bytes ++ ", i1 false)")
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
        c <- ins "c" ("icmp slt i64 " ++ i ++ ", " ++ count)
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

-- The number of elements of an array operand
-- (the text of a number: a constant when the size is in the type, and what a Box of an array of no size carries otherwise)
arrayLength :: Function -> Operand -> G String
arrayLength fn o = case o of
    Const (CArray cs) -> pure (show (length cs))
    Copy l -> ofLocal l
    Move l -> ofLocal l
    Const _ -> failG ("Not an array: " ++ renderOperand' o)
  where
    ofLocal l = localTypeG fn l >>= \ty -> case ty of
        TArray _ n -> pure (show n)
        TBox (TArray _ n) -> pure (show n)
        TBox (TArrayOf _ SizeAny) -> ins "p" ("getelementptr i8, ptr " ++ slot l ++ ", i64 8") >>= \p -> ins "n" ("load i64, ptr " ++ p)
        _ -> failG ("Not an array: " ++ show l)

-- The text of the index of the last element, given the text of the length
lastIndex :: String -> G String
lastIndex count = case reads count :: [(Integer, String)] of
    [(n, "")] -> pure (show (n - 1))
    _ -> ins "i" ("sub i64 " ++ count ++ ", 1")

-- An element of an array that is a word, or its length
arrayRead :: Function -> Type -> ListOp -> [Operand] -> G String
arrayRead fn destType op os =
    case (op, os) of
        (Length, [a]) -> arrayLength fn a
        (First, [a]) -> arrayPtr fn a >>= \base -> loadElement destType base
        (Last, [a]) -> do
            index <- arrayLength fn a >>= lastIndex
            base <- arrayPtr fn a
            elementAddress base index 8 >>= loadElement destType
        -- the elements of a Box of an array are changed where they are, and the Box is given back (it is moved in, so nothing else has it)
        (Set, [a, i, x]) | TBox (TArrayOf elementTy _) <- destType -> do
            block <- operandAt fn destType a
            index <- operandAt fn TInt i
            value <- elementValue fn elementTy x
            writeElement elementTy block index value
            pure block
        (Get, [a, i]) -> do
            base <- arrayPtr fn a
            index <- operandAt fn TInt i
            elementAddress base index 8 >>= loadElement destType
        _ -> failG ("Native code does not support " ++ renderRvalue (ListOp op os) ++ " for an array yet")

-- The address of an element: a list is 24 bytes of header (count, length, capacity) and then the elements, stride words apart (an
-- element is a word, or the words of a value held inline)
elementSlot :: Integer -> String -> String -> G String
elementSlot stride list index = do
    elements <- ins "e" ("getelementptr i8, ptr " ++ list ++ ", i64 24")
    at <- if stride == 1 then pure index else ins "o" ("mul i64 " ++ index ++ ", " ++ show stride)
    ins "p" ("getelementptr i64, ptr " ++ elements ++ ", i64 " ++ at)

elementPtr :: String -> String -> G String
elementPtr = elementSlot 1

storeElement :: Type -> String -> String -> String -> G ()
storeElement t list index value = do
    stride <- slotsG t
    p <- elementSlot stride list index
    if isAggregate t then copyWords p value (8 * stride) else storeAt t p value

loadElement :: Type -> String -> G String
loadElement = loadAt

-- A slot of a struct or an enum value, at a byte offset
storeSlot :: Type -> String -> Integer -> String -> G ()
storeSlot t object offset value = do
    p <- ins "p" ("getelementptr i8, ptr " ++ object ++ ", i64 " ++ show offset)
    if isAggregate t then bytesG t >>= copyWords p value else storeAt t p value

loadSlot :: Type -> String -> Integer -> G String
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

-- Whether a value is the address of a value of the heap, which has one owner (a list, or a Box)
isPointer :: Type -> Bool
isPointer TList{} = True
isPointer ty@TBox{} = not (isFat ty)
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
binary (Compare rel) ty x y | isPointer ty || isAggregate ty = do
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
        Just ty | isAggregate ty -> do
            bytesG ty >>= copyWords "%ret" (slot (Local 0))
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
    if isAggregate returnType
        then do
            -- the callee makes a value held inline in the room it is given. If the local that gets it owns something, the room
            -- is one of the function's own and the local is given the value after what it held is freed; otherwise it is the slot
            -- of the local (the callee has copied its arguments by the time it writes, so the local may be one of them).
            owns <- ownsG returnType
            if owns
                then do
                    room <- slotsG returnType >>= entryTemp
                    emit ("call void " ++ target ++ "(" ++ intercalate ", " (("ptr " ++ room) : arguments) ++ ")")
                    dropSlot returnType dest
                    bytesG returnType >>= copyWords (slot dest) room
                else emit ("call void " ++ target ++ "(" ++ intercalate ", " (("ptr " ++ slot dest) : arguments) ++ ")")
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
    -- (a value held inline is the address of the words it is made of)
    if isAggregate ty then pure (slot l) else ins "v" ("load " ++ t ++ ", ptr " ++ slot l)
operandAt fn _ o@(Move l) = do
    ty <- localTypeG fn l
    t <- typeG ty
    if isAggregate ty
        then operandAddress fn ty o
        else do
            v <- ins "v" ("load " ++ t ++ ", ptr " ++ slot l)
            emit ("store " ++ t ++ " " ++ zeroOf t ++ ", ptr " ++ slot l)
            pure v
operandAt _ ty (Const c) = constantValue ty c

constantValue :: Type -> Constant -> G String
constantValue _ (CInt i) = pure (show i)
constantValue _ (CBool b) = pure (if b then "true" else "false")
constantValue ty c@CArray{} = constantAggregate ty c
constantValue ty c@CData{} = constantAggregate ty c
constantValue (TList t) (CList cs) = constantList t cs
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

-- Frees what the value a local holds owns (nothing, if it holds none), and leaves a list or a Box it held holding nothing
dropSlot :: Type -> Local -> G ()
dropSlot ty l = do
    d <- descriptor ty
    emit ("call void @tersus_drop(ptr " ++ d ++ ", ptr " ++ slot l ++ ")")

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
llvmType TBox{} = Ok "ptr"
llvmType TVariant{} = Ok "ptr"
llvmType TFn{} = Ok "ptr"
llvmType ty = Error (unsupportedType ty)

-- What a local takes in the frame: a word, or for a value held inline all the words it is made of
storageType :: Program -> Type -> Result String String
storageType program ty
    | isAggregate ty = Ok ("[" ++ show (slotsOf program ty) ++ " x i64]")
    | otherwise = llvmType ty

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
