module LlvmEmit
    ( emitProgram
    ) where

import Data.List (elemIndex, intercalate, nub)
import qualified Data.Map.Strict as Map
import Data.Maybe (listToMaybe)

import Mir
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
-- value is the address of the function. Nothing is freed yet. The runtime prints and compares values by a descriptor of
-- their type, a constant global `@"type.<type>"`.

emitProgram :: Program -> Result String String
emitProgram program =
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
    , "declare ptr @tersus_list_push(ptr, i64)"
    , "declare ptr @tersus_list_set(ptr, i64, i64)"
    , "declare ptr @tersus_data_new(i64, i64)"
    , ""
    ]

-- The C-level main: runs the program and prints its return value, if it returned one
entryPoint :: Program -> Function -> Result ([String], [Type]) String
entryPoint program fn =
    case fnReturns fn of
        Nothing -> Ok (wrap ["call void @tersus_main()", "ret i32 0"], [])
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
                                ++ ["call void @tersus_print(ptr " ++ typeSymbol program ty ++ ", i64 " ++ word ++ ")", "br label %done", "done:", "ret i32 0"]
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
        ++ [ "@\"str." ++ name ++ "\" = private constant [" ++ show (length name + 1) ++ " x i8] c\"" ++ name ++ "\\00\""
           | name <- nub (concat [v : map fst fields | TNamed n <- types, (v, fields) <- variantsOf program n])
           ]
        ++ [""]
  where
    body TInt = "{ i64 0, ptr null }"
    body TBool = "{ i64 1, ptr null }"
    body (TList t) = "{ i64 2, ptr " ++ typeSymbol program t ++ " }"
    body (TNamed n) = "{ i64 3, ptr @\"data." ++ n ++ "\" }"
    body (TFn _ _) = "{ i64 4, ptr null }"
    body _ = "{ i64 -1, ptr null }"
    dataDescriptor n =
        let variants = variantsOf program n
         in [ "@\"data." ++ n ++ "\" = private constant { i64, ptr } { i64 " ++ show (length variants) ++ ", ptr @\"variants." ++ n ++ "\" }"
            , "@\"variants." ++ n ++ "\" = private constant [" ++ show (length variants) ++ " x { ptr, i64, ptr }] ["
                ++ intercalate ", " ["{ ptr, i64, ptr } { ptr @\"str." ++ v ++ "\", i64 " ++ show (length fields) ++ ", ptr " ++ (if null fields then "null" else "@\"fields." ++ v ++ "\"") ++ " }" | (v, fields) <- variants]
                ++ "]"
            ]
                ++ [ "@\"fields." ++ v ++ "\" = private constant [" ++ show (length fields) ++ " x { ptr, ptr }] ["
                        ++ intercalate ", " ["{ ptr, ptr } { ptr @\"str." ++ f ++ "\", ptr " ++ typeSymbol program t ++ " }" | (f, t) <- fields]
                        ++ "]"
                   | (v, fields) <- variants
                   , not (null fields)
                   ]

typeSymbol :: Program -> Type -> String
typeSymbol program ty = "@\"type." ++ renderType (canonical program ty) ++ "\""

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
data S = S {sCount :: Int, sLines :: [String], sTypes :: [Type], sProgram :: Program}

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
            let returnType = if entry && fnReturns fn /= Nothing then resultStruct valueType else valueType
             in inFunction (flatResultMap (\(l, d) -> mapResult ((,) l) (llvmType (localType d))) (Map.toList (fnLocals fn))) `bindResult` \localTypes ->
                    let params = intercalate ", " [t ++ " %p." ++ localNumber p | (p, t) <- zip (fnParams fn) paramTypes]
                        header = "define internal " ++ returnType ++ " " ++ symbol ++ "(" ++ params ++ ") {"
                        prologue =
                            ["entry:"]
                                ++ ["    " ++ slot l ++ " = alloca " ++ t | (l, t) <- localTypes]
                                ++ ["    store " ++ t ++ " %p." ++ localNumber p ++ ", ptr " ++ slot p | (p, t) <- zip (fnParams fn) paramTypes]
                                ++ entryPrologue
                                ++ ["    br label %bb" ++ blockNumber (BlockId 0)]
                        entryPrologue =
                            if entry && fnReturns fn /= Nothing
                                then ["    %returned = alloca i1", "    store i1 false, ptr %returned", "    store " ++ valueType ++ " " ++ zeroOf valueType ++ ", ptr " ++ slot (Local 0)]
                                else []
                     in case runG (mapM_ (emitBlock program entry fn) (Map.toList (fnBlocks fn))) (S 0 [] [] program) of
                            Error e -> Error ("In " ++ fnName fn ++ ": " ++ e)
                            Ok (_, s) ->
                                Ok ([header] ++ prologue ++ reverse (sLines s) ++ overflowBlock ++ ["}"], sTypes s)
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
emitStatement entry fn (Assign dest rv) = do
    destType <- localTypeG fn dest
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
            ins "l" ("call ptr @tersus_list_set(ptr " ++ list ++ ", i64 " ++ index ++ ", i64 " ++ word ++ ")")
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
binary (Compare rel) ty x y | isPointer ty = do
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
    r <- ins "c" ("call " ++ result ++ " " ++ target ++ "(" ++ intercalate ", " (zipWith (\t v -> t ++ " " ++ v) paramTypes values) ++ ")")
    storeResult entry fn dest r
    emit ("br label %bb" ++ blockNumber next)

renderOperand' :: Operand -> String
renderOperand' o = renderRvalue (Use o)

-- The text that stands for an operand where a value of the type is wanted: the value loaded from the slot of a local, a
-- number or a Bool, or a list made from a constant (the type says what an empty one holds)
operandAt :: Function -> Type -> Operand -> G String
operandAt fn _ (Copy l) = do
    t <- localTypeG fn l >>= typeG
    ins "v" ("load " ++ t ++ ", ptr " ++ slot l)
operandAt _ ty (Const c) = constantValue ty c

constantValue :: Type -> Constant -> G String
constantValue _ (CInt i) = pure (show i)
constantValue _ (CBool b) = pure (if b then "true" else "false")
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
    local (Const _) = Nothing

-- The type of a constant, as far as its contents say: an empty list of lists is a List<List<Int>>
constantShape :: Program -> Constant -> Type
constantShape _ (CBool _) = TBool
constantShape program (CList cs) =
    case [c | c <- cs, constantKnown c] ++ cs of
        c : _ -> TList (constantShape program c)
        [] -> TList TInt
constantShape program (CData name _) = constructedType program name
constantShape program (CFn name) =
    case Map.lookup name (progFunctions program) of
        Just f -> TFn [maybe TInt localType (Map.lookup p (fnLocals f)) | p <- fnParams f] (maybe TInt id (fnReturns f))
        Nothing -> TInt
constantShape _ _ = TInt

-- Whether the contents of a constant say what it is made of: a number or a Bool is, and a list is when one element is
constantKnown :: Constant -> Bool
constantKnown (CList cs) = any constantKnown cs
constantKnown _ = True

-- Stores the result of a statement; in the entry, the return slot being assigned is what makes the program return a value
storeResult :: Bool -> Function -> Local -> String -> G ()
storeResult entry fn dest value = do
    store fn dest value
    if entry && dest == Local 0 then emit "store i1 true, ptr %returned" else pure ()

store :: Function -> Local -> String -> G ()
store fn dest value = do
    t <- localTypeG fn dest >>= typeG
    emit ("store " ++ t ++ " " ++ value ++ ", ptr " ++ slot dest)

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
llvmType TNamed{} = Ok "ptr"
llvmType TVariant{} = Ok "ptr"
llvmType TFn{} = Ok "ptr"
llvmType ty = Error (unsupportedType ty)

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
functionSymbol name = "@\"fn." ++ concatMap escape name ++ "\""
  where
    escape '"' = "\\22"
    escape '\\' = "\\5C"
    escape c = [c]
