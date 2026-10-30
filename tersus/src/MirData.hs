module MirData
    ( writeProgram
    , readProgram
    , forNative
    ) where

import Control.Monad (replicateM)
import qualified Data.Map.Strict as Map

import Mir
import TersusTypes (Name, Rel (..), Size (..), Type (..), Variable)
import Utils

-- The MIR of a program as text that a program can read (`tersus mir --data`): what native code is made from, and nothing else. It is the
-- owned MIR of MirOwnership with the validator's part left out (the ghost statements, the contracts, the structs with sizes and their
-- invariants), since the code that is made from it (LlvmEmit, and the emitter written in Tersus that replaces it, see STEP31.md) does not
-- use them. `readProgram (writeProgram p) = Ok (forNative p)`.
--
-- A line is a record: words and numbers separated by one space, and names in quotes (the UTF-8 bytes of the name, those that are printable
-- ASCII as they are and the others, `"` and `\` as `\xHH`), so the text is ASCII and a reader needs no more than a line, its words and its
-- numbers. The first line is `tersus-mir 1`. The types come first (a `struct` or an `enum`), then the functions in the order of their
-- names, then `main`; the order is that of the maps they were in, which the emitter keeps. A function is its `function` line, a `local`
-- line for each local, and for each block a `block` line, its statements and the line of its terminator, and an `end` line:
--
--     struct "Point" 2 "x" int "y" int
--     enum "Shape" 2 "Shape::Circle" 1 "radius" int "Shape::Empty" 0
--     function "double" params 1 1 returns some int sizeparams 0 typeparams 0 borrowed 0
--     local 0 none int
--     local 1 some "n" int
--     block 0
--     assign 0 binary add copy 1 copy 1
--     return
--     end
--
-- The words of a type are `int byte bool`, `i8 i16 i32 u16 u32`, `list T`, `array T SIZE`, `box T`, `addr T`, `block T`, `fn N T... T`, `named "n"`, `variant "n"`, `var N`,
-- `forall N "n"... N "n"... T`, `param "n"` and `ref T`, and of a size `c N`, `any`, `p "n"` and `v N`. An operand is `copy L`, `move L` or
-- `const C`, a constant `int N`, `bool true`, `list N C...`, `array N C...`, `data "n" N ("f" C)...` or `fn "n"`. The statements are
-- `assign L RVALUE`, `peek L RVALUE` and `drop L`; the terminators `goto B`, `switch O B B`, `call O N O... L B`, `return` and `unreachable`.

-- What native code uses of a program: the same without the validator's part
forNative :: Program -> Program
forNative program =
    program
        { progFunctions = Map.map plain (progFunctions program)
        , progMain = plain (progMain program)
        , progGenerics = Map.empty
        , progInvariants = Map.empty
        }
  where
    plain f = f{fnSpec = emptySpec, fnBlocks = Map.map (\(BasicBlock stmts term) -> BasicBlock (filter (not . ghost) stmts) term) (fnBlocks f)}
    ghost s = case s of
        Ghost _ _ -> True
        _ -> False

-- Writing

writeProgram :: Program -> String
writeProgram program =
    unlines
        ( "tersus-mir 1"
            : concatMap typeLines (Map.toList (progTypes native))
            ++ concatMap (functionLines "function") (Map.elems (progFunctions native))
            ++ functionLines "main" (progMain native)
        )
  where
    native = forNative program

typeLines :: (Name, TypeDecl) -> [String]
typeLines (name, StructDecl fields) = [unwords (["struct", quote name, show (length fields)] ++ concatMap fieldTokens fields)]
typeLines (name, EnumDecl variants) =
    [unwords (["enum", quote name, show (length variants)] ++ concat [quote v : show (length fields) : concatMap fieldTokens fields | (v, fields) <- variants])]

fieldTokens :: (Variable, Type) -> [String]
fieldTokens (f, t) = quote f : typeTokens t

functionLines :: String -> Function -> [String]
functionLines kind fn =
    unwords
        ( [kind, quote (fnName fn), "params", show (length (fnParams fn))]
            ++ map localText (fnParams fn)
            ++ ["returns"]
            ++ maybe ["none"] (\t -> "some" : typeTokens t) (fnReturns fn)
            ++ ["sizeparams", show (length (fnSizeParams fn))]
            ++ map quote (fnSizeParams fn)
            ++ ["typeparams", show (length (fnTypeParams fn))]
            ++ map quote (fnTypeParams fn)
            ++ ["borrowed", show (length (fnBorrowed fn))]
            ++ map localText (fnBorrowed fn)
        )
        : [ unwords (["local", localText l] ++ maybe ["none"] (\n -> ["some", quote n]) (localName d) ++ typeTokens (localType d))
          | (l, d) <- Map.toList (fnLocals fn)
          ]
            ++ concat [("block " ++ blockText b) : map statementText stmts ++ [terminatorText term] | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn)]
            ++ ["end"]

localText :: Local -> String
localText (Local n) = show n

blockText :: BlockId -> String
blockText (BlockId n) = show n

typeTokens :: Type -> [String]
typeTokens ty = case ty of
    TInt -> ["int"]
    TByte -> ["byte"]
    TWord signed bits -> [(if signed then "i" else "u") ++ show bits]
    TBool -> ["bool"]
    TList t -> "list" : typeTokens t
    TArrayOf t s -> "array" : typeTokens t ++ sizeTokens s
    TBox t -> "box" : typeTokens t
    TAddr t -> "addr" : typeTokens t
    TUninit t -> "uninit" : typeTokens t
    TBlock t -> "block" : typeTokens t
    TFn args ret -> ["fn", show (length args)] ++ concatMap typeTokens (args ++ [ret])
    TNamed n -> ["named", quote n]
    TVariant n -> ["variant", quote n]
    TVar i -> ["var", show i]
    TForall sizes types t -> ["forall", show (length sizes)] ++ map quote sizes ++ [show (length types)] ++ map quote types ++ typeTokens t
    TParam n -> ["param", quote n]
    TRef t -> "ref" : typeTokens t

sizeTokens :: Size -> [String]
sizeTokens s = case s of
    SizeConst n -> ["c", show n]
    SizeAny -> ["any"]
    SizeParam n -> ["p", quote n]
    SizeVar i -> ["v", show i]

statementText :: Statement -> String
statementText s = case s of
    Assign l rv -> unwords ("assign" : localText l : rvalueTokens rv)
    Peek l rv -> unwords ("peek" : localText l : rvalueTokens rv)
    Drop l -> unwords ["drop", localText l]
    Ghost _ _ -> error "MirData: a ghost statement is not data (see forNative)"

terminatorText :: Terminator -> String
terminatorText t = case t of
    Goto b -> unwords ["goto", blockText b]
    SwitchBool o yes no -> unwords (["switch"] ++ operandTokens o ++ [blockText yes, blockText no])
    Call callee args dest next -> unwords (["call"] ++ operandTokens callee ++ [show (length args)] ++ concatMap operandTokens args ++ [localText dest, blockText next])
    Return -> "return"
    Unreachable -> "unreachable"

rvalueTokens :: Rvalue -> [String]
rvalueTokens rv = case rv of
    Use o -> "use" : operandTokens o
    BinaryOp op a b -> "binary" : binOpWord op : operandTokens a ++ operandTokens b
    ListOp op os -> ["listop", listOpWord op, show (length os)] ++ concatMap operandTokens os
    MakeList os -> ["makelist", show (length os)] ++ concatMap operandTokens os
    MakeBox o -> "makebox" : operandTokens o
    Unbox o -> "unbox" : operandTokens o
    Unsize o -> "unsize" : operandTokens o
    MakeData name fields -> ["makedata", quote name, show (length fields)] ++ concat [quote f : operandTokens o | (f, o) <- fields]
    ReadField o name field -> "readfield" : operandTokens o ++ [quote name, quote field]
    IsVariant o name -> "isvariant" : operandTokens o ++ [quote name]
    AsVariant o name -> "asvariant" : operandTokens o ++ [quote name]
    Clone o -> "clone" : operandTokens o
    TakeField l name field -> ["takefield", localText l, quote name, quote field]

operandTokens :: Operand -> [String]
operandTokens o = case o of
    Copy l -> ["copy", localText l]
    Move l -> ["move", localText l]
    Const c -> "const" : constantTokens c

constantTokens :: Constant -> [String]
constantTokens c = case c of
    CInt n -> ["int", show n]
    CBool b -> ["bool", if b then "true" else "false"]
    CList cs -> ["list", show (length cs)] ++ concatMap constantTokens cs
    CArray cs -> ["array", show (length cs)] ++ concatMap constantTokens cs
    CData name fields -> ["data", quote name, show (length fields)] ++ concat [quote f : constantTokens v | (f, v) <- fields]
    CFn name -> ["fn", quote name]

binOpWord :: BinOp -> String
binOpWord op = case op of
    Add -> "add"
    Sub -> "sub"
    Mul -> "mul"
    Div -> "div"
    Mod -> "mod"
    Compare Eq -> "eq"
    Compare NotEq -> "noteq"
    Compare Lt -> "lt"
    Compare LtEq -> "lteq"
    Compare Gt -> "gt"
    Compare GtEq -> "gteq"

binOps :: [(String, BinOp)]
binOps = [(binOpWord op, op) | op <- [Add, Sub, Mul, Div, Mod] ++ map Compare [Eq, NotEq, Lt, LtEq, Gt, GtEq]]

listOps :: [(String, ListOp)]
listOps =
    [ ("length", Length), ("first", First), ("last", Last), ("get", Get), ("push", Push), ("pop", Pop), ("set", Set)
    , ("newArray", NewArray), ("newBoxed", NewBoxed), ("newEmptyBoxed", NewEmptyBoxed)
    , ("writeByte", WriteByte), ("writeError", WriteError), ("readByte", ReadByte), ("argCount", ArgCount), ("argByte", ArgByte)
    , ("pathByte", PathByte), ("fileLoad", FileLoad), ("fileByte", FileByte), ("storeByte", StoreByte), ("fileStore", FileStore)
    , ("toByte", ToByte), ("fromByte", FromByte)
    , ("addrNull", AddrNull), ("addrOffset", AddrOffset), ("addrCast", AddrCast), ("addrToInt", AddrToInt), ("addrFromInt", AddrFromInt)
    , ("addrAlloc", AddrAlloc), ("addrGet", AddrGet), ("addrWrite", AddrWrite), ("addrTake", AddrTake), ("addrDropValue", AddrDropValue)
    , ("addrDropRange", AddrDropRange), ("addrResize", AddrResize), ("addrFree", AddrFree)
    , ("blockNew", BlockNew), ("blockTaken", BlockTaken), ("blockResized", BlockResized), ("blockSplitLo", BlockSplitLo)
    , ("blockSplitHi", BlockSplitHi), ("blockJoin", BlockJoin), ("blockAssume", BlockAssume), ("blockCast", BlockCast)
    , ("narrowI8", Narrow True 8), ("narrowI16", Narrow True 16), ("narrowI32", Narrow True 32), ("narrowU16", Narrow False 16), ("narrowU32", Narrow False 32)
    , ("uninitEmpty", UninitEmpty), ("uninitNew", UninitNew), ("uninitGet", UninitGet), ("uninitTake", UninitTake), ("uninitDiscard", UninitDiscard)
    ]

listOpWord :: ListOp -> String
listOpWord op = head ([w | (w, o) <- listOps, o == op] ++ error "MirData: a list operation without a word")

-- A name in quotes: the UTF-8 bytes of it, those that are printable ASCII as they are and the others as `\xHH`
quote :: String -> String
quote name = '"' : concatMap byteText (encodeUtf8 name) ++ "\""
  where
    byteText c
        | n >= 32 && n < 127 && c /= '"' && c /= '\\' = [c]
        | otherwise = ['\\', 'x', hexDigit (n `div` 16), hexDigit (n `mod` 16)]
      where
        n = fromEnum c
    hexDigit d = "0123456789ABCDEF" !! d

-- Reading

data Token = Word String | Str String
    deriving (Eq, Show)

tokenize :: String -> Result [Token] String
tokenize text = case text of
    [] -> Ok []
    ' ' : rest -> tokenize rest
    '"' : rest -> quoted rest [] `bindResult` \(name, more) -> mapResult (Str (decodeUtf8 name) :) (tokenize more)
    _ ->
        let (w, more) = break (== ' ') text
         in mapResult (Word w :) (tokenize more)
  where
    quoted s acc = case s of
        '"' : more -> Ok (reverse acc, more)
        '\\' : 'x' : h : l : more | Just a <- hexValue h, Just b <- hexValue l -> quoted more (toEnum (16 * a + b) : acc)
        '\\' : _ -> Error "a bad escape in a name"
        c : more -> quoted more (c : acc)
        [] -> Error "a name that is not closed"
    hexValue c
        | c >= '0' && c <= '9' = Just (fromEnum c - fromEnum '0')
        | c >= 'A' && c <= 'F' = Just (fromEnum c - fromEnum 'A' + 10)
        | otherwise = Nothing

-- A parser of the tokens of a line
newtype P a = P {runP :: [Token] -> Result (a, [Token]) String}

instance Functor P where
    fmap f (P g) = P (\ts -> mapResult (\(a, rest) -> (f a, rest)) (g ts))

instance Applicative P where
    pure a = P (\ts -> Ok (a, ts))
    P f <*> P g = P (\ts -> f ts `bindResult` \(h, rest) -> mapResult (\(a, rest') -> (h a, rest')) (g rest))

instance Monad P where
    P g >>= f = P (\ts -> g ts `bindResult` \(a, rest) -> runP (f a) rest)

failP :: String -> P a
failP e = P (\_ -> Error e)

word :: P String
word = P (\ts -> case ts of
    Word w : rest -> Ok (w, rest)
    _ -> Error "a word was expected")

name :: P String
name = P (\ts -> case ts of
    Str s : rest -> Ok (s, rest)
    _ -> Error "a name was expected")

expect :: String -> P ()
expect w = word >>= \found -> if found == w then pure () else failP ("expected " ++ w ++ ", found " ++ found)

integer :: P Integer
integer = word >>= \w -> case reads w of
    [(n, "")] -> pure n
    _ -> failP ("a number was expected, found " ++ w)

int :: P Int
int = fromInteger <$> integer

-- A line parsed whole
parseLine :: P a -> [Token] -> Result a String
parseLine p ts = runP p ts `bindResult` \(a, rest) -> if null rest then Ok a else Error "a line has more in it than it should"

local :: P Local
local = Local <$> int

block :: P BlockId
block = BlockId <$> int

typeP :: P Type
typeP = word >>= \w -> case w of
    "int" -> pure TInt
    "byte" -> pure TByte
    "i8" -> pure (TWord True 8)
    "i16" -> pure (TWord True 16)
    "i32" -> pure (TWord True 32)
    "u16" -> pure (TWord False 16)
    "u32" -> pure (TWord False 32)
    "bool" -> pure TBool
    "list" -> TList <$> typeP
    "array" -> TArrayOf <$> typeP <*> sizeP
    "box" -> TBox <$> typeP
    "addr" -> TAddr <$> typeP
    "block" -> TBlock <$> typeP
    "fn" -> int >>= \n -> replicateM n typeP >>= \args -> TFn args <$> typeP
    "named" -> TNamed <$> name
    "variant" -> TVariant <$> name
    "var" -> TVar <$> int
    "forall" -> do
        sizes <- int >>= \n -> replicateM n name
        types <- int >>= \n -> replicateM n name
        TForall sizes types <$> typeP
    "param" -> TParam <$> name
    "ref" -> TRef <$> typeP
    _ -> failP ("not a type: " ++ w)

sizeP :: P Size
sizeP = word >>= \w -> case w of
    "c" -> SizeConst <$> integer
    "any" -> pure SizeAny
    "p" -> SizeParam <$> name
    "v" -> SizeVar <$> int
    _ -> failP ("not a size: " ++ w)

operandP :: P Operand
operandP = word >>= \w -> case w of
    "copy" -> Copy <$> local
    "move" -> Move <$> local
    "const" -> Const <$> constantP
    _ -> failP ("not an operand: " ++ w)

constantP :: P Constant
constantP = word >>= \w -> case w of
    "int" -> CInt <$> integer
    "bool" -> word >>= \b -> case b of
        "true" -> pure (CBool True)
        "false" -> pure (CBool False)
        _ -> failP ("not a Bool: " ++ b)
    "list" -> CList <$> (int >>= \n -> replicateM n constantP)
    "array" -> CArray <$> (int >>= \n -> replicateM n constantP)
    "data" -> CData <$> name <*> (int >>= \n -> replicateM n ((,) <$> name <*> constantP))
    "fn" -> CFn <$> name
    _ -> failP ("not a constant: " ++ w)

rvalueP :: P Rvalue
rvalueP = word >>= \w -> case w of
    "use" -> Use <$> operandP
    "binary" -> word >>= \o -> maybe (failP ("not an operator: " ++ o)) (\op -> BinaryOp op <$> operandP <*> operandP) (lookup o binOps)
    "listop" -> word >>= \o -> maybe (failP ("not a list operation: " ++ o)) (\op -> ListOp op <$> (int >>= \n -> replicateM n operandP)) (lookup o listOps)
    "makelist" -> MakeList <$> (int >>= \n -> replicateM n operandP)
    "makebox" -> MakeBox <$> operandP
    "unbox" -> Unbox <$> operandP
    "unsize" -> Unsize <$> operandP
    "makedata" -> MakeData <$> name <*> (int >>= \n -> replicateM n ((,) <$> name <*> operandP))
    "readfield" -> ReadField <$> operandP <*> name <*> name
    "isvariant" -> IsVariant <$> operandP <*> name
    "asvariant" -> AsVariant <$> operandP <*> name
    "clone" -> Clone <$> operandP
    "takefield" -> TakeField <$> local <*> name <*> name
    _ -> failP ("not an rvalue: " ++ w)

data Line = LStatement Statement | LTerminator Terminator

lineP :: P Line
lineP = word >>= \w -> case w of
    "assign" -> LStatement <$> (Assign <$> local <*> rvalueP)
    "peek" -> LStatement <$> (Peek <$> local <*> rvalueP)
    "drop" -> LStatement . Drop <$> local
    "goto" -> LTerminator . Goto <$> block
    "switch" -> LTerminator <$> (SwitchBool <$> operandP <*> block <*> block)
    "call" -> do
        callee <- operandP
        args <- int >>= \n -> replicateM n operandP
        LTerminator <$> (Call callee args <$> local <*> block)
    "return" -> pure (LTerminator Return)
    "unreachable" -> pure (LTerminator Unreachable)
    _ -> failP ("not a statement or a terminator: " ++ w)

-- The header of a function, without the locals and blocks that follow it
headerP :: P Function
headerP = do
    fname <- name
    expect "params"
    params <- int >>= \n -> replicateM n local
    expect "returns"
    returns <- word >>= \w -> case w of
        "none" -> pure Nothing
        "some" -> Just <$> typeP
        _ -> failP ("not none or some: " ++ w)
    expect "sizeparams"
    sizeParams <- int >>= \n -> replicateM n name
    expect "typeparams"
    typeParams <- int >>= \n -> replicateM n name
    expect "borrowed"
    borrowed <- int >>= \n -> replicateM n local
    pure (Function fname params returns Map.empty Map.empty sizeParams typeParams borrowed emptySpec)

localDeclP :: P (Local, LocalDecl)
localDeclP = do
    l <- local
    source <- word >>= \w -> case w of
        "none" -> pure Nothing
        "some" -> Just <$> name
        _ -> failP ("not none or some: " ++ w)
    t <- typeP
    pure (l, LocalDecl t source)

readProgram :: String -> Result Program String
readProgram text = case lines text of
    "tersus-mir 1" : rest ->
        flatResultMap tokenize (filter (not . null) rest) `bindResult` \records -> fileFrom records ([], [], Nothing)
    _ -> Error "not the MIR as data: the first line should be tersus-mir 1"

-- The records of the file, with the types, the functions and the main that were read (last first)
fileFrom :: [[Token]] -> ([(Name, TypeDecl)], [Function], Maybe Function) -> Result Program String
fileFrom [] (types, fns, Just mainFn) =
    Ok (Program (Map.fromList (reverse types)) (Map.fromList [(fnName f, f) | f <- reverse fns]) mainFn Map.empty Map.empty)
fileFrom [] _ = Error "the program has no main"
fileFrom (record : rest) (types, fns, mainFn) = case record of
    Word "struct" : ts -> parseLine structP ts `bindResult` \d -> fileFrom rest (d : types, fns, mainFn)
    Word "enum" : ts -> parseLine enumP ts `bindResult` \d -> fileFrom rest (d : types, fns, mainFn)
    Word "function" : ts -> functionFrom ts rest `bindResult` \(f, rest') -> fileFrom rest' (types, f : fns, mainFn)
    Word "main" : ts
        | Nothing <- mainFn -> functionFrom ts rest `bindResult` \(f, rest') -> fileFrom rest' (types, fns, Just f)
        | otherwise -> Error "the program has two mains"
    _ -> Error ("not a record of the MIR: " ++ show (take 1 record))

structP :: P (Name, TypeDecl)
structP = (,) <$> name <*> (StructDecl <$> fieldsP)

enumP :: P (Name, TypeDecl)
enumP = (,) <$> name <*> (EnumDecl <$> (int >>= \n -> replicateM n ((,) <$> name <*> fieldsP)))

fieldsP :: P [(Variable, Type)]
fieldsP = int >>= \n -> replicateM n ((,) <$> name <*> typeP)

-- A function: its header (given), its locals, its blocks and the line that ends it
functionFrom :: [Token] -> [[Token]] -> Result (Function, [[Token]]) String
functionFrom header rest =
    parseLine headerP header `bindResult` \fn ->
        localsFrom rest `bindResult` \(decls, rest1) ->
            blocksFrom rest1 `bindResult` \(blocks, rest2) ->
                Ok (fn{fnLocals = Map.fromList decls, fnBlocks = Map.fromList blocks}, rest2)

localsFrom :: [[Token]] -> Result ([(Local, LocalDecl)], [[Token]]) String
localsFrom (record : rest)
    | Word "local" : ts <- record = parseLine localDeclP ts `bindResult` \d -> mapResult (\(ds, r) -> (d : ds, r)) (localsFrom rest)
localsFrom rest = Ok ([], rest)

blocksFrom :: [[Token]] -> Result ([(BlockId, BasicBlock)], [[Token]]) String
blocksFrom (record : rest)
    | [Word "end"] <- record = Ok ([], rest)
    | Word "block" : ts <- record =
        parseLine block ts `bindResult` \b ->
            bodyFrom rest [] `bindResult` \(body, rest') -> mapResult (\(bs, r) -> ((b, body) : bs, r)) (blocksFrom rest')
blocksFrom _ = Error "a function that is not ended by end, or a line that is not a block"

-- The statements of a block and the terminator that ends it
bodyFrom :: [[Token]] -> [Statement] -> Result (BasicBlock, [[Token]]) String
bodyFrom [] _ = Error "a block without a terminator"
bodyFrom (record : rest) stmts =
    parseLine lineP record `bindResult` \l -> case l of
        LStatement s -> bodyFrom rest (s : stmts)
        LTerminator term -> Ok (BasicBlock (reverse stmts) term, rest)
