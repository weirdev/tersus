{-# LANGUAGE PatternSynonyms #-}

module MirData
    ( writeProgram
    , writeProgramWithGhosts
    , readProgram
    , forNative
    , writeLowered
    , readLowered
    , readLoweredBytes
    ) where

import Control.Monad (replicateM)
import qualified Data.ByteString.Char8 as B
import Data.List (sort, sortOn)
import DataCodec
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AstData (readMirPayloadBytes, writeMirPayloadLines)
import Mir
import qualified Syntax as S
import Types (Arg (..), Name, Rel (..), Size (..), Type (..), pattern TList, pattern TBox, Variable)
import Utils

-- The MIR of a program as text that a program can read (`tersus mir --data`): what native code is made from, and nothing else. It is the
-- owned MIR of the ownership pass with the validator's part left out (the ghost statements, the contracts, the structs with sizes and their
-- invariants), since the code that is made from it (the emitter written in Tersus, see STEP31.md) does not
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
-- The words of a type are `int byte bool`, `i8 i16 i32 u16 u32`, `list T`, `array T SIZE`, `box T`, `addr T`, `block T`, `uninit T`, `fn N T... T`, `named "n" N ARG...` (each ARG `size SIZE` or `type T`), `variant "n"`, `var N`,
-- `forall N "n"... N "n"... T`, `param "n"`, `ref T` and `mutref T`, and of a size `c N`, `any`, `p "n"` and `v N`. An operand is `copy L`, `move L` or
-- `const C`, a constant `int N`, `bool true`, `list N C...`, `array N C...`, `data "n" N ("f" C)...` or `fn "n"`. The statements are
-- `assign L RVALUE`, `peek L RVALUE` and `drop L`; the terminators `goto B`, `switch O B B`, `call O N O... L B`, `return` and `unreachable`.
--
-- `writeProgramWithGhosts` writes `tersus-mir 2` instead: the program before erasure, or the ownership tool's transport.
-- Ordinary ghosts are `ghost`; ownership markers are `ghost N` with a nonnegative ID and round-trip as wire-only
-- `GhostPosition (-1) N`. The ownership host replaces every original ghost (including dissolve) with a unique marker
-- and restores its payload by identity, rather than statement offset. The eraser still receives `dissolve L` for a
-- dissolve and writes version 1. Generic templates, invariants and function specifications stay in host sidecars.
--
-- `writeLowered` writes `tersus-mir 3`: a whole unit as lowering gives it (Mir.Lowered), with everything the
-- validator uses. The validator's statements are records of the AST data in a block at the end, referred to by
-- index (MIR.md, "Version 3").

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

-- The program before its ghosts are erased, as version 2 of the data (see the note at the head of this module)
writeProgramWithGhosts :: Program -> String
writeProgramWithGhosts program =
    unlines
        ( "tersus-mir 2"
            : concatMap typeLines (Map.toList (progTypes program))
            ++ concatMap (functionLinesWith statementTextWithGhosts "function") (Map.elems (progFunctions program))
            ++ functionLinesWith statementTextWithGhosts "main" (progMain program)
        )

typeLines :: (Name, TypeDecl) -> [String]
typeLines (name, StructDecl fields) = [unwords (["struct", quote name, show (length fields)] ++ concatMap fieldTokens fields)]
typeLines (name, EnumDecl variants) =
    [unwords (["enum", quote name, show (length variants)] ++ concat [quote v : show (length fields) : concatMap fieldTokens fields | (v, fields) <- variants])]

fieldTokens :: (Variable, Type) -> [String]
fieldTokens (f, t) = quote f : typeTokens t

functionLines :: String -> Function -> [String]
functionLines = functionLinesWith statementText

functionLinesWith :: (Statement -> String) -> String -> Function -> [String]
functionLinesWith statementText kind fn =
    headerText kind fn
        : localLines fn
        ++ concat [("block " ++ blockText b) : map statementText stmts ++ [terminatorText term] | (b, BasicBlock stmts term) <- Map.toList (fnBlocks fn)]
        ++ ["end"]

headerText :: String -> Function -> String
headerText kind fn =
    let mutBorrowedLocals = fnMutBorrowed fn
        fromLocals = fnFrom fn
     in unwords
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
            ++ (if null mutBorrowedLocals && null fromLocals then [] else ["mutborrowed", show (length mutBorrowedLocals)] ++ map localText mutBorrowedLocals ++ ["from", show (length fromLocals)] ++ map localText fromLocals)
        )

localLines :: Function -> [String]
localLines fn =
    [ unwords (["local", localText l] ++ maybe ["none"] (\n -> ["some", quote n]) (localName d) ++ typeTokens (localType d))
    | (l, d) <- Map.toList (fnLocals fn)
    ]

localText :: Local -> String
localText (Local n) = show n

blockText :: BlockId -> String
blockText (BlockId n) = show n

statementText :: Statement -> String
statementText s = case s of
    Assign l rv -> unwords ("assign" : localText l : rvalueTokens rv)
    Peek l rv -> unwords ("peek" : localText l : rvalueTokens rv)
    Drop l -> unwords ["drop", localText l]
    AssignRef root steps rv -> unwords ("assignref" : localText root : show (length steps) : concatMap refStepTokens steps ++ rvalueTokens rv)
    Ghost _ _ -> error "MirData: a ghost statement is not data (see forNative)"

statementTextWithGhosts :: Statement -> String
statementTextWithGhosts s = case s of
    Ghost _ (GhostPosition (-1) ident) | ident >= 0 -> "ghost " ++ show ident
    Ghost _ (GhostDissolve l) -> unwords ["dissolve", localText l]
    Ghost _ _ -> "ghost"
    _ -> statementText s

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
    CopyOf o -> "clone" : operandTokens o
    TakeField l name field -> ["takefield", localText l, quote name, quote field]
    Borrow root steps mutable -> (if mutable then "borrowmut" else "borrow") : localText root : show (length steps) : concatMap refStepTokens steps
    Deref o -> "deref" : operandTokens o

refStepTokens :: RefStep -> [String]
refStepTokens (RefField ctor field) = ["field", quote ctor, quote field]
refStepTokens (RefIndex o) = "index" : operandTokens o

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
    , ("newArray", NewArray), ("newBoxed", NewBoxed), ("newEmptyBoxed", NewEmptyBoxed), ("fromList", FromList)
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

local :: P Local
local = Local <$> int

block :: P BlockId
block = BlockId <$> int

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
    "list" -> CList <$> (itemCount >>= \n -> replicateM n constantP)
    "array" -> CArray <$> (itemCount >>= \n -> replicateM n constantP)
    "data" -> CData <$> name <*> (itemCount >>= \n -> replicateM n ((,) <$> name <*> constantP))
    "fn" -> CFn <$> name
    _ -> failP ("not a constant: " ++ w)

rvalueP :: P Rvalue
rvalueP = word >>= \w -> case w of
    "use" -> Use <$> operandP
    "binary" -> word >>= \o -> maybe (failP ("not an operator: " ++ o)) (\op -> BinaryOp op <$> operandP <*> operandP) (lookup o binOps)
    "listop" -> word >>= \o -> maybe (failP ("not a list operation: " ++ o)) (\op -> ListOp op <$> (itemCount >>= \n -> replicateM n operandP)) (lookup o listOps)
    "makelist" -> MakeList <$> (itemCount >>= \n -> replicateM n operandP)
    "makebox" -> MakeBox <$> operandP
    "unbox" -> Unbox <$> operandP
    "unsize" -> Unsize <$> operandP
    "makedata" -> MakeData <$> name <*> (itemCount >>= \n -> replicateM n ((,) <$> name <*> operandP))
    "readfield" -> ReadField <$> operandP <*> name <*> name
    "isvariant" -> IsVariant <$> operandP <*> name
    "asvariant" -> AsVariant <$> operandP <*> name
    "clone" -> CopyOf <$> operandP
    "takefield" -> TakeField <$> local <*> name <*> name
    "borrow" -> Borrow <$> local <*> (itemCount >>= \n -> replicateM n refStepP) <*> pure False
    "borrowmut" -> Borrow <$> local <*> (itemCount >>= \n -> replicateM n refStepP) <*> pure True
    "deref" -> Deref <$> operandP
    _ -> failP ("not an rvalue: " ++ w)

refStepP :: P RefStep
refStepP = word >>= \w -> case w of
    "field" -> RefField <$> name <*> name
    "index" -> RefIndex <$> operandP
    _ -> failP ("not a reference step: " ++ w)

data Line = LStatement Statement | LTerminator Terminator

lineP :: P Line
lineP = word >>= \w -> case w of
    "assign" -> LStatement <$> (Assign <$> local <*> rvalueP)
    "peek" -> LStatement <$> (Peek <$> local <*> rvalueP)
    "drop" -> LStatement . Drop <$> local
    "assignref" -> LStatement <$> (AssignRef <$> local <*> (itemCount >>= \n -> replicateM n refStepP) <*> rvalueP)
    "ghost" -> LStatement . Ghost Map.empty . GhostPosition (-1) <$> optionalGhostId
    "dissolve" -> LStatement . Ghost Map.empty . GhostDissolve <$> local
    "goto" -> LTerminator . Goto <$> block
    "switch" -> LTerminator <$> (SwitchBool <$> operandP <*> block <*> block)
    "call" -> do
        callee <- operandP
        args <- itemCount >>= \n -> replicateM n operandP
        LTerminator <$> (Call callee args <$> local <*> block)
    "return" -> pure (LTerminator Return)
    "unreachable" -> pure (LTerminator Unreachable)
    _ -> failP ("not a statement or a terminator: " ++ w)

optionalGhostId :: P Int
optionalGhostId = P (\ts -> case ts of
    [] -> Ok ((-1), [])
    _ -> runP (do
        ident <- int
        if ident < 0 then failP "a ghost ID must be nonnegative" else pure ident) ts)

-- The header of a function, without the locals and blocks that follow it
headerP :: P Function
headerP = do
    fname <- name
    expect "params"
    params <- itemCount >>= \n -> replicateM n local
    expect "returns"
    returns <- word >>= \w -> case w of
        "none" -> pure Nothing
        "some" -> Just <$> typeP
        _ -> failP ("not none or some: " ++ w)
    expect "sizeparams"
    sizeParams <- itemCount >>= \n -> replicateM n name
    expect "typeparams"
    typeParams <- itemCount >>= \n -> replicateM n name
    expect "borrowed"
    borrowed <- itemCount >>= \n -> replicateM n local
    (mutBorrowed, fromLocals) <- optionalRefHeader
    pure (Function fname params returns Map.empty Map.empty sizeParams typeParams borrowed mutBorrowed fromLocals emptySpec)

optionalRefHeader :: P ([Local], [Local])
optionalRefHeader = P (\ts -> case ts of
    Word "mutborrowed" : rest -> runP (do
        mutBorrowed <- itemCount >>= \n -> replicateM n local
        expect "from"
        fromLocals <- itemCount >>= \n -> replicateM n local
        pure (mutBorrowed, fromLocals)) rest
    _ -> Ok (([], []), ts))

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
    "tersus-mir 1" : rest -> readRecords rest
    "tersus-mir 2" : rest -> readRecords rest
    _ -> Error "not the MIR as data: the first line should be tersus-mir 1 or 2"
  where
    readRecords rest = flatResultMap tokenize (filter (not . null) rest) `bindResult` \records -> fileFrom records ([], [], Nothing)

-- The records of the file, with the types, the functions and the main that were read (last first)
fileFrom :: [[Token]] -> ([(Name, TypeDecl)], [Function], Maybe Function) -> Result Program String
fileFrom [] (types, fns, Just mainFn) =
    unique "type" (map fst types) `bindResult` \_ ->
        unique "function" (map fnName fns) `bindResult` \_ ->
            Ok (Program (Map.fromList (reverse types)) (Map.fromList [(fnName f, f) | f <- reverse fns]) mainFn Map.empty Map.empty Map.empty Map.empty)
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
enumP = (,) <$> name <*> (EnumDecl <$> (itemCount >>= \n -> replicateM n ((,) <$> name <*> fieldsP)))

fieldsP :: P [(Variable, Type)]
fieldsP = itemCount >>= \n -> replicateM n ((,) <$> name <*> typeP)

-- A function: its header (given), its locals, its blocks and the line that ends it
functionFrom :: [Token] -> [[Token]] -> Result (Function, [[Token]]) String
functionFrom header rest =
    parseLine headerP header `bindResult` \fn ->
        localsFrom rest `bindResult` \(decls, rest1) ->
            blocksFrom rest1 `bindResult` \(blocks, rest2) ->
                unique "local" (map fst decls) `bindResult` \_ ->
                    unique "block" (map fst blocks) `bindResult` \_ ->
                        Ok (fn{fnLocals = Map.fromList decls, fnBlocks = Map.fromList blocks}, rest2)

unique :: Ord a => String -> [a] -> Result () String
unique kind keys
    | length keys == Set.size (Set.fromList keys) = Ok ()
    | otherwise = Error ("duplicate " ++ kind ++ " records")

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

-- Version 3: a lowered unit

-- The payloads met so far while writing, last first, and how many there are
newtype Pay a = Pay ((Int, [S.Statement]) -> (a, (Int, [S.Statement])))

instance Functor Pay where
    fmap f (Pay g) = Pay (\s -> let (a, s') = g s in (f a, s'))

instance Applicative Pay where
    pure a = Pay (\s -> (a, s))
    Pay f <*> Pay g = Pay (\s -> let (h, s1) = f s; (a, s2) = g s1 in (h a, s2))

instance Monad Pay where
    Pay g >>= f = Pay (\s -> let (a, s1) = g s; Pay h = f a in h s1)

payload :: S.Statement -> Pay String
payload stmt = Pay (\(n, stmts) -> (show n, (n + 1, stmt : stmts)))

writeLowered :: Lowered -> Result String String
writeLowered lowered = case unwritable (lowProgram lowered) of
    problem : _ -> Error ("MirData: " ++ problem)
    [] -> mapResult (\payloadLines -> unlines (mirLines ++ ("data " ++ show (length payloadLines)) : payloadLines)) (writeMirPayloadLines (reverse payloads))
  where
    Pay run = loweredLines lowered
    (mirLines, (_, payloads)) = run (0, [])

loweredLines :: Lowered -> Pay [String]
loweredLines lowered = do
    invariants <- mapM invariantLine (Map.toList (progInvariants program))
    functions <- mapM (functionLines3 shared "function") (Map.elems (progFunctions program))
    mainLines <- functionLines3 shared "main" (progMain program)
    assumes <- mapM (payload . S.ValidationStatement . S.Assume) (lowAssumes lowered)
    pure
        ( "tersus-mir 3"
            : concatMap typeLines (Map.toList (progTypes program))
            ++ map genericLine (Map.toList (progGenerics program))
            ++ invariants
            ++ map boundedLine (Map.toList (progBounded program))
            ++ map instanceLine (Map.toList (progInstances program))
            ++ map (sharedLine . fst) (sortOn snd (Map.toList shared))
            ++ concat functions
            ++ mainLines
            ++ [ namesLine "copies" (lowCopies lowered)
               , namesLine "linear" (lowLinear lowered)
               , namesLine "drops" (lowDrops lowered)
               , namesLine "stubs" (lowStubs lowered)
               , namesLine "declared" (lowDeclared lowered)
               , namesLine "nested" (lowNested lowered)
               , unwords ("assumes" : show (length assumes) : assumes)
               ]
        )
  where
    program = lowProgram lowered
    shared = sharedEnvironments program
    namesLine w names = unwords (w : namesTokens (Set.toList names))
    genericLine (n, (sizes, fields)) = unwords (["generic", quote n] ++ namesTokens sizes ++ [show (length fields)] ++ concatMap fieldTokens fields)
    boundedLine (n, BoundedFn sizes copy lifted loops) = unwords (["bounded", quote n] ++ namesTokens sizes ++ namesTokens copy ++ namesTokens lifted ++ [show (length loops)] ++ concatMap packLoopTokens loops)
    packLoopTokens (PackLoop h b x bs ls i e et lo hi taken) =
        [blockText h, blockText b, blockText x, show (length bs)] ++ map blockText bs ++ [show (length ls)] ++ map localText ls
            ++ [localText i, localText e, quote et, localText lo, localText hi, maybe "none" localText taken]
    instanceLine (n, (generic, args)) = unwords (["instance", quote n, quote generic, show (length args)] ++ concatMap argTokens args)
    invariantLine (n, invariant) = (\p -> unwords ["invariant", quote n, p]) <$> payload (validationsPayload invariant)

-- What the records cannot hold: fixed-width integers other than i8 i16 i32 u16 u32, and narrowings to them (the
-- validator's payloads are checked by the AST data writer)
unwritable :: Program -> [String]
unwritable program =
    ["a type the data has no word for: " ++ show t | t <- types, not (writable t)]
        ++ ["an operation the data has no word for: " ++ show op | op <- operations, op `notElem` map snd listOps]
  where
    functions = progMain program : Map.elems (progFunctions program)
    types =
        concat [map snd fields | StructDecl fields <- Map.elems (progTypes program)]
            ++ concat [map snd fields | EnumDecl variants <- Map.elems (progTypes program), (_, fields) <- variants]
            ++ concat [map snd fields | (_, fields) <- Map.elems (progGenerics program)]
            ++ [t | (_, args) <- Map.elems (progInstances program), ArgType t <- args]
            ++ concat [maybe [] (: []) (fnReturns f) ++ map localType (Map.elems (fnLocals f)) | f <- functions]
    operations = [op | f <- functions, BasicBlock stmts _ <- Map.elems (fnBlocks f), ListOp op _ <- concatMap rvalues stmts]
    rvalues s = case s of
        Assign _ rv -> [rv]
        Peek _ rv -> [rv]
        AssignRef _ _ rv -> [rv]
        _ -> []
    writable t = case t of
        TWord signed bits -> (signed, bits) `elem` [(True, 8), (True, 16), (True, 32), (False, 16), (False, 32)]
        TNamed _ args -> and [writable u | ArgType u <- args]
        TArrayOf u _ -> writable u
        TAddr u -> writable u
        TUninit u -> writable u
        TBlock u -> writable u
        TRef u -> writable u
        TMutRef u -> writable u
        TFn args ret -> all writable (ret : args)
        TForall _ _ u -> writable u
        _ -> True

namesTokens :: [Name] -> [String]
namesTokens names = show (length names) : map quote names

envTokens :: Env -> [String]
envTokens env = show (Map.size env) : concat [quote x : operandTokens o | (x, o) <- Map.toList env]

-- The functions an environment names, which are the program's functions at the top and repeat in nearly every
-- environment: each such part is written once, numbered in the order it is met
type Shared = Map.Map (Map.Map Variable Name) Int

sharedEnvironments :: Program -> Shared
sharedEnvironments program = foldl add Map.empty [common | env <- environments, let common = fst (sharedPart env), not (Map.null common)]
  where
    add table key = if Map.member key table then table else Map.insert key (Map.size table) table
    environments =
        concat
            [ specEnv (fnSpec f) : map loopEnv (Map.elems (specLoops (fnSpec f))) ++ [env | BasicBlock stmts _ <- Map.elems (fnBlocks f), Ghost env _ <- stmts]
            | f <- Map.elems (progFunctions program) ++ [progMain program]
            ]

sharedPart :: Env -> (Map.Map Variable Name, Env)
sharedPart env = (Map.mapMaybe function env, Map.filter ((== Nothing) . function) env)
  where
    function o = case o of
        Const (CFn n) -> Just n
        _ -> Nothing

sharedLine :: Map.Map Variable Name -> String
sharedLine common = unwords ("shared" : envTokens (Map.map (Const . CFn) common))

envReference :: Shared -> Env -> [String]
envReference shared env =
    let (common, own) = sharedPart env
     in maybe "none" show (Map.lookup common shared) : envTokens own

validationsPayload :: [S.ValidationStatement] -> S.Statement
validationsPayload = S.Block . map S.ValidationStatement

terminationTokens :: Maybe S.Termination -> Pay String
terminationTokens = maybe (pure "none") (\t -> payload (S.While alwaysTrue [] (Just t) []))

alwaysTrue :: S.Expression
alwaysTrue = S.Val (S.VBool True)

functionLines3 :: Shared -> String -> Function -> Pay [String]
functionLines3 shared kind fn = do
    requires <- payload (validationsPayload (specRequires spec))
    ensures <- payload (validationsPayload (specEnsures spec))
    termination <- terminationTokens (specTermination spec)
    loops <- mapM loopLine (Map.toList (specLoops spec))
    blocks <- mapM blockLines (Map.toList (fnBlocks fn))
    pure
        ( headerText kind fn
            : unwords (["spec", "requires", requires, "ensures", ensures, "termination", termination, "writes"] ++ namesTokens (specWrites spec) ++ ["mutparams"] ++ namesTokens (specMutParams spec) ++ ["from"] ++ namesTokens (specFrom spec))
            : unwords ("env" : envReference shared (specEnv spec))
            : localLines fn
            ++ loops
            ++ concat blocks
            ++ ["end"]
        )
  where
    spec = fnSpec fn
    loopLine (header, LoopSpec invariant term env body) = do
        p <- payload (validationsPayload invariant)
        t <- terminationTokens term
        pure (unwords (["loop", blockText header, "body", blockText body, "invariant", p, "termination", t, "env"] ++ envReference shared env))
    blockLines (b, BasicBlock stmts term) = do
        texts <- mapM (statementText3 shared) stmts
        pure (("block " ++ blockText b) : texts ++ [terminatorText term])

statementText3 :: Shared -> Statement -> Pay String
statementText3 shared s = case s of
    Ghost env g -> unwords . ("ghost" :) <$> ghostTokens (envReference shared env) g
    _ -> pure (statementText s)

ghostTokens :: [String] -> GhostStatement -> Pay [String]
ghostTokens env g = case g of
    GhostValidation vs -> carrying "validation" <$> payload (S.ValidationStatement vs)
    GhostAxiom n args ins outs -> carrying "axiom" <$> payload (S.AxiomDef n args ins outs)
    GhostProof n args ins outs body -> carrying "proof" <$> payload (S.ProofDef n args ins outs body)
    GhostFunction n var top -> pure ("function" : env ++ [quote n, quote var, if top then "true" else "false"])
    GhostPosition line column -> pure ("position" : env ++ [show line, show column])
    GhostDissolve l -> pure ("dissolve" : env ++ [localText l])
  where
    carrying kind p = kind : env ++ [p]

-- The payloads and the shared environments, by index
data Tables = Tables (Map.Map Int S.Statement) (Map.Map Int Env)

readLowered :: String -> Result Lowered String
readLowered = readLoweredBytes . map B.pack . lines

readLoweredBytes :: [B.ByteString] -> Result Lowered String
readLoweredBytes ls = case ls of
    header : rest | header == B.pack "tersus-mir 3" -> case break (B.isPrefixOf (B.pack "data ")) rest of
        (records, dataLine : payloadLines) ->
            payloadCount (B.unpack dataLine) `bindResult` \n ->
                if toInteger (length payloadLines) /= n
                    then Error "the payload block is not as long as its data line says"
                    else
                        readMirPayloadBytes payloadLines `bindResult` \payloads ->
                            flatResultMap strictTokenizeBytesAnyNumber records `bindResult` \tokens ->
                                loweredFrom (Map.fromList (zip [0 ..] payloads)) tokens
        (_, []) -> Error "a lowered unit without its payload block"
    _ -> Error "not a lowered unit: the first line should be tersus-mir 3"
  where
    payloadCount line = case words line of
        ["data", digits] | Just n <- decimal digits, n >= 0, show n == digits, line == "data " ++ digits -> Ok n
        _ -> Error "a malformed data line"

-- The records in the order they are written, each payload referred to once
loweredFrom :: Map.Map Int S.Statement -> [[Token]] -> Result Lowered String
loweredFrom payloads records0 =
    recordsWhile typeRecord records0 `bindResult` \(types, r1) ->
        recordsWhile genericRecord r1 `bindResult` \(generics, r2) ->
            recordsWhile invariantRecord r2 `bindResult` \(invariants, r2') ->
                recordsWhile boundedRecord r2' `bindResult` \(bounded, r2'') ->
                recordsWhile instanceRecord r2'' `bindResult` \(instances, r3) ->
                recordsWhile sharedRecord r3 `bindResult` \(shared, r3') ->
                let tables = Tables payloads (Map.fromList (zip [0 ..] shared)) in
                functionsFrom tables r3' `bindResult` \(fns, fnUses, r4) ->
                    mainFrom tables r4 `bindResult` \(mainFn, mainUses, r5) ->
                        trailer r5 `bindResult` \(copies, linear, drops, stubs, declared, nested, (assumes, assumeUses)) ->
                            unique "type" (map fst types) `bindResult` \_ ->
                                unique "generic" (map fst generics) `bindResult` \_ ->
                                    unique "invariant" (map (fst . fst) invariants) `bindResult` \_ ->
                                    unique "bounded" (map fst bounded) `bindResult` \_ ->
                                    unique "instance" (map fst instances) `bindResult` \_ ->
                                        unique "function" (map fnName fns) `bindResult` \_ ->
                                            payloadUses (map snd invariants ++ fnUses ++ mainUses ++ assumeUses) `bindResult` \_ ->
                                                Ok
                                                    Lowered
                                                        { lowProgram = Program (Map.fromList types) (Map.fromList [(fnName f, f) | f <- fns]) mainFn (Map.fromList generics) (Map.fromList (map fst invariants)) (Map.fromList bounded) (Map.fromList instances)
                                                        , lowCopies = copies
                                                        , lowLinear = linear
                                                        , lowDrops = drops
                                                        , lowStubs = stubs
                                                        , lowDeclared = declared
                                                        , lowNested = nested
                                                        , lowAssumes = assumes
                                                        }
  where
    typeRecord record = case record of
        Word "struct" : ts -> Just (parseLine structP ts)
        Word "enum" : ts -> Just (parseLine enumP ts)
        _ -> Nothing
    genericRecord record = case record of
        Word "generic" : ts -> Just (parseLine ((,) <$> name <*> ((,) <$> namesP <*> fieldsP)) ts)
        _ -> Nothing
    invariantRecord record = case record of
        Word "invariant" : ts -> Just (parseLine ((\n (vs, i) -> ((n, vs), i)) <$> name <*> payloadP (Tables payloads Map.empty) "a list of validation statements" validationsOf) ts)
        _ -> Nothing
    boundedRecord record = case record of
        Word "bounded" : ts -> Just (parseLine ((\n sizes copy lifted loops -> (n, BoundedFn sizes copy lifted loops)) <$> name <*> namesP <*> namesP <*> namesP <*> (itemCount >>= \k -> replicateM k packLoopP)) ts)
        _ -> Nothing
    instanceRecord record = case record of
        Word "instance" : ts -> Just (parseLine ((\n generic args -> (n, (generic, args))) <$> name <*> name <*> (itemCount >>= \k -> replicateM k argP)) ts)
        _ -> Nothing
    sharedRecord record = case record of
        Word "shared" : ts -> Just (parseLine entriesP ts)
        _ -> Nothing
    functionsFrom tables records = case records of
        (Word "function" : header) : rest -> function3From tables header rest `bindResult` \(f, uses, rest') -> mapResult (\(fs, us, r) -> (f : fs, uses ++ us, r)) (functionsFrom tables rest')
        _ -> Ok ([], [], records)
    mainFrom tables records = case records of
        (Word "main" : header) : rest -> function3From tables header rest
        _ -> Error "the unit has no main after its functions"
    trailer records = case records of
        [c, l, d, s, n, i, a] ->
            namesRecord "copies" c `bindResult` \copies ->
                namesRecord "linear" l `bindResult` \linear ->
                    namesRecord "drops" d `bindResult` \drops ->
                        namesRecord "stubs" s `bindResult` \stubs ->
                            namesRecord "declared" n `bindResult` \declared ->
                                namesRecord "nested" i `bindResult` \nested ->
                                    assumesRecord a `bindResult` \assumes -> Ok (copies, linear, drops, stubs, declared, nested, assumes)
        _ -> Error "the unit does not end with its copies, linear, drops, stubs, declared, nested and assumes records"
    namesRecord w record = case record of
        Word w' : ts | w' == w -> parseLine namesP ts `bindResult` \names ->
            if length names == Set.size (Set.fromList names) then Ok (Set.fromList names) else Error ("a name twice in " ++ w)
        _ -> Error ("expected the " ++ w ++ " record")
    assumesRecord record = case record of
        Word "assumes" : ts -> mapResult unzip (parseLine (itemCount >>= \n -> replicateM n (payloadP (Tables payloads Map.empty) "an assume" assumeOf)) ts)
        _ -> Error "expected the assumes record"
    payloadUses uses
        | length uses /= Set.size (Set.fromList uses) = Error "a payload is referred to twice"
        | sort uses /= [0 .. Map.size payloads - 1] = Error "a payload is not referred to"
        | otherwise = Ok ()
    assumeOf stmt = case stmt of
        S.ValidationStatement (S.Assume p) -> Just p
        _ -> Nothing

recordsWhile :: ([Token] -> Maybe (Result a String)) -> [[Token]] -> Result ([a], [[Token]]) String
recordsWhile select records = case records of
    record : rest | Just parsed <- select record -> parsed `bindResult` \a -> mapResult (\(as, r) -> (a : as, r)) (recordsWhile select rest)
    _ -> Ok ([], records)

-- A function of version 3: its header (given), its spec and env, its locals, its loops, its blocks and the line that ends it
function3From :: Tables -> [Token] -> [[Token]] -> Result (Function, [Int], [[Token]]) String
function3From tables header records =
    parseLine headerP header `bindResult` \fn -> case records of
        (Word "spec" : specTokens) : (Word "env" : envTokens') : rest ->
            parseLine (specP tables) specTokens `bindResult` \(spec, specUses) ->
                parseLine (envP tables) envTokens' `bindResult` \env ->
                    localsFrom rest `bindResult` \(decls, rest1) ->
                        recordsWhile loopRecord rest1 `bindResult` \(loops, rest2) ->
                            blocks3From tables rest2 `bindResult` \(blocks, blockUses, rest3) ->
                                unique "local" (map fst decls) `bindResult` \_ ->
                                    unique "loop" (map (fst . fst) loops) `bindResult` \_ ->
                                        unique "block" (map fst blocks) `bindResult` \_ ->
                                            Ok
                                                ( fn{fnLocals = Map.fromList decls, fnBlocks = Map.fromList blocks, fnSpec = spec{specEnv = env, specLoops = Map.fromList (map fst loops)}}
                                                , specUses ++ concatMap snd loops ++ blockUses
                                                , rest3
                                                )
        _ -> Error ("the function " ++ fnName fn ++ " is not followed by its spec and env records")
  where
    loopRecord record = case record of
        Word "loop" : ts -> Just (parseLine (loopP tables) ts)
        _ -> Nothing

specP :: Tables -> P (FunctionSpec, [Int])
specP tables = do
    expect "requires"
    (requires, r) <- payloadP tables "a list of validation statements" validationsOf
    expect "ensures"
    (ensures, e) <- payloadP tables "a list of validation statements" validationsOf
    expect "termination"
    (termination, t) <- terminationP tables
    expect "writes"
    writes <- namesP
    expect "mutparams"
    mutParams <- namesP
    expect "from"
    froms <- namesP
    pure (FunctionSpec requires ensures termination Map.empty Map.empty writes mutParams froms, r : e : t)

loopP :: Tables -> P ((BlockId, LoopSpec), [Int])
loopP tables = do
    header <- block
    expect "body"
    body <- block
    expect "invariant"
    (invariant, i) <- payloadP tables "a list of validation statements" validationsOf
    expect "termination"
    (termination, t) <- terminationP tables
    expect "env"
    env <- envP tables
    pure ((header, LoopSpec invariant termination env body), i : t)

blocks3From :: Tables -> [[Token]] -> Result ([(BlockId, BasicBlock)], [Int], [[Token]]) String
blocks3From tables records = case records of
    [Word "end"] : rest -> Ok ([], [], rest)
    (Word "block" : ts) : rest ->
        parseLine block ts `bindResult` \b ->
            body3From rest [] [] `bindResult` \(body, uses, rest') -> mapResult (\(bs, us, r) -> ((b, body) : bs, uses ++ us, r)) (blocks3From tables rest')
    _ -> Error "a function that is not ended by end, or a line that is not a block"
  where
    body3From [] _ _ = Error "a block without a terminator"
    body3From (record : rest) stmts uses =
        line3 record `bindResult` \(l, u) -> case l of
            LStatement s -> body3From rest (s : stmts) (uses ++ u)
            LTerminator term -> Ok (BasicBlock (reverse stmts) term, uses ++ u, rest)
    line3 record = case record of
        Word "ghost" : ts -> mapResult (\(g, u) -> (LStatement g, u)) (parseLine (ghostP tables) ts)
        Word "dissolve" : _ -> Error "a dissolve is a ghost statement in version 3"
        _ -> mapResult (\l -> (l, [])) (parseLine lineP record)

ghostP :: Tables -> P (Statement, [Int])
ghostP tables = word >>= \kind -> envP tables >>= \env -> case kind of
    "validation" -> carrying env GhostValidation <$> payloadP tables "a validation statement" (\s -> case s of S.ValidationStatement v -> Just v; _ -> Nothing)
    "axiom" -> carrying env id <$> payloadP tables "an axiom" (\s -> case s of S.AxiomDef n args ins outs -> Just (GhostAxiom n args ins outs); _ -> Nothing)
    "proof" -> carrying env id <$> payloadP tables "a proof" (\s -> case s of S.ProofDef n args ins outs body -> Just (GhostProof n args ins outs body); _ -> Nothing)
    "function" -> (\n var top -> (Ghost env (GhostFunction n var top), [])) <$> name <*> name <*> boolP
    "position" -> (\line column -> (Ghost env (GhostPosition line column), [])) <$> int <*> int
    "dissolve" -> (\l -> (Ghost env (GhostDissolve l), [])) <$> local
    _ -> failP ("not a ghost statement: " ++ kind)
  where
    carrying env make (a, i) = (Ghost env (make a), [i])
    boolP = word >>= \w -> case w of
        "true" -> pure True
        "false" -> pure False
        _ -> failP ("not a Bool: " ++ w)

-- An environment: a shared one or none, and the names it gives besides or instead of the shared one's
envP :: Tables -> P Env
envP (Tables _ shared) = word >>= \w -> base w >>= \common -> (`Map.union` common) <$> entriesP
  where
    base w
        | w == "none" = pure Map.empty
        | Just i <- decimal w, i >= 0, i < toInteger (Map.size shared), Just env <- Map.lookup (fromInteger i) shared = pure env
        | otherwise = failP ("no shared environment " ++ w)

entriesP :: P Env
entriesP = itemCount >>= \n -> replicateM n ((,) <$> name <*> operandP) >>= \pairs ->
    if length pairs == Map.size (Map.fromList pairs) then pure (Map.fromList pairs) else failP "a name twice in an environment"

namesP :: P [Name]
namesP = itemCount >>= \n -> replicateM n name

packLoopP :: P PackLoop
packLoopP =
    PackLoop <$> block <*> block <*> block <*> (itemCount >>= \n -> replicateM n block) <*> (itemCount >>= \n -> replicateM n local)
        <*> local <*> local <*> name <*> local <*> local <*> takenP
  where
    takenP = P (\ts -> case ts of
        Word "none" : rest -> Ok (Nothing, rest)
        _ -> runP (Just <$> local) ts)

payloadP :: Tables -> String -> (S.Statement -> Maybe a) -> P (a, Int)
payloadP (Tables payloads _) kind project = int >>= \i -> case Map.lookup i payloads of
    Nothing -> failP ("no payload " ++ show i)
    Just stmt -> maybe (failP ("payload " ++ show i ++ " is not " ++ kind)) (\a -> pure (a, i)) (project stmt)

terminationP :: Tables -> P (Maybe S.Termination, [Int])
terminationP tables = P (\ts -> case ts of
    Word "none" : rest -> Ok ((Nothing, []), rest)
    _ -> runP ((\(t, i) -> (Just t, [i])) <$> payloadP tables "a termination" termination) ts)
  where
    termination s = case s of
        S.While (S.Val (S.VBool True)) [] (Just t) [] -> Just t
        _ -> Nothing

validationsOf :: S.Statement -> Maybe [S.ValidationStatement]
validationsOf s = case s of
    S.Block stmts -> mapM (\x -> case x of S.ValidationStatement v -> Just v; _ -> Nothing) stmts
    _ -> Nothing
