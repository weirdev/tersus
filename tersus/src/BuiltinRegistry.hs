module BuiltinRegistry
    ( BuiltinKind (..)
    , allBuiltinKinds
    , builtinKind
    , NameSpace (..)
    , SigScheme (..)
    , ContractSpec (..)
    , BuiltinEntry (..)
    , builtinRegistry
    , entryForKind
    , entryFor
    , builtinSymbol
    , stdBindings
    , builtinDecls
    , pointerBuiltinByName
    , ghostBuiltinByName
    , proofBuiltinByName
    , methodBuiltinByName
    , methodNameFor
    , signatureScheme
    , contractSpec
    ) where

import Data.List (find)
import Data.Maybe (mapMaybe)

import Types
import Syntax

-- The one registry of builtins. Every BuiltinFunct constructor has exactly one entry here, carrying its
-- surface names, its signature scheme (TParam "T"/"U" are scheme variables the checker instantiates
-- afresh at each use) and its contract. A contract is Tersus source text parsed with the ordinary
-- parser (ParsedContract): the name of the `builtin fn` declaration of lib/stdlib.tersus whose
-- parameter names and input/output validation statements StdLibDefs takes as the builtin's; the
-- types in that text are placeholders, the scheme below is what the checker uses. The exceptions are
-- the clearly delimited primitive contracts at the bottom of this file (PrimitiveContract): the
-- operations on addresses, permissions and Uninit, Cast, and the word conversions, whose ranges
-- depend on the constructor's arguments. Their proof terms speak of a permission through the ghost
-- accessors (`base`, `cap`, ...) and through `get(filled(b), i)` / `get(at(b), i)`, and a parsed affirm
-- names those as ordinary terms that only the checker resolves (it even chooses BlockFilled against
-- UninitFilled from the argument's type), while `whole(b)`, `offset(p, i)` and `cast(p)` terms and the
-- `value is Variant` proof of a cast (whose variant is the constructor's argument, so no declaration
-- is in scope when the text would be parsed) likewise have no parsed form that is the term the
-- validator works with. Those contracts therefore stay as Haskell terms, inside this same registry.
-- Adding a builtin is one entry here (and, for a ParsedContract, its `builtin fn` declaration in
-- lib/stdlib.tersus) plus its runtime semantics (StdLib.evalBuiltinFunct, the lowering in MirLower
-- and the MIR operations), which key off the same constructor.

data BuiltinKind
    = KSize | KFirst | KLast | KGet | KPush | KPop | KSet
    | KPlus | KMinus | KTimes | KDiv | KMod
    | KNewArray | KArrayFrom | KArrayFromList | KNewBoxedArray | KNewEmptyArray
    | KWriteByte | KWriteError | KReadByte | KArgCount | KArgByte
    | KPathByte | KFileLoad | KFileByte | KStoreByte | KFileStore
    | KToByte | KFromByte | KBytesFrom | KUnsize | KNewBox | KUnBox | KCloneOf
    | KBorrowOf | KBorrowMutOf | KDerefOf | KOldOf
    | KAddrNull | KAddrOffset | KAddrCast | KAddrToInt | KAddrFromInt
    | KAddrAlloc | KAddrGet | KAddrWrite | KAddrTake | KAddrDropValue | KAddrDropRange | KAddrResize | KAddrFree
    | KAllocPair | KTakePair | KResizePair | KSplitPair
    | KBlockNew | KBlockTaken | KBlockResized | KBlockSplitLo | KBlockSplitHi | KBlockJoin | KBlockAssume | KBlockCast
    | KBlockBase | KBlockCap | KBlockFilled | KBlockContents | KBlockOrigin | KBlockStart | KBlockExtent | KBlockCount
    | KUninitEmpty | KUninitNew | KUninitGet | KUninitTake | KUninitDiscard | KUninitFilled | KUninitAt
    | KToWord | KReplace | KRel | KAnd | KOr | KNot | KWithin
    | KCtor | KField | KIs | KProject | KCast
    deriving (Eq, Ord, Show, Enum, Bounded)

allBuiltinKinds :: [BuiltinKind]
allBuiltinKinds = [minBound .. maxBound]

builtinKind :: BuiltinFunct -> BuiltinKind
builtinKind b = case b of
    Size -> KSize
    First -> KFirst
    Last -> KLast
    Get -> KGet
    Push -> KPush
    Pop -> KPop
    Set -> KSet
    Plus -> KPlus
    Minus -> KMinus
    Times -> KTimes
    Div -> KDiv
    Mod -> KMod
    NewArray -> KNewArray
    ArrayFrom -> KArrayFrom
    ArrayFromList -> KArrayFromList
    NewBoxedArray -> KNewBoxedArray
    NewEmptyArray -> KNewEmptyArray
    WriteByte -> KWriteByte
    WriteError -> KWriteError
    ReadByte -> KReadByte
    ArgCount -> KArgCount
    ArgByte -> KArgByte
    PathByte -> KPathByte
    FileLoad -> KFileLoad
    FileByte -> KFileByte
    StoreByte -> KStoreByte
    FileStore -> KFileStore
    ToByte -> KToByte
    FromByte -> KFromByte
    BytesFrom -> KBytesFrom
    Unsize -> KUnsize
    NewBox -> KNewBox
    UnBox -> KUnBox
    CloneOf -> KCloneOf
    BorrowOf -> KBorrowOf
    BorrowMutOf -> KBorrowMutOf
    DerefOf -> KDerefOf
    OldOf -> KOldOf
    AddrNull -> KAddrNull
    AddrOffset -> KAddrOffset
    AddrCast -> KAddrCast
    AddrToInt -> KAddrToInt
    AddrFromInt -> KAddrFromInt
    AddrAlloc -> KAddrAlloc
    AddrGet -> KAddrGet
    AddrWrite -> KAddrWrite
    AddrTake -> KAddrTake
    AddrDropValue -> KAddrDropValue
    AddrDropRange -> KAddrDropRange
    AddrResize -> KAddrResize
    AddrFree -> KAddrFree
    AllocPair -> KAllocPair
    TakePair -> KTakePair
    ResizePair -> KResizePair
    SplitPair -> KSplitPair
    BlockNew -> KBlockNew
    BlockTaken -> KBlockTaken
    BlockResized -> KBlockResized
    BlockSplitLo -> KBlockSplitLo
    BlockSplitHi -> KBlockSplitHi
    BlockJoin -> KBlockJoin
    BlockAssume -> KBlockAssume
    BlockCast -> KBlockCast
    BlockBase -> KBlockBase
    BlockCap -> KBlockCap
    BlockFilled -> KBlockFilled
    BlockContents -> KBlockContents
    BlockOrigin -> KBlockOrigin
    BlockStart -> KBlockStart
    BlockExtent -> KBlockExtent
    BlockCount -> KBlockCount
    UninitEmpty -> KUninitEmpty
    UninitNew -> KUninitNew
    UninitGet -> KUninitGet
    UninitTake -> KUninitTake
    UninitDiscard -> KUninitDiscard
    UninitFilled -> KUninitFilled
    UninitAt -> KUninitAt
    ToWord _ _ -> KToWord
    Replace -> KReplace
    Rel _ -> KRel
    And -> KAnd
    Or -> KOr
    Not -> KNot
    Within -> KWithin
    Ctor _ _ _ -> KCtor
    Field _ _ -> KField
    Is _ -> KIs
    Project _ _ -> KProject
    Cast _ -> KCast

-- Where a surface name is used: a name of the standard context, a qualified name the checker
-- resolves, a name of what a proof knows of a permission, a name a proof calls, a method name, or a
-- syntactic form the checker takes apart itself (Box::new and its kin).
data NameSpace = StdName | PointerName | GhostName | ProofName | MethodName | SyntaxName
    deriving (Eq, Ord, Show)

-- SigDynamic: the signature is made from the declarations of the program (a constructor, a field, a
-- variant), so the checker computes it; SigValueError: the builtin cannot be used as a value, and
-- the message says how it is written.
data SigScheme
    = SigFn [Type] Type
    | SigValueError String
    | SigDynamic
    deriving (Eq, Show)

data ContractSpec
    = ParsedContract String
    | PrimitiveContract [ValidationStatement] [VariableProof]
    | NoContract
    deriving (Eq, Show)

data BuiltinEntry = BuiltinEntry
    { entryKind :: BuiltinKind
    , entryInstances :: [BuiltinFunct]
    , entrySurface :: [(NameSpace, Name, BuiltinFunct)]
    , entryParams :: BuiltinFunct -> [Variable]
    , entrySignature :: BuiltinFunct -> SigScheme
    , entryContract :: BuiltinFunct -> ContractSpec
    , entryReadsWorld :: Bool
    , entryGhost :: Bool
    }

entryForKind :: BuiltinKind -> Maybe BuiltinEntry
entryForKind kind = find (\entry -> entryKind entry == kind) builtinRegistry

entryFor :: BuiltinFunct -> BuiltinEntry
entryFor b = case entryForKind (builtinKind b) of
    Just entry -> entry
    Nothing -> error ("BuiltinRegistry: no entry for " ++ show b)

signatureScheme :: BuiltinFunct -> SigScheme
signatureScheme b = entrySignature (entryFor b) b

contractSpec :: BuiltinFunct -> ContractSpec
contractSpec b = entryContract (entryFor b) b

-- The builtin as a bare symbol, with no contract: what the parser makes its terms of, since the
-- parser cannot import the parsed contracts (StdLib, which parses them, imports the parser's
-- results through this module's tables). A builtin value is identified by its constructor (see the
-- Eq and Ord instances of Value), and the validator always takes the contract of StdLib.builtinFunct.
builtinSymbol :: BuiltinFunct -> Value
builtinSymbol b = VFunct (entryParams (entryFor b) b) [] [] (BuiltinFunct b) []

stdBindings :: [(Name, BuiltinFunct)]
stdBindings = [(name, b) | entry <- builtinRegistry, (StdName, name, b) <- entrySurface entry]

-- The builtins lib/stdlib.tersus declares, by the name it declares each under: StdLibDefs parses
-- that file once and takes the contract of each from its declaration there
builtinDecls :: [(String, BuiltinFunct)]
builtinDecls = [(name, b) | entry <- builtinRegistry, b <- entryInstances entry, ParsedContract name <- [contractSpec b]]

pointerBuiltinByName :: Name -> Maybe BuiltinFunct
pointerBuiltinByName name = lookup name [(n, b) | entry <- builtinRegistry, (PointerName, n, b) <- entrySurface entry]

ghostBuiltinByName :: Name -> Maybe BuiltinFunct
ghostBuiltinByName name = lookup name [(n, b) | entry <- builtinRegistry, (GhostName, n, b) <- entrySurface entry]

proofBuiltinByName :: Name -> Maybe BuiltinFunct
proofBuiltinByName name = lookup name [(n, b) | entry <- builtinRegistry, (ProofName, n, b) <- entrySurface entry]

methodBuiltinByName :: Name -> Maybe BuiltinFunct
methodBuiltinByName name = lookup name [(n, b) | entry <- builtinRegistry, (MethodName, n, b) <- entrySurface entry]

methodNameFor :: BuiltinFunct -> Maybe Name
methodNameFor b = case [(n) | (MethodName, n, b') <- entrySurface (entryFor b), b' == b] of
    name : _ -> Just name
    [] -> Nothing

-- The scheme variables and the shapes most signatures are made of
tp, tu :: Type
tp = TParam "T"
tu = TParam "U"

sig :: [Type] -> Type -> BuiltinFunct -> SigScheme
sig params ret _ = SigFn params ret

noSig :: String -> BuiltinFunct -> SigScheme
noSig message _ = SigValueError message

dynamicSig :: BuiltinFunct -> SigScheme
dynamicSig _ = SigDynamic

parsed :: String -> BuiltinFunct -> ContractSpec
parsed text _ = ParsedContract text

none :: BuiltinFunct -> ContractSpec
none _ = NoContract

primitive :: ([ValidationStatement], [VariableProof]) -> BuiltinFunct -> ContractSpec
primitive (ins, outs) _ = PrimitiveContract ins outs

params :: [Variable] -> BuiltinFunct -> [Variable]
params names _ = names

entry
    :: BuiltinKind
    -> [BuiltinFunct]
    -> [(NameSpace, Name, BuiltinFunct)]
    -> (BuiltinFunct -> [Variable])
    -> (BuiltinFunct -> SigScheme)
    -> (BuiltinFunct -> ContractSpec)
    -> BuiltinEntry
entry kind instances surface paramNames signature contract =
    BuiltinEntry kind instances surface paramNames signature contract False False

readsW :: BuiltinEntry -> BuiltinEntry
readsW e = e{entryReadsWorld = True}

ghostly :: BuiltinEntry -> BuiltinEntry
ghostly e = e{entryGhost = True}

builtinRegistry :: [BuiltinEntry]
builtinRegistry =
    [ entry KSize [Size] [(StdName, "size", Size), (ProofName, "size", Size), (MethodName, "size", Size)] (params ["list"]) (sig [TRef (TList tp)] TInt) (parsed "size")
    , entry KFirst [First] [(StdName, "first", First), (ProofName, "first", First), (MethodName, "first", First)] (params ["list"]) (sig [TRef (TList tp)] tp) (parsed "first")
    , entry KLast [Last] [(StdName, "last", Last), (ProofName, "last", Last), (MethodName, "last", Last)] (params ["list"]) (sig [TRef (TList tp)] tp) (parsed "last")
    , entry KGet [Get] [(StdName, "get", Get), (ProofName, "get", Get), (MethodName, "get", Get)] (params ["list", "index"]) (sig [TRef (TList tp), TInt] tp) (parsed "get")
    , entry KPush [Push] [(StdName, "push", Push), (ProofName, "push", Push), (MethodName, "push", Push)] (params ["list", "x"]) (sig [TList tp, tp] (TList tp)) (parsed "push")
    , entry KPop [Pop] [(StdName, "pop", Pop), (ProofName, "pop", Pop), (MethodName, "pop", Pop)] (params ["list"]) (sig [TList tp] (TList tp)) (parsed "pop")
    , entry KSet [Set] [(StdName, "set", Set), (ProofName, "set", Set), (MethodName, "set", Set)] (params ["list", "index", "x"]) (sig [TList tp, TInt, tp] (TList tp)) (parsed "set")
    , entry KPlus [Plus] [(StdName, "+", Plus)] (params ["a", "b"]) (sig [TInt, TInt] TInt) (parsed "plus")
    , entry KMinus [Minus] [(StdName, "-", Minus)] (params ["a", "b"]) (sig [TInt, TInt] TInt) (parsed "minus")
    , entry KTimes [Times] [(StdName, "*", Times)] (params ["a", "b"]) (sig [TInt, TInt] TInt) (parsed "times")
    , entry KDiv [Div] [(StdName, "/", Div)] (params ["a", "b"]) (sig [TInt, TInt] TInt) (parsed "div")
    , entry KMod [Mod] [(StdName, "%", Mod)] (params ["a", "b"]) (sig [TInt, TInt] TInt) (parsed "mod")
    , entry KNewArray [NewArray] [(StdName, "array", NewArray), (ProofName, "array", NewArray)] (params ["n", "x"]) (noSig "Type error: array needs a size that is a constant, so it is written array(3, x) and cannot be used as a value") (parsed "array")
    , entry KArrayFrom [ArrayFrom] [] (params ["list"]) (noSig "Type error: an array literal #[...] cannot be used as a value") (parsed "arrayFrom")
    , entry KArrayFromList [ArrayFromList] [(SyntaxName, "Array::fromList", ArrayFromList)] (params ["list"]) (noSig "Type error: Array::fromList is called, as in Array::fromList(xs), and cannot be used as a value") (parsed "arrayFromList")
    , entry KNewBoxedArray [NewBoxedArray] [(SyntaxName, "Array::boxed", NewBoxedArray)] (params ["n", "x"]) (noSig "Type error: Array::boxed is called, as in Array::boxed(n, x), and cannot be used as a value") (parsed "arrayBoxed")
    , entry KNewEmptyArray [NewEmptyArray] [(SyntaxName, "Array::empty", NewEmptyArray)] (params []) (noSig "Type error: Array::empty is called, as in Array::empty(), and cannot be used as a value") (parsed "arrayEmpty")
    , entry KWriteByte [WriteByte] [(StdName, "writeByte", WriteByte)] (params ["b"]) (sig [TByte] TByte) (parsed "writeByte")
    , entry KWriteError [WriteError] [(StdName, "writeError", WriteError)] (params ["b"]) (sig [TByte] TByte) (parsed "writeError")
    , readsW (entry KReadByte [ReadByte] [(StdName, "readByte", ReadByte)] (params []) (sig [] TInt) (parsed "readByte"))
    , readsW (entry KArgCount [ArgCount] [(StdName, "argCount", ArgCount)] (params []) (sig [] TInt) (parsed "argCount"))
    , readsW (entry KArgByte [ArgByte] [(StdName, "argByte", ArgByte)] (params ["i", "j"]) (sig [TInt, TInt] TInt) (parsed "argByte"))
    , readsW (entry KPathByte [PathByte] [(StdName, "pathByte", PathByte)] (params ["b"]) (sig [TByte] TInt) (parsed "pathByte"))
    , readsW (entry KFileLoad [FileLoad] [(StdName, "fileLoad", FileLoad)] (params []) (sig [] TInt) (parsed "fileLoad"))
    , readsW (entry KFileByte [FileByte] [(StdName, "fileByte", FileByte)] (params ["i"]) (sig [TInt] TInt) (parsed "fileByte"))
    , readsW (entry KStoreByte [StoreByte] [(StdName, "storeByte", StoreByte)] (params ["b"]) (sig [TByte] TInt) (parsed "storeByte"))
    , readsW (entry KFileStore [FileStore] [(StdName, "fileStore", FileStore)] (params []) (sig [] TInt) (parsed "fileStore"))
    , entry KToByte [ToByte] [(StdName, "toByte", ToByte)] (params ["x"]) (sig [TInt] TByte) (parsed "toByte")
    , entry KFromByte [FromByte] [(StdName, "toInt", FromByte)] (params ["b"]) (sig [TByte] TInt) (parsed "toInt")
    , entry KBytesFrom [BytesFrom] [] (params ["list"]) (sig [TRef (TList TInt)] (TList TByte)) (parsed "bytesFrom")
    , entry KUnsize [Unsize] [] (params ["box"]) (noSig "Type error: a Box of an array is given the size of its type by the checker, and unsize cannot be used as a value") (parsed "unsize")
    , entry KNewBox [NewBox] [(SyntaxName, "Box::new", NewBox)] (params ["value"]) (noSig "Type error: Box::new is called, as in Box::new(x), and cannot be used as a value") (parsed "boxNew")
    , entry KUnBox [UnBox] [(SyntaxName, "Box::unbox", UnBox)] (params ["box"]) (noSig "Type error: Box::unbox is called, as in Box::unbox(b), and cannot be used as a value") (parsed "boxUnbox")
    , entry KCloneOf [CloneOf] [(SyntaxName, "clone", CloneOf)] (params ["value"]) (noSig "Type error: clone is called, as in clone(x) or x.clone(), and cannot be used as a value") (parsed "cloneOf")
    , entry KBorrowOf [BorrowOf] [] (params ["place"]) (noSig "Type error: & is written on a place, as in &x, and cannot be used as a value") none
    , entry KBorrowMutOf [BorrowMutOf] [] (params ["place"]) (noSig "Type error: &mut is written on a place, as in &mut x, and cannot be used as a value") none
    , entry KDerefOf [DerefOf] [] (params ["reference"]) (noSig "Type error: * is written on a reference, as in *r, and cannot be used as a value") none
    , entry KOldOf [OldOf] [] (params ["place"]) (noSig "Type error: old(...) is only written in a postcondition, of the place an update parameter is to") none
    , entry KAddrNull [AddrNull] [(PointerName, "Addr::null", AddrNull), (GhostName, "Addr::null", AddrNull)] (params []) (sig [] (TAddr tp)) none
    , entry KAddrOffset [AddrOffset] [(PointerName, "Addr::offset", AddrOffset), (GhostName, "Addr::offset", AddrOffset)] (params ["p", "i"]) (sig [TAddr tp, TInt] (TAddr tp)) none
    , entry KAddrCast [AddrCast] [(PointerName, "Addr::cast", AddrCast), (GhostName, "Addr::cast", AddrCast)] (params ["p"]) (sig [TAddr tp] (TAddr tu)) none
    , entry KAddrToInt [AddrToInt] [(PointerName, "Addr::toInt", AddrToInt), (GhostName, "Addr::toInt", AddrToInt)] (params ["p"]) (sig [TAddr tp] TInt) none
    , entry KAddrFromInt [AddrFromInt] [(PointerName, "Addr::fromInt", AddrFromInt), (GhostName, "Addr::fromInt", AddrFromInt)] (params ["n"]) (sig [TInt] (TAddr tp)) (primitive (primAddrFromInt))
    , readsW (entry KAddrAlloc [AddrAlloc] [] (params ["n"]) (sig [TInt] (TAddr tp)) (primitive primAddrAlloc))
    , entry KAddrGet [AddrGet] [(PointerName, "Addr::get", AddrGet)] (params ["p", "i", "b"]) (sig [TAddr tp, TInt, TBlock tp] tp) (primitive primAddrGet)
    , entry KAddrWrite [AddrWrite] [(PointerName, "Addr::write", AddrWrite)] (params ["p", "i", "x", "b"]) (sig [TAddr tp, TInt, tp, TBlock tp] (TBlock tp)) (primitive primAddrWrite)
    , entry KAddrTake [AddrTake] [] (params ["p", "i", "b"]) (sig [TAddr tp, TInt, TBlock tp] tp) (primitive primAddrTake)
    , entry KAddrDropValue [AddrDropValue] [(PointerName, "Addr::dropValue", AddrDropValue)] (params ["p", "i", "b"]) (sig [TAddr tp, TInt, TBlock tp] (TBlock tp)) (primitive primAddrDropValue)
    , entry KAddrDropRange [AddrDropRange] [(PointerName, "Addr::dropRange", AddrDropRange)] (params ["p", "i", "n", "b"]) (sig [TAddr tp, TInt, TInt, TBlock tp] (TBlock tp)) (primitive primAddrDropRange)
    , readsW (entry KAddrResize [AddrResize] [] (params ["p", "n", "b"]) (sig [TAddr tp, TInt, TBlock tp] (TAddr tp)) (primitive primAddrResize))
    , entry KAddrFree [AddrFree] [(PointerName, "Addr::free", AddrFree)] (params ["p", "b"]) (sig [TAddr tp, TBlock tp] TInt) (primitive primAddrFree)
    , entry KAllocPair [AllocPair] [(PointerName, "Addr::alloc", AllocPair)] (params ["a1"]) (sig [TInt] (tupleType [TAddr tp, TBlock tp])) none
    , entry KTakePair [TakePair] [(PointerName, "Addr::take", TakePair)] (params ["a1", "a2", "a3"]) (sig [TAddr tp, TInt, TBlock tp] (tupleType [tp, TBlock tp])) none
    , entry KResizePair [ResizePair] [(PointerName, "Addr::resize", ResizePair)] (params ["a1", "a2", "a3"]) (sig [TAddr tp, TInt, TBlock tp] (tupleType [TAddr tp, TBlock tp])) none
    , entry KSplitPair [SplitPair] [(PointerName, "Block::split", SplitPair)] (params ["a1", "a2"]) (sig [TBlock tp, TInt] (tupleType [TBlock tp, TBlock tp])) none
    , ghostly (entry KBlockNew [BlockNew] [] (params ["p", "n"]) (sig [TAddr tp, TInt] (TBlock tp)) (primitive primBlockNew))
    , ghostly (entry KBlockTaken [BlockTaken] [] (params ["b", "i"]) (sig [TBlock tp, TInt] (TBlock tp)) (primitive primBlockTaken))
    , ghostly (entry KBlockResized [BlockResized] [] (params ["b", "q", "n"]) (sig [TBlock tp, TAddr tp, TInt] (TBlock tp)) (primitive primBlockResized))
    , ghostly (entry KBlockSplitLo [BlockSplitLo] [] (params ["b", "i"]) (sig [TBlock tp, TInt] (TBlock tp)) (primitive primBlockSplitLo))
    , ghostly (entry KBlockSplitHi [BlockSplitHi] [] (params ["b", "i"]) (sig [TBlock tp, TInt] (TBlock tp)) (primitive primBlockSplitHi))
    , ghostly (entry KBlockJoin [BlockJoin] [(PointerName, "Block::join", BlockJoin)] (params ["lo", "hi"]) (sig [TBlock tp, TBlock tp] (TBlock tp)) (primitive primBlockJoin))
    , readsW (ghostly (entry KBlockAssume [BlockAssume] [(PointerName, "Block::assume", BlockAssume)] (params ["p", "n"]) (sig [TAddr tp, TInt] (TBlock tp)) (primitive primBlockAssume)))
    , ghostly (entry KBlockCast [BlockCast] [(PointerName, "Block::cast", BlockCast)] (params ["b"]) (sig [TBlock tp] (TBlock tu)) (primitive primBlockCast))
    , ghostly (entry KBlockBase [BlockBase] [(GhostName, "base", BlockBase)] (params ["a1"]) (sig [TBlock tp] (TAddr tp)) none)
    , ghostly (entry KBlockCap [BlockCap] [(GhostName, "cap", BlockCap)] (params ["a1"]) (sig [TBlock tp] TInt) none)
    , ghostly (entry KBlockFilled [BlockFilled] [(GhostName, "filled", BlockFilled)] (params ["a1"]) (sig [TBlock tp] (TList TBool)) none)
    , ghostly (entry KBlockContents [BlockContents] [(GhostName, "at", BlockContents)] (params ["a1"]) (sig [TBlock tp] (TList tp)) none)
    , ghostly (entry KBlockOrigin [BlockOrigin] [(GhostName, "origin", BlockOrigin)] (params ["a1"]) (sig [TBlock tp] TInt) none)
    , ghostly (entry KBlockStart [BlockStart] [(GhostName, "start", BlockStart)] (params ["a1"]) (sig [TBlock tp] TInt) none)
    , ghostly (entry KBlockExtent [BlockExtent] [(GhostName, "extent", BlockExtent)] (params ["a1"]) (sig [TInt] TInt) none)
    , ghostly (entry KBlockCount [BlockCount] [(GhostName, "count", BlockCount)] (params ["a1"]) (sig [TBlock tp] TInt) none)
    , entry KUninitEmpty [UninitEmpty] [(PointerName, "Uninit::empty", UninitEmpty)] (params []) (sig [] (TUninit tp)) (primitive primUninitEmpty)
    , entry KUninitNew [UninitNew] [(PointerName, "Uninit::new", UninitNew)] (params ["x"]) (sig [tp] (TUninit tp)) (primitive primUninitNew)
    , entry KUninitGet [UninitGet] [(PointerName, "Uninit::get", UninitGet)] (params ["u"]) (sig [TUninit tp] tp) (primitive primUninitGet)
    , entry KUninitTake [UninitTake] [(PointerName, "Uninit::take", UninitTake)] (params ["u"]) (sig [TUninit tp] tp) (primitive primUninitTake)
    , entry KUninitDiscard [UninitDiscard] [(PointerName, "Uninit::discard", UninitDiscard)] (params ["u"]) (sig [TUninit tp] TInt) (primitive primUninitDiscard)
    , entry KUninitFilled [UninitFilled] [] (params ["u"]) (sig [TUninit tp] TBool) none
    , entry KUninitAt [UninitAt] [] (params ["u"]) (sig [TUninit tp] tp) none
    , entry KToWord [ToWord True 8, ToWord True 16, ToWord True 32, ToWord False 16, ToWord False 32]
        [(PointerName, "I8::from", ToWord True 8), (PointerName, "I16::from", ToWord True 16), (PointerName, "I32::from", ToWord True 32), (PointerName, "U16::from", ToWord False 16), (PointerName, "U32::from", ToWord False 32)]
        (params ["x"])
        (\b -> case b of ToWord signed bits -> SigFn [TInt] (TWord signed bits); _ -> SigFn [TInt] TInt)
        (\b -> case b of
            ToWord signed bits -> primToWord signed bits
            _ -> NoContract)
    , entry KReplace [Replace] [(PointerName, "replace", Replace)] (params ["list", "index", "x"]) (sig [TList tp, TInt, tp] (tupleType [TList tp, tp])) none
    , entry KRel [Rel Eq, Rel NotEq, Rel Lt, Rel Gt, Rel LtEq, Rel GtEq]
        [(StdName, "=", Rel Eq), (StdName, "!=", Rel NotEq), (StdName, "<", Rel Lt), (StdName, ">", Rel Gt), (StdName, "<=", Rel LtEq), (StdName, ">=", Rel GtEq)]
        (params ["a", "b"])
        (\b -> case b of Rel Eq -> SigFn [tp, tp] TBool; Rel NotEq -> SigFn [tp, tp] TBool; _ -> SigFn [TInt, TInt] TBool)
        none
    , entry KAnd [And] [] (params ["a", "b"]) (sig [TBool, TBool] TBool) none
    , entry KOr [Or] [] (params ["a", "b"]) (sig [TBool, TBool] TBool) none
    , entry KNot [Not] [] (params ["a"]) (sig [TBool] TBool) none
    , entry KWithin [Within] [] (params ["a", "b"]) (sig [tp, tp] TBool) none
    , entry KCtor [] [] (\b -> case b of Ctor _ _ fields -> fields; _ -> []) dynamicSig none
    , entry KField [] [] (params ["struct"]) dynamicSig none
    , entry KIs [] [] (params ["value"]) dynamicSig none
    , entry KProject [] [] (params ["value"]) dynamicSig none
    , entry KCast [] [] (params ["value"]) dynamicSig primCast
    ]

-- Primitive contracts (see the module header for why these are not parsed text)

primToWord :: Bool -> Integer -> ContractSpec
primToWord signed bits =
    let (low, high) = wordRange signed bits
     in PrimitiveContract
            [ Rewrite (CheckRel (relP GtEq (ATerm "x") (CTerm (VInt low))))
            , ProofAssert (relP GtEq (ATerm "x") (CTerm (VInt low)))
            , Rewrite (CheckRel (relP Lt (ATerm "x") (CTerm (VInt high))))
            , ProofAssert (relP Lt (ATerm "x") (CTerm (VInt high)))
            ]
            [relP Eq (ATerm "return") (ATerm "x")]

primCast :: BuiltinFunct -> ContractSpec
primCast (Cast variant) = PrimitiveContract [ProofAssert (FApp (CTerm (builtinSymbol (Is variant))) [ATerm "value"])] []
primCast _ = NoContract

sym :: BuiltinFunct -> Value
sym = builtinSymbol

relP :: Rel -> VariableProof -> VariableProof -> VariableProof
relP rel lhs rhs = FApp (CTerm (sym (Rel rel))) [lhs, rhs]

ptrApp :: BuiltinFunct -> [VariableProof] -> VariableProof
ptrApp b args = FApp (CTerm (sym b)) args

plusP, minusP :: VariableProof -> VariableProof -> VariableProof
plusP x y = FApp (CTerm (sym Plus)) [x, y]
minusP x y = FApp (CTerm (sym Minus)) [x, y]

blockBase, blockCap, blockOrigin, blockStart, blockCount :: VariableProof -> VariableProof
blockBase b = ptrApp BlockBase [b]
blockCap b = ptrApp BlockCap [b]
blockOrigin b = ptrApp BlockOrigin [b]
blockStart b = ptrApp BlockStart [b]
blockCount b = ptrApp BlockCount [b]

blockFilled, blockAt :: VariableProof -> VariableProof -> VariableProof
blockFilled b i = FApp (CTerm (sym Get)) [ptrApp BlockFilled [b], i]
blockAt b i = FApp (CTerm (sym Get)) [ptrApp BlockContents [b], i]

uninitFilled :: VariableProof -> VariableProof
uninitFilled u = ptrApp UninitFilled [u]

atLeastZero :: VariableProof -> ValidationStatement
atLeastZero x = ProofAssert (relP GtEq x (CTerm (VInt 0)))

indexIn :: Variable -> VariableProof -> VariableProof -> VariableProof -> VariableProof
indexIn j lo hi = Forall j [relP GtEq (BVar j) lo, relP Lt (BVar j) hi]

slotOf :: Variable -> [ValidationStatement]
slotOf b =
    [ ProofAssert (relP Eq (blockBase (ATerm b)) (ATerm "p"))
    , atLeastZero (ATerm "i")
    , ProofAssert (relP Lt (ATerm "i") (blockCap (ATerm b)))
    ]

isFilled, isEmpty :: Variable -> VariableProof -> ValidationStatement
isFilled b i = ProofAssert (relP Eq (blockFilled (ATerm b) i) (CTerm (VBool True)))
isEmpty b i = ProofAssert (relP Eq (blockFilled (ATerm b) i) (CTerm (VBool False)))

isWhole :: Variable -> [ValidationStatement]
isWhole b =
    [ ProofAssert (relP Eq (blockStart (ATerm b)) (CTerm (VInt 0)))
    , ProofAssert (relP Eq (blockCap (ATerm b)) (ptrApp BlockExtent [blockOrigin (ATerm b)]))
    ]

allEmpty :: Variable -> VariableProof
allEmpty b = indexIn "j" (CTerm (VInt 0)) (blockCap (ATerm b)) (relP Eq (blockFilled (ATerm b) (BVar "j")) (CTerm (VBool False)))

noneFilled :: Variable -> ValidationStatement
noneFilled b = ProofAssert (relP Eq (blockCount (ATerm b)) (CTerm (VInt 0)))

newBlockFacts :: VariableProof -> VariableProof -> [VariableProof]
newBlockFacts p n =
    [ relP Eq (blockBase (ATerm "return")) p
    , relP Eq (blockCap (ATerm "return")) n
    , relP GtEq (blockCap (ATerm "return")) (CTerm (VInt 0))
    , relP Eq (blockStart (ATerm "return")) (CTerm (VInt 0))
    , relP Eq (ptrApp BlockExtent [blockOrigin (ATerm "return")]) n
    ]

newBlock :: VariableProof -> VariableProof -> [VariableProof]
newBlock p n = newBlockFacts p n ++ [relP Eq (blockCount (ATerm "return")) (CTerm (VInt 0)), allEmpty "return"]

keeps :: Variable -> Variable -> [VariableProof]
keeps r b =
    [ relP Eq (blockBase (ATerm r)) (blockBase (ATerm b))
    , relP Eq (blockCap (ATerm r)) (blockCap (ATerm b))
    , relP Eq (blockOrigin (ATerm r)) (blockOrigin (ATerm b))
    , relP Eq (blockStart (ATerm r)) (blockStart (ATerm b))
    ]

sameExcept :: Variable -> Variable -> VariableProof -> [VariableProof]
sameExcept r b i =
    [ Forall "j" guards (relP Eq (blockFilled (ATerm r) (BVar "j")) (blockFilled (ATerm b) (BVar "j")))
    , Forall "j" guards (relP Eq (blockAt (ATerm r) (BVar "j")) (blockAt (ATerm b) (BVar "j")))
    ]
  where
    guards = [relP GtEq (BVar "j") (CTerm (VInt 0)), relP Lt (BVar "j") (blockCap (ATerm b)), relP NotEq (BVar "j") i]

emptied :: Variable -> Variable -> VariableProof -> [VariableProof]
emptied r b i =
    keeps r b
        ++ [relP Eq (blockFilled (ATerm r) i) (CTerm (VBool False)), relP Eq (blockCount (ATerm r)) (minusP (blockCount (ATerm b)) (CTerm (VInt 1)))]
        ++ sameExcept r b i

primAddrFromInt :: ([ValidationStatement], [VariableProof])
primAddrFromInt = ([], [relP Eq (ptrApp AddrToInt [ATerm "return"]) (ATerm "n")])

primAddrAlloc :: ([ValidationStatement], [VariableProof])
primAddrAlloc = ([atLeastZero (ATerm "n")], [])

primBlockNew :: ([ValidationStatement], [VariableProof])
primBlockNew = ([], newBlock (ATerm "p") (ATerm "n"))

primAddrGet :: ([ValidationStatement], [VariableProof])
primAddrGet = (slotOf "b" ++ [isFilled "b" (ATerm "i")], [relP Eq (ATerm "return") (blockAt (ATerm "b") (ATerm "i"))])

primAddrWrite :: ([ValidationStatement], [VariableProof])
primAddrWrite =
    ( slotOf "b" ++ [isEmpty "b" (ATerm "i")]
    , keeps "return" "b"
        ++ [ relP Eq (blockCount (ATerm "return")) (plusP (blockCount (ATerm "b")) (CTerm (VInt 1)))
           , relP Eq (blockFilled (ATerm "return") (ATerm "i")) (CTerm (VBool True))
           , relP Eq (blockAt (ATerm "return") (ATerm "i")) (ATerm "x")
           ]
        ++ sameExcept "return" "b" (ATerm "i")
    )

primAddrTake :: ([ValidationStatement], [VariableProof])
primAddrTake = (slotOf "b" ++ [isFilled "b" (ATerm "i")], [relP Eq (ATerm "return") (blockAt (ATerm "b") (ATerm "i"))])

primBlockTaken :: ([ValidationStatement], [VariableProof])
primBlockTaken = ([], emptied "return" "b" (ATerm "i"))

primAddrDropValue :: ([ValidationStatement], [VariableProof])
primAddrDropValue = (slotOf "b" ++ [isFilled "b" (ATerm "i")], emptied "return" "b" (ATerm "i"))

primAddrDropRange :: ([ValidationStatement], [VariableProof])
primAddrDropRange =
    ( [ ProofAssert (relP Eq (blockBase (ATerm "b")) (ATerm "p"))
      , atLeastZero (ATerm "i")
      , atLeastZero (ATerm "n")
      , ProofAssert (relP LtEq (plusP (ATerm "i") (ATerm "n")) (blockCap (ATerm "b")))
      , ProofAssert (indexIn "j" (ATerm "i") (plusP (ATerm "i") (ATerm "n")) (relP Eq (blockFilled (ATerm "b") (BVar "j")) (CTerm (VBool True))))
      ]
    , keeps "return" "b"
        ++ [ indexIn "j" (ATerm "i") (plusP (ATerm "i") (ATerm "n")) (relP Eq (blockFilled (ATerm "return") (BVar "j")) (CTerm (VBool False)))
           , indexIn "j" (CTerm (VInt 0)) (ATerm "i") (relP Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
           , indexIn "j" (plusP (ATerm "i") (ATerm "n")) (blockCap (ATerm "b")) (relP Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
           , relP Eq (ptrApp BlockContents [ATerm "return"]) (ptrApp BlockContents [ATerm "b"])
           , relP Eq (blockCount (ATerm "return")) (minusP (blockCount (ATerm "b")) (ATerm "n"))
           ]
    )

primAddrResize :: ([ValidationStatement], [VariableProof])
primAddrResize = ([ProofAssert (relP Eq (blockBase (ATerm "b")) (ATerm "p")), atLeastZero (ATerm "n")] ++ isWhole "b" ++ [ProofAssert (indexIn "j" (ATerm "n") (blockCap (ATerm "b")) (relP Eq (blockFilled (ATerm "b") (BVar "j")) (CTerm (VBool False))))], [])

primBlockResized :: ([ValidationStatement], [VariableProof])
primBlockResized =
    ( []
    , newBlockFacts (ATerm "q") (ATerm "n")
        ++ [ relP Eq (blockCount (ATerm "return")) (blockCount (ATerm "b"))
           , Forall "j" [relP GtEq (BVar "j") (CTerm (VInt 0)), relP Lt (BVar "j") (ATerm "n"), relP Lt (BVar "j") (blockCap (ATerm "b"))] (relP Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
           , Forall "j" [relP GtEq (BVar "j") (CTerm (VInt 0)), relP Lt (BVar "j") (ATerm "n"), relP Lt (BVar "j") (blockCap (ATerm "b"))] (relP Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "b") (BVar "j")))
           , Forall "j" [relP GtEq (BVar "j") (blockCap (ATerm "b")), relP Lt (BVar "j") (ATerm "n")] (relP Eq (blockFilled (ATerm "return") (BVar "j")) (CTerm (VBool False)))
           ]
    )

primAddrFree :: ([ValidationStatement], [VariableProof])
primAddrFree = ([ProofAssert (relP Eq (blockBase (ATerm "b")) (ATerm "p"))] ++ isWhole "b" ++ [noneFilled "b"], [relP Eq (ATerm "return") (CTerm (VInt 0))])

primBlockSplitLo :: ([ValidationStatement], [VariableProof])
primBlockSplitLo =
    ( [atLeastZero (ATerm "i"), ProofAssert (relP LtEq (ATerm "i") (blockCap (ATerm "b")))]
    , [ relP Eq (blockBase (ATerm "return")) (blockBase (ATerm "b"))
      , relP Eq (blockCap (ATerm "return")) (ATerm "i")
      , relP Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "b"))
      , relP Eq (blockStart (ATerm "return")) (blockStart (ATerm "b"))
      , relP GtEq (blockCount (ATerm "return")) (CTerm (VInt 0))
      , relP LtEq (blockCount (ATerm "return")) (blockCount (ATerm "b"))
      , indexIn "j" (CTerm (VInt 0)) (ATerm "i") (relP Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
      , indexIn "j" (CTerm (VInt 0)) (ATerm "i") (relP Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "b") (BVar "j")))
      ]
    )

primBlockSplitHi :: ([ValidationStatement], [VariableProof])
primBlockSplitHi =
    ( [atLeastZero (ATerm "i"), ProofAssert (relP LtEq (ATerm "i") (blockCap (ATerm "b")))]
    , [ relP Eq (blockBase (ATerm "return")) (ptrApp AddrOffset [blockBase (ATerm "b"), ATerm "i"])
      , relP Eq (blockCap (ATerm "return")) (minusP (blockCap (ATerm "b")) (ATerm "i"))
      , relP Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "b"))
      , relP Eq (blockStart (ATerm "return")) (plusP (blockStart (ATerm "b")) (ATerm "i"))
      , relP Eq (blockCount (ATerm "return")) (minusP (blockCount (ATerm "b")) (blockCount (ptrApp BlockSplitLo [ATerm "b", ATerm "i"])))
      , relP GtEq (blockCount (ATerm "return")) (CTerm (VInt 0))
      , indexIn "j" (CTerm (VInt 0)) (minusP (blockCap (ATerm "b")) (ATerm "i")) (relP Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (plusP (ATerm "i") (BVar "j"))))
      , indexIn "j" (CTerm (VInt 0)) (minusP (blockCap (ATerm "b")) (ATerm "i")) (relP Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "b") (plusP (ATerm "i") (BVar "j"))))
      ]
    )

primBlockJoin :: ([ValidationStatement], [VariableProof])
primBlockJoin =
    ( [ ProofAssert (relP Eq (blockOrigin (ATerm "lo")) (blockOrigin (ATerm "hi")))
      , ProofAssert (relP Eq (blockStart (ATerm "hi")) (plusP (blockStart (ATerm "lo")) (blockCap (ATerm "lo"))))
      ]
    , [ relP Eq (blockBase (ATerm "return")) (blockBase (ATerm "lo"))
      , relP Eq (blockCap (ATerm "return")) (plusP (blockCap (ATerm "lo")) (blockCap (ATerm "hi")))
      , relP Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "lo"))
      , relP Eq (blockStart (ATerm "return")) (blockStart (ATerm "lo"))
      , relP Eq (blockCount (ATerm "return")) (plusP (blockCount (ATerm "lo")) (blockCount (ATerm "hi")))
      , indexIn "j" (CTerm (VInt 0)) (blockCap (ATerm "lo")) (relP Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "lo") (BVar "j")))
      , indexIn "j" (CTerm (VInt 0)) (blockCap (ATerm "lo")) (relP Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "lo") (BVar "j")))
      , indexIn "j" (blockCap (ATerm "lo")) (plusP (blockCap (ATerm "lo")) (blockCap (ATerm "hi"))) (relP Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "hi") (minusP (BVar "j") (blockCap (ATerm "lo")))))
      , indexIn "j" (blockCap (ATerm "lo")) (plusP (blockCap (ATerm "lo")) (blockCap (ATerm "hi"))) (relP Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "hi") (minusP (BVar "j") (blockCap (ATerm "lo")))))
      ]
    )

primBlockAssume :: ([ValidationStatement], [VariableProof])
primBlockAssume = ([atLeastZero (ATerm "n")], newBlock (ATerm "p") (ATerm "n"))

primBlockCast :: ([ValidationStatement], [VariableProof])
primBlockCast =
    ( [noneFilled "b"]
    , [ relP Eq (blockBase (ATerm "return")) (ptrApp AddrCast [blockBase (ATerm "b")])
      , relP Eq (blockCap (ATerm "return")) (blockCap (ATerm "b"))
      , relP Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "b"))
      , relP Eq (blockStart (ATerm "return")) (blockStart (ATerm "b"))
      , relP Eq (blockCount (ATerm "return")) (CTerm (VInt 0))
      , allEmpty "return"
      ]
    )

primUninitEmpty :: ([ValidationStatement], [VariableProof])
primUninitEmpty = ([], [relP Eq (uninitFilled (ATerm "return")) (CTerm (VBool False))])

primUninitNew :: ([ValidationStatement], [VariableProof])
primUninitNew = ([], [relP Eq (uninitFilled (ATerm "return")) (CTerm (VBool True)), relP Eq (ptrApp UninitAt [ATerm "return"]) (ATerm "x")])

primUninitGet :: ([ValidationStatement], [VariableProof])
primUninitGet = ([ProofAssert (relP Eq (uninitFilled (ATerm "u")) (CTerm (VBool True)))], [relP Eq (ATerm "return") (ptrApp UninitAt [ATerm "u"])])

primUninitTake :: ([ValidationStatement], [VariableProof])
primUninitTake = ([ProofAssert (relP Eq (uninitFilled (ATerm "u")) (CTerm (VBool True)))], [relP Eq (ATerm "return") (ptrApp UninitAt [ATerm "u"])])

primUninitDiscard :: ([ValidationStatement], [VariableProof])
primUninitDiscard = ([ProofAssert (relP Eq (uninitFilled (ATerm "u")) (CTerm (VBool False)))], [relP Eq (ATerm "return") (CTerm (VInt 0))])
