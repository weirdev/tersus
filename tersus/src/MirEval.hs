{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module MirEval
    ( MirValue (MInt, MBool, MList, MData, MFn, MEmpty, MRef, MHeapRef, MFrameRef)
    , runProgram
    , runProgramOutput
    , runProgramWith
    , runProgramStreams
    , runProgramIn
    , RunEnv (..)
    , Outcome (..)
    , runProgramEnv
    , runNamedFunction
    , renderMirValue
    , toMirValue
    , fromMirValue
    ) where

import Data.Char (chr)
import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Sequence (Seq, ViewL (..), ViewR (..), (|>))
import qualified Data.Sequence as Seq
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir
import MirMono (monomorphize)
import Types (Name, Rel (..), Type (..), pattern TList, pattern TBox, Variable)
import Syntax (Value (..))
import Utils

-- Runs the MIR: a function is its locals and the block it is in. The statements of the block run, then the
-- terminator says where to go next. The operations that need a contract the validator proved (a divisor that is not 0,
-- an index in range) still check it and report an error, so that a mistake of the validator is a failure here instead
-- of a wrong answer, as it is in the evaluator of the AST.
data MirValue
    = MInt Integer
    | MBool Bool
    | MSequence (Seq MirValue)
    | MData Name [(Variable, MirValue)]
    | MFn Name
    | -- What an empty Uninit<T> holds: nothing, which no operation can read
      MEmpty
    | -- Host-supplied frame-local targets are qualified when their frame starts.
      MRef Local [EvalStep]
    | MHeapRef Integer [EvalStep]
    | MFrameRef Integer Local [EvalStep]
    deriving (Eq)

pattern MList :: [MirValue] -> MirValue
pattern MList values <- MSequence (toList -> values)
  where
    MList values = MSequence (Seq.fromList values)

{-# COMPLETE MInt, MBool, MList, MData, MFn, MEmpty, MRef, MHeapRef, MFrameRef #-}

instance Show MirValue where
    showsPrec p value = case value of
        MInt n -> constructor "MInt" [showsPrec 11 n]
        MBool b -> constructor "MBool" [showsPrec 11 b]
        MSequence values -> constructor "MList" [showsPrec 11 (toList values)]
        MData name fields -> constructor "MData" [showsPrec 11 name, showsPrec 11 fields]
        MFn name -> constructor "MFn" [showsPrec 11 name]
        MEmpty -> showString "MEmpty"
        MRef local steps -> constructor "MRef" [showsPrec 11 local, showsPrec 11 steps]
        MHeapRef address steps -> constructor "MHeapRef" [showsPrec 11 address, showsPrec 11 steps]
        MFrameRef frame local steps -> constructor "MFrameRef" [showsPrec 11 frame, showsPrec 11 local, showsPrec 11 steps]
      where
        constructor name args = showParen (p > 10) (showString name . foldr (.) id [showChar ' ' . arg | arg <- args])

-- A step from the root of a borrowed place to the place itself, with its index a value
data EvalStep = EvalField Variable | EvalIndex Integer
    deriving (Eq, Show)

-- The value of _0 when the program returns, and Nothing when it ends without
runProgram :: Program -> Result (Maybe MirValue) String
runProgram = mapResult snd . runProgramOutput

-- The bytes that the program wrote with writeByte (as characters from 0 to 255), and the value it returns, when there is no input
runProgramOutput :: Program -> Result (String, Maybe MirValue) String
runProgramOutput = runProgramWith ""

-- The same for a program given input, the bytes (as characters from 0 to 255) that readByte reads in turn. The input is read as the program
-- asks for it, so it can be a stream that is not at its end.
runProgramWith :: String -> Program -> Result (String, Maybe MirValue) String
runProgramWith input program = mapResult (\(out, _, value) -> (out, value)) (runProgramStreams input program)

-- The same, with the bytes written to the standard error too (as characters from 0 to 255)
runProgramStreams :: String -> Program -> Result (String, String, Maybe MirValue) String
runProgramStreams input = runProgramIn [] input

-- The same for a program that was given arguments: each is its bytes (as characters from 0 to 255), which argCount and argByte give
runProgramIn :: [String] -> String -> Program -> Result (String, String, Maybe MirValue) String
runProgramIn args input program =
    mapResult (\o -> (outStdout o, outStderr o, outValue o)) (runProgramEnv RunEnv{envArgs = args, envInput = input, envFile = const Nothing} program)

-- What a program is run in: its arguments, the bytes of the standard input, and the files it can read (a file by its path, as the bytes of the path, with
-- the bytes of its contents, or Nothing when there is no such file). A program that writes a file does not change what this gives: it reads its own
-- writes, and the files it wrote are in the outcome.
data RunEnv = RunEnv
    { envArgs :: [String]
    , envInput :: String
    , envFile :: FilePath -> Maybe String
    }

-- What a program did: the bytes it wrote to the standard output and to the standard error, the files it wrote (each path once, in the order of its first
-- write, with what the file holds at the end), and the value it returns
data Outcome = Outcome
    { outStdout :: String
    , outStderr :: String
    , outFiles :: [(FilePath, String)]
    , outValue :: Maybe MirValue
    }

runProgramEnv :: RunEnv -> Program -> Result Outcome String
runProgramEnv env source =
    let program = monomorphize source
     in mapResult
        (\(value, (out, err), s) -> Outcome out err [(spelling, Map.findWithDefault "" key (sFiles s)) | (key, spelling) <- sOrder s] value)
        (runE (fmap fst (runFunction program (progMain program) [] Map.empty)) env (startState (envInput env)))

-- What a program has written to the standard output and to the standard error
type Written = (String, String)

none :: Written
none = ("", "")

-- What changes while a program runs: the input that is left, the path being built and the file that was loaded last and the file being built
-- (the bytes of each), and the files written so far
data S = S
    { sInput :: String
    , sPath :: String
    , sLoaded :: String
    , sStore :: String
    , sFiles :: Map FilePath String -- by the path with its dots taken out (see samePath)
    , sOrder :: [(FilePath, FilePath)] -- the files written, by that path and the way the program first spelled it
    , sHeap :: Map Integer Allocation -- the memory that Addr::alloc gave, by the number of each allocation
    , sNextAllocation :: Integer
    , sFrames :: Map Integer Frame
    , sFrame :: Frame
    , sCurrentFrame :: Maybe Integer
    , sNextFrame :: Integer
    }

-- The memory of an allocation: its slots, each holding a value or nothing (POINTERS.md). An address is a number: allocation k starts at
-- k * 2^32 and a slot is one more than the slot before it, so that `Addr::offset` is a sum, `Addr::toInt` is the number (which is not the
-- one native code has) and the null address, 0, is in no allocation. A read of an empty slot, a write over a filled one, a use of memory
-- that was freed or never allocated, and a free of memory that still holds a value are errors: a proved program does none of them, so
-- this is a check of what a program assumes (Block::assume).
data Allocation = Allocation {allocSize :: Integer, allocSlots :: Map Integer MirValue}

startState :: String -> S
startState input = S{sInput = input, sPath = "", sLoaded = "", sStore = "", sFiles = Map.empty, sOrder = [], sHeap = Map.empty, sNextAllocation = 1, sFrames = Map.empty, sFrame = Map.empty, sCurrentFrame = Nothing, sNextFrame = 1}

allocationSpan :: Integer
allocationSpan = 2 ^ (32 :: Integer)

-- The allocation an address is in and the slot it is, if it is the address of a slot of an allocation that is there
slotAt :: S -> Integer -> Result (Integer, Allocation, Integer) String
slotAt s address =
    let (k, slot) = address `divMod` allocationSpan
     in case Map.lookup k (sHeap s) of
            Just a | slot < allocSize a -> Ok (k, a, slot)
            Just _ -> Error "An address past the end of its allocation was used"
            Nothing -> Error "An address of memory that is not allocated (it was freed, or never allocated) was used"

heapE :: (S -> Result (a, S) String) -> E a
heapE f = E (\_ s -> mapResult (\(a, s') -> (a, none, s')) (f s))

-- n new slots, all empty: the address of the first
allocate :: Integer -> E Integer
allocate n
    | n < 0 = failE "Addr::alloc needs a number of slots that is not negative"
    | n >= allocationSpan = failE "Addr::alloc was asked for more memory than there is"
    | otherwise = heapE (\s -> let k = sNextAllocation s in Ok (k * allocationSpan, s{sHeap = Map.insert k (Allocation n Map.empty) (sHeap s), sNextAllocation = k + 1}))

-- The value in a slot, which stays there, or which is taken out of it
readSlot :: Bool -> Integer -> E MirValue
readSlot taking address = heapE $ \s ->
    slotAt s address `bindResult` \(k, a, slot) -> case Map.lookup slot (allocSlots a) of
        Nothing -> Error "A slot that holds no value was read"
        Just v -> Ok (v, if taking then s{sHeap = Map.insert k a{allocSlots = Map.delete slot (allocSlots a)} (sHeap s)} else s)

writeSlot :: Integer -> MirValue -> E ()
writeSlot address value = do
    frame <- currentFrame
    v <- captureValue frame value
    heapE $ \s ->
        slotAt s address `bindResult` \(k, a, slot) ->
            if Map.member slot (allocSlots a)
                then Error "A value was written over a slot that holds one"
                else Ok ((), s{sHeap = Map.insert k a{allocSlots = Map.insert slot v (allocSlots a)} (sHeap s)})

-- The allocation that starts at the address
wholeAt :: S -> Integer -> Result (Integer, Allocation) String
wholeAt s address =
    let (k, slot) = address `divMod` allocationSpan
     in case Map.lookup k (sHeap s) of
            Just a | slot == 0 -> Ok (k, a)
            Just _ -> Error "Memory was freed or resized from an address that is not the start of its allocation"
            Nothing -> Error "Memory that is not allocated (it was freed already, or never allocated) was freed or resized"

release :: Integer -> E ()
release address = heapE $ \s ->
    wholeAt s address `bindResult` \(k, a) ->
        if Map.null (allocSlots a)
            then Ok ((), s{sHeap = Map.delete k (sHeap s)})
            else Error "Memory that still holds a value was freed, which would lose it"

-- The slots moved to a new allocation of n: those from n have to be empty
reallocate :: Integer -> Integer -> E Integer
reallocate address n = do
    moved <- heapE (\s -> wholeAt s address `bindResult` \(k, a) ->
        if any (>= n) (Map.keys (allocSlots a))
            then Error "Memory was resized to fewer slots than hold values"
            else Ok (allocSlots a, s{sHeap = Map.delete k (sHeap s)}))
    q <- allocate n
    heapE (\s -> let k = q `div` allocationSpan in Ok (q, s{sHeap = Map.adjust (\a -> a{allocSlots = moved}) k (sHeap s)}))

-- The evaluator is a function of what the program is run in and of its state, and the failure of a result, with the bytes written so far
newtype E a = E {runE :: RunEnv -> S -> Result (a, Written, S) String}

-- Execute a named MIR function in an empty host environment. The caller is
-- responsible for the types, invariants and contracts of the arguments.
runNamedFunction :: Program -> Name -> [MirValue] -> Result (Maybe MirValue) String
runNamedFunction program name args = case Map.lookup name (progFunctions program) of
    Nothing -> Error ("Function does not exist: " ++ name)
    Just fn -> mapResult (\((value, _), _, _) -> value) (runE (runFunction program fn args Map.empty) RunEnv{envArgs = [], envInput = "", envFile = const Nothing} (startState ""))

instance Functor E where
    fmap f (E r) = E (\env s -> mapResult (\(a, output, s') -> (f a, output, s')) (r env s))

instance Applicative E where
    pure a = E (\_ s -> Ok (a, none, s))
    E f <*> E g = E (\env s -> f env s `bindResult` \(h, o1, s') -> mapResult (\(a, o2, s'') -> (h a, together o1 o2, s'')) (g env s'))

instance Monad E where
    E g >>= f = E (\env s -> g env s `bindResult` \(a, o1, s') -> runE (f a) env s' `bindResult` \(b, o2, s'') -> Ok (b, together o1 o2, s''))

together :: Written -> Written -> Written
together (out1, err1) (out2, err2) = (out1 ++ out2, err1 ++ err2)

failE :: String -> E a
failE e = E (\_ _ -> Error e)

liftE :: Result a String -> E a
liftE r = E (\_ s -> mapResult (\a -> (a, none, s)) r)

write :: Char -> E ()
write c = E (\_ s -> Ok ((), ([c], ""), s))

writeError :: Char -> E ()
writeError c = E (\_ s -> Ok ((), ("", [c]), s))

-- The next byte of the input, or -1 at its end
readInput :: E Integer
readInput = E (\_ s -> case sInput s of
    [] -> Ok (-1, none, s)
    c : rest -> Ok (toInteger (fromEnum c `mod` 256), none, s{sInput = rest}))

-- The arguments of the program
arguments :: E [String]
arguments = E (\env s -> Ok (envArgs env, none, s))

-- A byte more in the path of the file to be loaded or stored (as long as a path is, in the runtime); the length of the path
pathByte :: Integer -> E Integer
pathByte b = E (\_ s ->
    let path = if length (sPath s) < 4095 then sPath s ++ [toEnum (fromInteger (b `mod` 256))] else sPath s
     in Ok (toInteger (length path), none, s{sPath = path}))

-- The path that has been built, up to a byte that is 0 as in the runtime
builtPath :: S -> FilePath
builtPath = takeWhile (/= '\0') . sPath

-- A path with what does not name another file taken out, so that two spellings of one file are one key: `x`, `./x` and `d/../x` (and `a//b`, `a/b/`),
-- the way the system reads them (but for a link, which it follows, and a name in a file system that does not tell capitals apart, which the interpreter
-- does not know of)
samePath :: FilePath -> FilePath
samePath path = (if absolute then "/" else "") ++ intercalate "/" (reverse kept)
  where
    absolute = take 1 path == "/"
    kept = foldl step [] (segments path)
    step acc segment = case segment of
        "" -> acc
        "." -> acc
        ".." -> case acc of
            previous : more | previous /= ".." -> more
            [] | absolute -> []
            _ -> ".." : acc
        _ -> segment : acc
    segments text = case break (== '/') text of
        (segment, []) -> [segment]
        (segment, _ : rest) -> segment : segments rest

-- Loads the file at the path that has been built, and clears the path: its size, or -1 when there is no such file
fileLoad :: E Integer
fileLoad = E (\env s ->
    let path = builtPath s
        contents = if null path then Nothing else maybe (envFile env path) Just (Map.lookup (samePath path) (sFiles s))
     in case contents of
            Just c -> Ok (toInteger (length c), none, s{sPath = "", sLoaded = c})
            Nothing -> Ok (-1, none, s{sPath = "", sLoaded = ""}))

-- The byte i of the file that was loaded, or -1
fileByteAt :: Integer -> E Integer
fileByteAt i = E (\_ s ->
    let c = sLoaded s
     in Ok (if i >= 0 && i < toInteger (length c) then toInteger (fromEnum (c !! fromInteger i) `mod` 256) else -1, none, s))

-- A byte more in the file to be stored; its length
storeByte :: Integer -> E Integer
storeByte b = E (\_ s -> let store = sStore s ++ [toEnum (fromInteger (b `mod` 256))] in Ok (toInteger (length store), none, s{sStore = store}))

-- Stores the bytes that have been given in the file at the path that has been built, which holds only them after: 0, or -1 when there is no path
fileStore :: E Integer
fileStore = E (\_ s ->
    let path = builtPath s
     in if null path
            then Ok (-1, none, s{sPath = "", sStore = ""})
            else
                Ok
                    ( 0
                    , none
                    , s{ sPath = ""
                       , sStore = ""
                       , sFiles = Map.insert (samePath path) (sStore s) (sFiles s)
                       , sOrder = if samePath path `elem` map fst (sOrder s) then sOrder s else sOrder s ++ [(samePath path, path)]
                       }
                    ))

runFunction :: Program -> Function -> [MirValue] -> Frame -> E (Maybe MirValue, Frame)
runFunction program fn args extra
    | length args /= length (fnParams fn) =
        failE ("Function expected " ++ show (length (fnParams fn)) ++ " arguments, got " ++ show (length args))
    | otherwise = do
        let initial = Map.union extra (Map.fromList (zip (fnParams fn) args))
        (_identity, parent) <- heapE $ \s ->
            if sCurrentFrame s == Nothing && any hasFrameReference (Map.elems initial)
                then Error "A frame reference from another evaluation was used"
                else let identity = sNextFrame s
                         frame = case sCurrentFrame s of
                             Nothing -> Map.map (qualifyRefs identity initial) initial
                             Just _ -> initial
                      in Ok ((identity, sCurrentFrame s), s{sFrames = maybe (sFrames s) (\parent -> Map.insert parent (sFrame s) (sFrames s)) (sCurrentFrame s), sFrame = frame, sCurrentFrame = Just identity, sNextFrame = identity + 1})
        initial' <- currentFrame
        (result, _) <- runBlock program fn (BlockId 0) initial'
        final <- currentFrame
        heapE $ \s -> case parent of
            Nothing -> Ok ((), s{sFrame = Map.empty, sCurrentFrame = Nothing})
            Just caller -> case Map.lookup caller (sFrames s) of
                Nothing -> Error "The suspended caller frame is not there"
                Just callerFrame -> Ok ((), s{sFrames = Map.delete caller (sFrames s), sFrame = callerFrame, sCurrentFrame = parent})
        return (result, final)

type Frame = Map Local MirValue

hasFrameReference :: MirValue -> Bool
hasFrameReference MFrameRef{} = True
hasFrameReference (MData _ fields) = any (hasFrameReference . snd) fields
hasFrameReference (MSequence values) = any hasFrameReference values
hasFrameReference _ = False

currentIdentity :: E Integer
currentIdentity = heapE (\s -> maybe (Error "No active reference frame") (\identity -> Ok (identity, s)) (sCurrentFrame s))

frameAt :: Integer -> E Frame
frameAt identity = E $ \_ s ->
    if sCurrentFrame s == Just identity
        then Ok (sFrame s, none, s)
        else maybe (Error "A reference to an exited frame was used") (\frame -> Ok (frame, none, s)) (Map.lookup identity (sFrames s))

currentFrame :: E Frame
currentFrame = E $ \_ s -> case sCurrentFrame s of
    Nothing -> Error "No active reference frame"
    Just _ -> Ok (sFrame s, none, s)

storeFrame :: Integer -> Frame -> E ()
storeFrame identity frame = E $ \_ s ->
    if sCurrentFrame s == Just identity
        then Ok ((), none, s{sFrame = frame})
        else if Map.member identity (sFrames s)
            then Ok ((), none, s{sFrames = Map.insert identity frame (sFrames s)})
            else Error "A reference to an exited frame was updated"

storeCurrentFrame :: Frame -> E ()
storeCurrentFrame frame = E $ \_ s -> case sCurrentFrame s of
    Nothing -> Error "No active reference frame"
    Just _ -> Ok ((), none, s{sFrame = frame})

captureValue :: Frame -> MirValue -> E MirValue
captureValue frame value = do
    identity <- currentIdentity
    return (qualifyRefs identity frame value)

qualifyRefs :: Integer -> Frame -> MirValue -> MirValue
qualifyRefs identity frame value = case value of
    MRef{} -> case normaliseRefs frame value of
        MRef root steps -> MFrameRef identity root steps
        qualified -> qualified
    MData name fields -> MData name [(field, qualifyRefs identity frame child) | (field, child) <- fields]
    MSequence values -> MSequence (fmap (qualifyRefs identity frame) values)
    qualified -> qualified

runBlock :: Program -> Function -> BlockId -> Frame -> E (Maybe MirValue, Frame)
runBlock program fn block frame =
    case Map.lookup block (fnBlocks fn) of
        Nothing -> failE ("Jump to a block that does not exist: " ++ show block)
        Just (BasicBlock stmts term) -> do
            frame' <- runStatements program fn frame stmts
            case term of
                Goto next -> runBlock program fn next frame'
                SwitchBool test yes no -> do
                    v <- intOrValue frame' test
                    case v of
                        MBool True -> runBlock program fn yes frame'
                        MBool False -> runBlock program fn no frame'
                        _ -> failE "Condition must be a boolean"
                Call callee args dest next -> do
                    f <- intOrValue frame' callee
                    target <- case f of
                        MFn name -> maybe (failE ("Call of a function that does not exist: " ++ name)) return (Map.lookup name (progFunctions program))
                        _ -> failE "Object being called must be a function"
                    argValues <- prepareArguments fn target args
                    (result, _) <- callFunction program f argValues Map.empty
                    refreshed <- currentFrame
                    runBlock program fn next (Map.insert dest result refreshed)
                Return -> return (Map.lookup (Local 0) frame', frame')
                Unreachable -> failE "Function did not return a value"

prepareArguments :: Function -> Function -> [Operand] -> E [MirValue]
prepareArguments caller callee args
    | length args /= length (fnParams callee) = failE ("Function expected " ++ show (length (fnParams callee)) ++ " arguments, got " ++ show (length args))
    | otherwise = mapM argument (zip (fnParams callee) args)
  where
    argument (param, operand) = do
        frame <- currentFrame
        value <- liftE (operandValue frame operand)
        if param `elem` fnBorrowed callee || maybe False (referenceType . localType) (Map.lookup param (fnLocals callee))
            then case value of
                MRef{} -> captureValue frame value
                MFrameRef{} -> return value
                MHeapRef{} -> return value
                _ -> case operand of
                    Copy root -> captureValue frame (MRef root [])
                    Move root -> captureValue frame (MRef root [])
                    Const _ -> do
                        let root = Local (minimum (0 : [slot | Local slot <- Map.keys frame ++ Map.keys (fnLocals caller)]) - 1)
                        storeCurrentFrame (Map.insert root value frame)
                        captureValue frame (MRef root [])
            else if maybe False (referencePayload . localType) (Map.lookup param (fnLocals callee))
                then return value
                else resolveContents frame value

referencePayload :: Type -> Bool
referencePayload (TBox inner) = referencePayload inner
referencePayload (TUninit inner) = referencePayload inner
referencePayload ty = referenceType ty

referenceType :: Type -> Bool
referenceType TRef{} = True
referenceType TMutRef{} = True
referenceType _ = False

resolveReference :: Frame -> MirValue -> E MirValue
resolveReference frame value = case value of
    MRef{} -> captureValue frame value >>= resolveReference frame
    MFrameRef identity root steps -> do
        target <- frameAt identity
        base <- maybe (failE ("Undefined reference root: " ++ show root)) return (Map.lookup root target)
        walk target steps base
    MHeapRef address steps -> readSlot False address >>= walk frame steps
    _ -> return value
  where
    walk _ [] base = return base
    walk context steps base | isReference base = resolveReference context base >>= walk context steps
    walk context (EvalField field : rest) (MData _ fields) = case lookup field fields of
        Nothing -> failE ("A reference is to a field that is not there: " ++ field)
        Just child -> walk context rest child
    walk context (EvalIndex i : rest) (MSequence values)
        | i >= 0 && i < toInteger (Seq.length values) = walk context rest (Seq.index values (fromInteger i))
        | otherwise = failE "A reference is to an index that is not there"
    walk _ _ _ = failE "A reference is to a place that is not there"

isReference :: MirValue -> Bool
isReference MRef{} = True
isReference MFrameRef{} = True
isReference MHeapRef{} = True
isReference _ = False

resolveContents :: Frame -> MirValue -> E MirValue
resolveContents frame value
    | isReference value = resolveReference frame value >>= resolveContents frame
    | otherwise = return value

appendReference :: MirValue -> [EvalStep] -> MirValue
appendReference (MRef root steps) rest = MRef root (steps ++ rest)
appendReference (MFrameRef identity root steps) rest = MFrameRef identity root (steps ++ rest)
appendReference (MHeapRef address steps) rest = MHeapRef address (steps ++ rest)
appendReference value _ = value

writeReference :: Frame -> MirValue -> MirValue -> E ()
writeReference context target value = case target of
    MRef{} -> captureValue context target >>= \qualified -> writeReference context qualified value
    MFrameRef identity root steps -> do
        frame <- frameAt identity
        base <- maybe (failE ("Undefined reference root: " ++ show root)) return (Map.lookup root frame)
        changed <- setPath frame base steps value
        refreshed <- frameAt identity
        storeFrame identity (Map.insert root changed refreshed)
    MHeapRef{} -> do
        held <- resolveReference context target
        if isReference held
            then writeReference context held value
            else failE "A raw heap reference cannot be written through"
    _ -> failE "A value that is not a reference is written through"
  where
    setPath _ _ [] new = return new
    setPath frame base rest new | isReference base = writeReference frame (appendReference base rest) new >> return base
    setPath frame (MData name fields) (EvalField field : rest) new = case lookup field fields of
        Nothing -> failE ("A reference is to a field that is not there: " ++ field)
        Just old -> do
            changed <- setPath frame old rest new
            return (MData name [(f, if f == field then changed else v) | (f, v) <- fields])
    setPath frame (MSequence values) (EvalIndex i : rest) new
        | i >= 0 && i < toInteger (Seq.length values) = do
            changed <- setPath frame (Seq.index values (fromInteger i)) rest new
            return (MSequence (Seq.update (fromInteger i) changed values))
        | otherwise = failE "A reference is to an index that is not there"
    setPath _ _ _ _ = failE "A reference is to a place that is not there"

callFunction :: Program -> MirValue -> [MirValue] -> Frame -> E (MirValue, Frame)
callFunction _ (MFn name) _ _
    | take 7 name == "extern " = failE ("The extern function " ++ drop 7 name ++ " is a function of C, which only native code can call")
callFunction program (MFn name) args extra =
    case Map.lookup name (progFunctions program) of
        Nothing -> failE ("Call of a function that does not exist: " ++ name)
        Just fn -> do
            (result, frame) <- runFunction program fn args extra
            value <- maybe (failE "Function did not return a value") return result
            return (value, frame)
callFunction _ _ _ _ = failE "Object being called must be a function"

normaliseRefs :: Frame -> MirValue -> MirValue
normaliseRefs frame value = case value of
    MRef l steps -> case Map.lookup l frame of
        Just (MRef l2 steps2) -> normaliseRefs frame (MRef l2 (steps2 ++ steps))
        Just (MHeapRef address steps2) -> MHeapRef address (steps2 ++ steps)
        Just (MFrameRef identity root steps2) -> MFrameRef identity root (steps2 ++ steps)
        _ -> MRef l steps
    MData name fields -> MData name [(f, normaliseRefs frame v) | (f, v) <- fields]
    MSequence values -> MSequence (fmap (normaliseRefs frame) values)
    _ -> value

runStatements :: Program -> Function -> Frame -> [Statement] -> E Frame
runStatements program fn frame stmts = storeCurrentFrame frame >> runStatementsStep program fn frame stmts

runStatementsStep :: Program -> Function -> Frame -> [Statement] -> E Frame
runStatementsStep _ _ frame [] = return frame
runStatementsStep program fn frame (Ghost{} : rest) = runStatements program fn frame rest
runStatementsStep program fn frame (Drop{} : rest) = runStatements program fn frame rest
runStatementsStep program fn frame (Peek dest rv : rest) = runStatementsStep program fn frame (Assign dest rv : rest)
runStatementsStep program fn frame (Assign dest (ListOp PathByte [b]) : rest) = intArgument frame b >>= \x -> pathByte x >>= \n -> runStatements program fn (Map.insert dest (MInt n) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp FileLoad []) : rest) = fileLoad >>= \n -> runStatements program fn (Map.insert dest (MInt n) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp FileByte [i]) : rest) = intArgument frame i >>= \x -> fileByteAt x >>= \n -> runStatements program fn (Map.insert dest (MInt n) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp StoreByte [b]) : rest) = intArgument frame b >>= \x -> storeByte x >>= \n -> runStatements program fn (Map.insert dest (MInt n) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp FileStore []) : rest) = fileStore >>= \n -> runStatements program fn (Map.insert dest (MInt n) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp ArgCount []) : rest) = do
    args <- arguments
    runStatements program fn (Map.insert dest (MInt (toInteger (length args))) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp ArgByte [i, j]) : rest) = do
    args <- arguments
    iv <- intOrValue frame i
    jv <- intOrValue frame j
    let byte = case (iv, jv) of
            (MInt a, MInt b)
                | a >= 0 && a < toInteger (length args) && b >= 0 && b < toInteger (length (args !! fromInteger a)) -> toInteger (fromEnum (args !! fromInteger a !! fromInteger b) `mod` 256)
            _ -> -1
    runStatements program fn (Map.insert dest (MInt byte) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp ReadByte []) : rest) = do
    b <- readInput
    runStatements program fn (Map.insert dest (MInt b) frame) rest
runStatementsStep program fn frame (Assign dest (ListOp WriteByte [o]) : rest) = do
    v <- intOrValue frame o
    case v of
        MInt b -> write (chr (fromIntegral (b `mod` 256))) >> runStatements program fn (Map.insert dest v frame) rest
        _ -> failE "writeByte takes an Int"
runStatementsStep program fn frame (Assign dest (ListOp WriteError [o]) : rest) = do
    v <- intOrValue frame o
    case v of
        MInt b -> writeError (chr (fromIntegral (b `mod` 256))) >> runStatements program fn (Map.insert dest v frame) rest
        _ -> failE "writeError takes an Int"
runStatementsStep program fn frame (Assign dest (ListOp op os) : rest) | Just run <- memoryOp op = do
    args <- case (op, os) of
        (AddrBorrow, [p, i, _]) -> do
            address <- intOrValue frame p
            index <- intOrValue frame i
            return [address, index, MEmpty]
        (AddrWrite, [p, i, x]) -> do
            address <- intOrValue frame p
            index <- intOrValue frame i
            let element = case p of
                    Copy root -> addressElement root
                    Move root -> addressElement root
                    Const _ -> TInt
                addressElement root = case Map.lookup root (fnLocals fn) of
                    Just decl -> case localType decl of TAddr inner -> inner; _ -> TInt
                    Nothing -> TInt
            v <- evalValue program fn frame element (Use x)
            return [address, index, v]
        _ -> mapM (intOrValue frame) os
    v <- run args
    runStatements program fn (Map.insert dest v frame) rest
runStatementsStep program fn frame (AssignRef root steps rv : rest) = do
    let target = referencePlaceType program fn root steps
    v <- evalValue program fn frame target rv
    evalSteps <- mapM (evalReferenceStep frame) steps
    writeReference frame (normaliseRefs frame (MRef root evalSteps)) v
    refreshed <- currentFrame
    runStatements program fn refreshed rest
runStatementsStep program fn frame (Assign dest rv : rest) = do
    let target = maybe TInt localType (Map.lookup dest (fnLocals fn))
    v <- evalValue program fn frame target rv
    runStatements program fn (Map.insert dest v frame) rest

referencePlaceType :: Program -> Function -> Local -> [RefStep] -> Type
referencePlaceType program fn root = foldl project (contents (maybe TInt localType (Map.lookup root (fnLocals fn))))
  where
    contents (TRef ty) = ty
    contents (TMutRef ty) = ty
    contents (TBox ty) = ty
    contents ty = ty
    project ty (RefIndex _) = case contents ty of
        TList element -> element
        TArrayOf element _ -> element
        _ -> TInt
    project _ (RefField name field) = case Map.lookup name (progTypes program) of
        Just (StructDecl fields) -> maybe TInt id (lookup field fields)
        Just (EnumDecl variants) -> maybe TInt id (lookup field (concatMap snd variants))
        Nothing -> maybe TInt id (lookup field (concat [fields | EnumDecl variants <- Map.elems (progTypes program), (variant, fields) <- variants, variant == name]))

evalReferenceStep :: Frame -> RefStep -> E EvalStep
evalReferenceStep _ (RefField _ field) = return (EvalField field)
evalReferenceStep frame (RefIndex operand) = intArgument frame operand >>= return . EvalIndex

intOrValue :: Frame -> Operand -> E MirValue
intOrValue frame operand = case operandValue frame operand of
    Ok value | not (isReference value) -> pure value
    result -> liftE result >>= resolveContents frame

evalValue :: Program -> Function -> Frame -> Type -> Rvalue -> E MirValue
evalValue program fn frame target rv = case rv of
    Use o -> valueAtType target o
    CopyOf o -> valueAtType target o
    Borrow root steps _ -> do
        evaluated <- mapM step steps
        captureValue frame (MRef root evaluated)
    BinaryOp op a b -> case (operandValue frame a, operandValue frame b) of
        (Ok x, Ok y) | not (isReference x || isReference y) -> liftE (binary op x y)
        _ -> do
            x <- value a
            y <- value b
            liftE (binary op x y)
    ListOp Push [container, item] -> do
        base <- value container
        child <- valueAtType (elementOf target) item
        liftE (listOp Push [base, child])
    ListOp Set [container, index, item] -> do
        base <- value container
        i <- value index
        child <- valueAtType (elementOf target) item
        liftE (listOp Set [base, i, child])
    ListOp op [count, item] | op == NewArray || op == NewBoxed -> do
        n <- value count
        child <- valueAtType (elementOf target) item
        liftE (listOp op [n, child])
    ListOp UninitNew [item] -> do
        child <- valueAtType (case target of TUninit inner -> inner; _ -> target) item
        liftE (listOp UninitNew [child])
    ListOp op [item] | op == UninitGet || op == UninitTake -> do
        child <- valueAtType target item
        liftE (listOp op [child])
    ListOp op os -> mapM value os >>= liftE . listOp op
    MakeList os -> MList <$> mapM (valueAtType (elementOf target)) os
    MakeBox o -> valueAtType (case target of TBox inner -> inner; _ -> target) o
    Unbox o -> do
        v <- liftE (operandValue frame o)
        case v of MHeapRef{} -> resolveReference frame v; _ -> return v
    Unsize o -> valueAtType target o
    MakeData name fields -> do
        values <- mapM (\(field, o) -> (,) field <$> valueAtType (fieldType name field) o) fields
        return (MData (plain name) values)
    IsVariant o name -> do
        v <- value o
        case v of MData actual _ -> return (MBool (actual == plain name)); _ -> failE "Is only tests the variant of an enum value"
    AsVariant o _ -> value o
    TakeField root name field -> evalValue program fn frame target (ReadField (Copy root) name field)
    ReadField o name field -> do
        v <- value o
        case v of
            MData actual fields | actual /= plain name -> failE ("Expected a " ++ name ++ " but got a " ++ actual)
                               | otherwise -> maybe (failE ("Variant " ++ name ++ " has no field " ++ field)) (atType target) (lookup field fields)
            MList values | field == "len" || field == "cap" -> return (MInt (toInteger (length values)))
            _ -> failE "A field can only be read from a struct"
    Deref o -> do
        v <- liftE (operandValue frame o) >>= resolveReference frame
        atType target v
  where
    value = intOrValue frame
    valueAtType ty o = case operandValue frame o of
        Ok v | not (referencePayload ty || isReference v) -> pure v
        result -> liftE result >>= atType ty
    atType ty v | referencePayload ty = captureValue frame v
                | otherwise = resolveContents frame v
    elementOf (TList inner) = inner
    elementOf (TArrayOf inner _) = inner
    elementOf (TBox inner) = elementOf inner
    elementOf _ = TInt
    fieldType name field = case Map.lookup name (progTypes program) of
        Just (StructDecl fields) -> maybe TInt id (lookup field fields)
        Just (EnumDecl variants) -> maybe TInt id (lookup field (concatMap snd variants))
        Nothing -> maybe TInt id (lookup field (concat [fields | EnumDecl variants <- Map.elems (progTypes program), (variant, fields) <- variants, variant == name]))
    step (RefField _ field) = return (EvalField field)
    step (RefIndex o) = do
        v <- value o
        case v of MInt index -> return (EvalIndex index); _ -> failE "The index of a borrowed place is not an Int"

-- The operations on memory, which change the heap (the permissions they were given are erased by the ghost erasure)
memoryOp :: ListOp -> Maybe ([MirValue] -> E MirValue)
memoryOp op = case op of
    AddrAlloc -> Just (\args -> case args of
        [MInt n] -> MInt <$> allocate n
        _ -> bad)
    AddrBorrow -> Just (\args -> case args of
        [MInt p, MInt i, _] -> readSlot False (p + i) >> return (MHeapRef (p + i) [])
        _ -> bad)
    AddrGet -> Just (\args -> case args of
        [MInt p, MInt i] -> readSlot False (p + i)
        _ -> bad)
    AddrTakeArray -> Just (\args -> case args of
        [MInt p, MInt n]
            | n < 0 -> failE "Addr::takeArray needs a non-negative prefix length"
            | otherwise -> MList <$> mapM (readSlot True . (p +)) [0 .. n - 1]
        _ -> bad)
    AddrTake -> Just (\args -> case args of
        [MInt p, MInt i] -> readSlot True (p + i)
        _ -> bad)
    AddrWrite -> Just (\args -> case args of
        [MInt p, MInt i, x] -> writeSlot (p + i) x >> return (MInt 0)
        _ -> bad)
    AddrDropValue -> Just (\args -> case args of
        [MInt p, MInt i] -> readSlot True (p + i) >> return (MInt 0)
        _ -> bad)
    AddrDropRange -> Just (\args -> case args of
        [MInt p, MInt i, MInt n] -> mapM_ (\j -> readSlot True (p + j)) [i .. i + n - 1] >> return (MInt 0)
        _ -> bad)
    AddrResize -> Just (\args -> case args of
        [MInt p, MInt n]
            | n < 0 -> failE "Addr::resize needs a number of slots that is not negative"
            | otherwise -> MInt <$> reallocate p n
        _ -> bad)
    AddrFree -> Just (\args -> case args of
        [MInt p] -> release p >> return (MInt 0)
        _ -> bad)
    _ -> Nothing
  where
    bad = failE (show op ++ " is given an address, numbers and a value, without the permission (which is erased before the program runs)")

-- The Int that an operand is
intArgument :: Frame -> Operand -> E Integer
intArgument frame o = do
    v <- liftE (operandValue frame o) >>= resolveContents frame
    case v of
        MInt n -> return n
        _ -> failE "An Int was expected"

operandValue :: Frame -> Operand -> Result MirValue String
operandValue frame (Copy l) = maybe (Error ("Undefined variable: " ++ show l)) Ok (Map.lookup l frame)
-- (a value is a value here: who owns it only matters to native code, so owned MIR gives the same results)
operandValue frame (Move l) = operandValue frame (Copy l)
operandValue _ (Const c) = Ok (constantValue c)

constantValue :: Constant -> MirValue
constantValue (CInt i) = MInt i
constantValue (CBool b) = MBool b
constantValue (CList cs) = MList (map constantValue cs)
constantValue (CArray cs) = MList (map constantValue cs)
constantValue (CData name fields) = MData (plain name) [(f, constantValue c) | (f, c) <- fields]
constantValue (CFn name) = MFn name

binary :: BinOp -> MirValue -> MirValue -> Result MirValue String
binary Add (MInt a) (MInt b) = checked (a + b)
binary Sub (MInt a) (MInt b) = checked (a - b)
binary Mul (MInt a) (MInt b) = checked (a * b)
binary Div (MInt _) (MInt 0) = Error "Division by zero"
binary Div (MInt a) (MInt b) = checked (a `div` b)
binary Mod (MInt _) (MInt 0) = Error "Modulo by zero"
binary Mod (MInt a) (MInt b) = Ok (MInt (a `mod` b))
binary (Compare Eq) a b | comparable a b = Ok (MBool (a == b))
binary (Compare NotEq) a b | comparable a b = Ok (MBool (a /= b))
binary (Compare Lt) (MInt a) (MInt b) = Ok (MBool (a < b))
binary (Compare Gt) (MInt a) (MInt b) = Ok (MBool (a > b))
binary (Compare LtEq) (MInt a) (MInt b) = Ok (MBool (a <= b))
binary (Compare GtEq) (MInt a) (MInt b) = Ok (MBool (a >= b))
binary op _ _ = Error (show op ++ " is not defined for these values")

-- Int is 64 bits: addition, subtraction, multiplication and division that leave the range stop the program
checked :: Integer -> Result MirValue String
checked n
    | inIntRange n = Ok (MInt n)
    | otherwise = Error "Integer overflow"

-- Only words are compared: any other value is compared by its Eq, which the checker calls in its place (lib/eq.tersus)
comparable :: MirValue -> MirValue -> Bool
comparable (MInt _) (MInt _) = True
comparable (MBool _) (MBool _) = True
comparable _ _ = False

listOp :: ListOp -> [MirValue] -> Result MirValue String
listOp Length [MSequence l] = Ok (MInt (fromIntegral (Seq.length l)))
listOp First [MSequence l] = case Seq.viewl l of
    EmptyL -> Error "First requires a non-empty list"
    x :< _ -> Ok x
listOp Last [MSequence l] = case Seq.viewr l of
    EmptyR -> Error "Last requires a non-empty list"
    _ :> x -> Ok x
listOp Get [MSequence l, MInt i]
    | i < 0 || i >= fromIntegral (Seq.length l) = Error "Get index out of range"
    | otherwise = Ok (Seq.index l (fromIntegral i))
listOp Push [MSequence l, x] = Ok (MSequence (l |> x))
listOp Pop [MSequence l] = case Seq.viewr l of
    EmptyR -> Error "Pop requires a non-empty list"
    rest :> _ -> Ok (MSequence rest)
listOp NewBoxed args = listOp NewArray args
listOp WriteByte _ = Error "writeByte is run by the statement that calls it"
listOp WriteError _ = Error "writeError is run by the statement that calls it"
listOp ToByte [MInt x]
    | x >= 0 && x < 256 = Ok (MInt x)
    | otherwise = Error "toByte needs an Int from 0 to 255"
listOp FromByte [MInt b] = Ok (MInt b)
listOp (Narrow signed bits) [MInt x]
    | x >= low && x < high = Ok (MInt x)
    | otherwise = Error ("The Int is not in the range of the fixed-width integer it is made")
  where
    (low, high) = if signed then (negate (2 ^ (bits - 1)), 2 ^ (bits - 1)) else (0, 2 ^ bits)
listOp ReadByte _ = Error "readByte is run by the statement that calls it"
listOp ArgCount _ = Error "argCount is run by the statement that calls it"
listOp ArgByte _ = Error "argByte is run by the statement that calls it"
listOp op _ | op `elem` [PathByte, FileLoad, FileByte, StoreByte, FileStore] = Error "a file operation is run by the statement that calls it"
listOp NewEmptyBoxed [] = Ok (MSequence Seq.empty)
listOp FromList [MSequence l] = Ok (MSequence l)
listOp NewArray [MInt n, x]
    | n < 0 = Error "array needs a size that is not negative"
    | otherwise = Ok (MSequence (Seq.replicate (max 0 (fromIntegral n)) x))
listOp Set [MSequence l, MInt i, x]
    | i < 0 || i >= fromIntegral (Seq.length l) = Error "Set index out of range"
    | otherwise = Ok (MSequence (Seq.update (fromIntegral i) x l))
listOp UninitEmpty [] = Ok MEmpty
listOp UninitNew [x] = Ok x
listOp UninitGet [MEmpty] = Error "An Uninit that holds nothing was read"
listOp UninitGet [x] = Ok x
listOp UninitTake [MEmpty] = Error "An Uninit that holds nothing was taken"
listOp UninitTake [x] = Ok x
listOp UninitDiscard [MEmpty] = Ok (MInt 0)
listOp UninitDiscard [_] = Error "An Uninit that holds a value was discarded, which would lose it"
-- (an address is a number: see Allocation)
listOp AddrNull [] = Ok (MInt 0)
listOp AddrOffset [MInt p, MInt i] = checked (p + i)
listOp AddrCast [p] = Ok p
listOp AddrToInt [p] = Ok p
listOp AddrFromInt [n] = Ok n
listOp op _ = Error (show op ++ " is not defined for these values")

-- A struct with sizes is one struct to a program that runs: the sizes are in the name of each copy that native code makes, and
-- not in a value (`Packet<n>` and `Packet<3>` are both a Packet)
plain :: Name -> Name
plain = takeWhile (/= '<')

renderMirValue :: MirValue -> String
renderMirValue (MInt i) = show i
renderMirValue (MBool True) = "true"
renderMirValue (MBool False) = "false"
renderMirValue (MList l) = "[" ++ intercalate ", " (map renderMirValue l) ++ "]"
renderMirValue (MData name []) = name
renderMirValue (MData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderMirValue v | (f, v) <- fields] ++ " }"
renderMirValue MFn{} = "<function>"
renderMirValue MEmpty = "<empty>"
renderMirValue MRef{} = "<reference>"
renderMirValue MFrameRef{} = "<reference>"
renderMirValue MHeapRef{} = "<reference>"

-- The value of the AST that a value of the MIR is, and the other way: a function of the program is VFnRef, and no function
-- written in the AST is a value of the MIR
fromMirValue :: MirValue -> Value
fromMirValue (MInt i) = VInt i
fromMirValue (MBool b) = VBool b
fromMirValue (MList vs) = VList (map fromMirValue vs)
fromMirValue (MData name fields) = VData name [(f, fromMirValue v) | (f, v) <- fields]
fromMirValue (MFn name) = VFnRef name
fromMirValue MEmpty = VData "<empty>" []
fromMirValue MRef{} = error "A runtime reference cannot be converted to a proof value"
fromMirValue MFrameRef{} = error "A runtime reference cannot be converted to a proof value"
fromMirValue MHeapRef{} = error "A runtime reference cannot be converted to a proof value"

toMirValue :: Value -> Maybe MirValue
toMirValue (VInt i) = Just (MInt i)
toMirValue (VBool b) = Just (MBool b)
toMirValue (VList vs) = MList <$> mapM toMirValue vs
toMirValue (VData name fields) = MData name <$> mapM (\(f, v) -> (,) f <$> toMirValue v) fields
toMirValue (VFnRef name) = Just (MFn name)
toMirValue VFunct{} = Nothing
