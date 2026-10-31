module MirEval
    ( MirValue (..)
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
import Data.List (elemIndex, intercalate)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir
import TersusTypes (Name, Rel (..), Value (..), Variable)
import Utils

-- Runs the MIR: a function is its locals and the block it is in. The statements of the block run, then the
-- terminator says where to go next. The operations that need a contract the validator proved (a divisor that is not 0,
-- an index in range) still check it and report an error, so that a mistake of the validator is a failure here instead
-- of a wrong answer, as it is in the evaluator of the AST.
data MirValue
    = MInt Integer
    | MBool Bool
    | MList [MirValue]
    | MData Name [(Variable, MirValue)]
    | MFn Name
    | -- What an empty Uninit<T> holds: nothing, which no operation can read
      MEmpty
    | -- A reference to a place in the frame that runs it: the local it starts from, and the fields and indexes from
      -- there (REFERENCES.md). Reading it gives the place's current value; a call through an update reference
      -- writes the callee's final value back into the place.
      MRef Local [EvalStep]
    deriving (Eq, Show)

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
runProgramEnv env program =
    mapResult
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
    }

-- The memory of an allocation: its slots, each holding a value or nothing (POINTERS.md). An address is a number: allocation k starts at
-- k * 2^32 and a slot is one more than the slot before it, so that `Addr::offset` is a sum, `Addr::toInt` is the number (which is not the
-- one native code has) and the null address, 0, is in no allocation. A read of an empty slot, a write over a filled one, a use of memory
-- that was freed or never allocated, and a free of memory that still holds a value are errors: a proved program does none of them, so
-- this is a check of what a program assumes (Block::assume).
data Allocation = Allocation {allocSize :: Integer, allocSlots :: Map Integer MirValue}

startState :: String -> S
startState input = S{sInput = input, sPath = "", sLoaded = "", sStore = "", sFiles = Map.empty, sOrder = [], sHeap = Map.empty, sNextAllocation = 1}

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
writeSlot address v = heapE $ \s ->
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
    | otherwise = runBlock program fn (BlockId 0) (Map.union extra (Map.fromList (zip (fnParams fn) args)))

type Frame = Map Local MirValue

runBlock :: Program -> Function -> BlockId -> Frame -> E (Maybe MirValue, Frame)
runBlock program fn block frame =
    case Map.lookup block (fnBlocks fn) of
        Nothing -> failE ("Jump to a block that does not exist: " ++ show block)
        Just (BasicBlock stmts term) -> do
            frame' <- runStatements frame stmts
            case term of
                Goto next -> runBlock program fn next frame'
                SwitchBool test yes no -> do
                    v <- liftE (operandValue frame' test)
                    case v of
                        MBool True -> runBlock program fn yes frame'
                        MBool False -> runBlock program fn no frame'
                        _ -> failE "Condition must be a boolean"
                Call callee args dest next -> do
                    f <- liftE (operandValue frame' callee)
                    argValues <- liftE (mapResults (operandValue frame') args)
                    resolved <- liftE (mapResults (resolveRef frame') argValues)
                    let normArgs = map (normaliseRefs frame') resolved
                        synthRoots = refRootClosure frame' normArgs
                        synthMap = Map.fromList (zip synthRoots [Local (1000000 + i) | i <- [0 ..]])
                        calleeArgs = map (rewriteRefRoots synthMap) normArgs
                        synthFrame = Map.fromList [(synth, rewriteRefRoots synthMap (normaliseRefs frame' v)) | (root, synth) <- Map.toList synthMap, Just v <- [Map.lookup root frame']]
                    (result, calleeFrame) <- callFunction program f calleeArgs synthFrame
                    -- (a result that is a reference, or holds them in its fields, is to a place of an argument:
                    -- the same place in this frame. References to the callee's own places cannot be returned,
                    -- which the checker has already refused.)
                    result' <- liftE $ case f of
                        MFn name | Just callee <- Map.lookup name (progFunctions program) -> rebaseRefs program callee calleeFrame args frame' result
                        _ -> Ok result
                    let finalParams = case f of
                            MFn name | Just callee <- Map.lookup name (progFunctions program) -> [Map.findWithDefault MEmpty p calleeFrame | p <- fnParams callee]
                            _ -> []
                    frame'' <- liftE (writeBack program frame' f args finalParams)
                    let invSynth = Map.fromList [(s, r) | (r, s) <- Map.toList synthMap]
                        result2 = rewriteRefRoots invSynth result'
                    frame3 <- liftE (foldl (\acc (root, synth) -> acc `bindResult` \fr -> case Map.lookup synth calleeFrame of Just v -> writePlace fr root [] (rewriteRefRoots invSynth v); Nothing -> Ok fr) (Ok frame'') (Map.toList synthMap))
                    runBlock program fn next (Map.insert dest result2 frame3)
                Return -> return (Map.lookup (Local 0) frame', frame')
                Unreachable -> failE "Function did not return a value"

-- What a reference stands for here: the value at the place it is to
resolveRef :: Frame -> MirValue -> Result MirValue String
resolveRef frame (MRef l steps) = readPlace frame l steps
resolveRef _ v = Ok v

readPlace :: Frame -> Local -> [EvalStep] -> Result MirValue String
readPlace frame l steps = case Map.lookup l frame of
    Nothing -> Error ("Undefined variable: " ++ show l)
    Just base -> readSteps base steps
  where
    readSteps (MRef l' steps') rest = readPlace frame l' (steps' ++ rest)
    readSteps v [] = Ok v
    readSteps (MData _ fields) (EvalField field : rest) = maybe (Error ("A reference is to a field that is not there: " ++ field)) (\v -> readSteps v rest) (lookup field fields)
    readSteps (MList xs) (EvalIndex i : rest)
        | i >= 0 && i < toInteger (length xs) = readSteps (xs !! fromInteger i) rest
        | otherwise = Error "A reference is to an index that is not there"
    readSteps _ _ = Error "A reference is to a place that is not there"

writePlace :: Frame -> Local -> [EvalStep] -> MirValue -> Result Frame String
writePlace frame l steps value = case Map.lookup l frame of
    Nothing -> Error ("Undefined variable: " ++ show l)
    Just (MRef l' steps') -> writePlace frame l' (steps' ++ steps) value
    Just base -> mapResult (\new -> Map.insert l new frame) (setSteps base steps value)
  where
    setSteps _ [] new = Ok new
    setSteps (MData name fields) (EvalField field : rest) new = case lookup field fields of
        Nothing -> Error ("A reference is to a field that is not there: " ++ field)
        Just old -> mapResult (\changed -> MData name [(f, if f == field then changed else v) | (f, v) <- fields]) (setSteps old rest new)
    setSteps (MList xs) (EvalIndex i : rest) new
        | i >= 0 && i < toInteger (length xs) = mapResult (\changed -> MList [if toInteger j == i then changed else x | (j, x) <- zip [0 ..] xs]) (setSteps (xs !! fromInteger i) rest new)
        | otherwise = Error "A reference is to an index that is not there"
    setSteps _ _ _ = Error "A reference is to a place that is not there"

-- A value that comes back from a call, with each reference in it made to name its place in the caller's
-- frame: a reference in the callee was to a local there, which was itself a reference or a parameter, and a
-- parameter's place is the place its argument is to here
rebaseRefs :: Program -> Function -> Frame -> [Operand] -> Frame -> MirValue -> Result MirValue String
rebaseRefs program callee calleeFrame args callerFrame value = case value of
    MRef l steps -> placeOf l steps
    MData name fields -> mapResult (MData name) (mapEach field fields)
      where
        field (f, v) = mapResult (\v' -> (f, v')) (rebaseRefs program callee calleeFrame args callerFrame v)
    MList values -> mapResult MList (mapEach (rebaseRefs program callee calleeFrame args callerFrame) values)
    _ -> Ok value
  where
    mapEach _ [] = Ok []
    mapEach g (x : xs) = g x `bindResult` \y -> mapResult (y :) (mapEach g xs)
    placeOf l steps = case Map.lookup l calleeFrame of
        Just (MRef l2 steps2) -> placeOf l2 (steps2 ++ steps)
        _ -> case elemIndex l (fnParams callee) of
            Just i | i < length args -> case args !! i of
                Copy cl -> Ok (case Map.lookup cl callerFrame of
                    Just (MRef rl rs) -> MRef rl (rs ++ steps)
                    _ -> MRef cl steps)
                Move cl -> Ok (case Map.lookup cl callerFrame of
                    Just (MRef rl rs) -> MRef rl (rs ++ steps)
                    _ -> MRef cl steps)
                _ -> Ok value
            _ -> Ok value

-- After a call, the final value of each update parameter is written back into the place its argument was to
writeBack :: Program -> Frame -> MirValue -> [Operand] -> [MirValue] -> Result Frame String
writeBack program frame (MFn name) args finalParams = case Map.lookup name (progFunctions program) of
    Nothing -> Ok frame
    Just fn ->
        let muts = [i | (i, param) <- zip [0 ..] (fnParams fn), Just (LocalDecl _ (Just n)) <- [Map.lookup param (fnLocals fn)], n `elem` specMutParams (fnSpec fn)]
            write (f, i) = case (args !! i, finalParams !! i) of
                (Copy l, v) -> placeOf f l v
                (Move l, v) -> placeOf f l v
                _ -> Ok f
            placeOf f l v = case Map.lookup l f of
                Just (MRef root steps) -> writePlace f root steps v
                _ -> writePlace f l [] v
         in foldl (\acc i -> acc `bindResult` \f -> write (f, i)) (Ok frame) muts
writeBack _ frame _ _ _ = Ok frame

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
        _ -> MRef l steps
    MData name fields -> MData name [(f, normaliseRefs frame v) | (f, v) <- fields]
    MList values -> MList (map (normaliseRefs frame) values)
    _ -> value

refRoots :: MirValue -> [Local]
refRoots value = case value of
    MRef l _ -> [l]
    MData _ fields -> concatMap (refRoots . snd) fields
    MList values -> concatMap refRoots values
    _ -> []

refRootClosure :: Frame -> [MirValue] -> [Local]
refRootClosure frame args = go [] (concatMap refRoots args)
  where
    go seen [] = seen
    go seen (r : rest)
        | r `elem` seen = go seen rest
        | otherwise = go (seen ++ [r]) (rest ++ maybe [] (refRoots . normaliseRefs frame) (Map.lookup r frame))

rewriteRefRoots :: Map Local Local -> MirValue -> MirValue
rewriteRefRoots m value = case value of
    MRef l steps -> MRef (Map.findWithDefault l l m) steps
    MData name fields -> MData name [(f, rewriteRefRoots m v) | (f, v) <- fields]
    MList values -> MList (map (rewriteRefRoots m) values)
    _ -> value

mapResults :: (a -> Result b String) -> [a] -> Result [b] String
mapResults = flatResultMap

runStatements :: Frame -> [Statement] -> E Frame
runStatements frame [] = return frame
runStatements frame (Ghost{} : rest) = runStatements frame rest
runStatements frame (Drop{} : rest) = runStatements frame rest
runStatements frame (Peek dest rv : rest) = runStatements frame (Assign dest rv : rest)
runStatements frame (Assign dest (ListOp PathByte [b]) : rest) = intArgument frame b >>= \x -> pathByte x >>= \n -> runStatements (Map.insert dest (MInt n) frame) rest
runStatements frame (Assign dest (ListOp FileLoad []) : rest) = fileLoad >>= \n -> runStatements (Map.insert dest (MInt n) frame) rest
runStatements frame (Assign dest (ListOp FileByte [i]) : rest) = intArgument frame i >>= \x -> fileByteAt x >>= \n -> runStatements (Map.insert dest (MInt n) frame) rest
runStatements frame (Assign dest (ListOp StoreByte [b]) : rest) = intArgument frame b >>= \x -> storeByte x >>= \n -> runStatements (Map.insert dest (MInt n) frame) rest
runStatements frame (Assign dest (ListOp FileStore []) : rest) = fileStore >>= \n -> runStatements (Map.insert dest (MInt n) frame) rest
runStatements frame (Assign dest (ListOp ArgCount []) : rest) = do
    args <- arguments
    runStatements (Map.insert dest (MInt (toInteger (length args))) frame) rest
runStatements frame (Assign dest (ListOp ArgByte [i, j]) : rest) = do
    args <- arguments
    iv <- liftE (operandValue frame i)
    jv <- liftE (operandValue frame j)
    let byte = case (iv, jv) of
            (MInt a, MInt b)
                | a >= 0 && a < toInteger (length args) && b >= 0 && b < toInteger (length (args !! fromInteger a)) -> toInteger (fromEnum (args !! fromInteger a !! fromInteger b) `mod` 256)
            _ -> -1
    runStatements (Map.insert dest (MInt byte) frame) rest
runStatements frame (Assign dest (ListOp ReadByte []) : rest) = do
    b <- readInput
    runStatements (Map.insert dest (MInt b) frame) rest
runStatements frame (Assign dest (ListOp WriteByte [o]) : rest) = do
    v <- liftE (operandValue frame o)
    case v of
        MInt b -> write (chr (fromIntegral (b `mod` 256))) >> runStatements (Map.insert dest v frame) rest
        _ -> failE "writeByte takes an Int"
runStatements frame (Assign dest (ListOp WriteError [o]) : rest) = do
    v <- liftE (operandValue frame o)
    case v of
        MInt b -> writeError (chr (fromIntegral (b `mod` 256))) >> runStatements (Map.insert dest v frame) rest
        _ -> failE "writeError takes an Int"
runStatements frame (Assign dest (ListOp op os) : rest) | Just run <- memoryOp op = do
    args <- mapM (intOrValue frame) os
    v <- run args
    runStatements (Map.insert dest v frame) rest
runStatements frame (AssignRef root steps rv : rest) = do
    v <- liftE (evalRvalue frame rv)
    evalSteps <- liftE (mapResults (evalRefStep frame) steps)
    frame' <- liftE (writePlace frame root evalSteps v)
    runStatements frame' rest
runStatements frame (Assign dest rv : rest) = do
    v <- liftE (evalRvalue frame rv)
    runStatements (Map.insert dest v frame) rest

intOrValue :: Frame -> Operand -> E MirValue
intOrValue frame o = liftE (operandValue frame o)

-- The operations on memory, which change the heap (the permissions they were given are erased by the ghost erasure)
memoryOp :: ListOp -> Maybe ([MirValue] -> E MirValue)
memoryOp op = case op of
    AddrAlloc -> Just (\args -> case args of
        [MInt n] -> MInt <$> allocate n
        _ -> bad)
    AddrGet -> Just (\args -> case args of
        [MInt p, MInt i] -> readSlot False (p + i)
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

evalRefStep :: Frame -> RefStep -> Result EvalStep String
evalRefStep _ (RefField _ field) = Ok (EvalField field)
evalRefStep frame (RefIndex o) = operandValue frame o `bindResult` \v -> case v of
    MInt i -> Ok (EvalIndex i)
    _ -> Error "The index of a borrowed place is not an Int"

-- The Int that an operand is
intArgument :: Frame -> Operand -> E Integer
intArgument frame o = do
    v <- liftE (operandValue frame o)
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

evalRvalue :: Frame -> Rvalue -> Result MirValue String
evalRvalue frame rv =
    case rv of
        Use o -> operandValue frame o
        Borrow root steps _ -> MRef root <$$> mapResults evalStep steps
        Deref o -> operandValue frame o `bindResult` resolveRef frame
        BinaryOp op a b -> operandValue frame a `bindResult` \x -> operandValue frame b `bindResult` \y -> binary op x y
        ListOp op os -> mapResults (\o -> operandValue frame o `bindResult` resolveRef frame) os `bindResult` listOp op
        MakeList os -> MList <$$> mapResults (operandValue frame) os
        MakeBox o -> operandValue frame o
        Unbox o -> operandValue frame o
        Unsize o -> operandValue frame o
        MakeData name fields -> MData (plain name) <$$> mapResults (\(f, o) -> (,) f <$$> operandValue frame o) fields
        ReadField o name field ->
            operandValue frame o `bindResult` \v -> case v of
                MData actual fields
                    | actual /= plain name -> Error ("Expected a " ++ name ++ " but got a " ++ actual)
                    | otherwise -> maybe (Error ("Variant " ++ name ++ " has no field " ++ field)) Ok (lookup field fields)
                _ -> Error "A field can only be read from a struct"
        -- (a wrong cast is undefined behaviour, as in the evaluator of the AST: reading a field that is not there is the error)
        AsVariant o _ -> operandValue frame o
        Clone o -> operandValue frame o
        TakeField l name field -> evalRvalue frame (ReadField (Copy l) name field)
        IsVariant o name ->
            operandValue frame o `bindResult` \v -> case v of
                MData actual _ -> Ok (MBool (actual == plain name))
                _ -> Error "Is only tests the variant of an enum value"
  where
    f <$$> r = mapResult f r
    evalStep = evalRefStep frame

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
listOp Length [MList l] = Ok (MInt (fromIntegral (length l)))
listOp First [MList []] = Error "First requires a non-empty list"
listOp First [MList l] = Ok (head l)
listOp Last [MList []] = Error "Last requires a non-empty list"
listOp Last [MList l] = Ok (last l)
listOp Get [MList l, MInt i]
    | i < 0 || i >= fromIntegral (length l) = Error "Get index out of range"
    | otherwise = Ok (l !! fromIntegral i)
listOp Push [MList l, x] = Ok (MList (l ++ [x]))
listOp Pop [MList []] = Error "Pop requires a non-empty list"
listOp Pop [MList l] = Ok (MList (init l))
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
listOp NewEmptyBoxed [] = Ok (MList [])
listOp NewArray [MInt n, x]
    | n < 0 = Error "array needs a size that is not negative"
    | otherwise = Ok (MList (replicate (fromIntegral n) x))
listOp Set [MList l, MInt i, x]
    | i < 0 || i >= fromIntegral (length l) = Error "Set index out of range"
    | otherwise = let (before, after) = splitAt (fromIntegral i) l in Ok (MList (before ++ x : drop 1 after))
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

-- The value of the AST that a value of the MIR is, and the other way: a function of the program is VFnRef, and no function
-- written in the AST is a value of the MIR
fromMirValue :: MirValue -> Value
fromMirValue (MInt i) = VInt i
fromMirValue (MBool b) = VBool b
fromMirValue (MList vs) = VList (map fromMirValue vs)
fromMirValue (MData name fields) = VData name [(f, fromMirValue v) | (f, v) <- fields]
fromMirValue (MFn name) = VFnRef name
fromMirValue MEmpty = VData "<empty>" []

toMirValue :: Value -> Maybe MirValue
toMirValue (VInt i) = Just (MInt i)
toMirValue (VBool b) = Just (MBool b)
toMirValue (VList vs) = MList <$> mapM toMirValue vs
toMirValue (VData name fields) = MData name <$> mapM (\(f, v) -> (,) f <$> toMirValue v) fields
toMirValue (VFnRef name) = Just (MFn name)
toMirValue VFunct{} = Nothing
