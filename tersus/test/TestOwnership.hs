module TestOwnership
    ( testOwnership
    , runOwned
    ) where

import Data.List (isInfixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir
import MirEval (MirValue (..), runProgram)
import MirOwnership (insertOwnership, needsDrop)
import MirVerify (verifyProgram)
import MirLower (lowerProgram)
import Parse (parseStatementBlock)
import Pipeline
import TestNative (nativeExamples, unvalidatedPrograms, validatedPrograms)
import TersusTypes (Name, Rel (..), Size (..), Type (..), Variable)
import TestHarness
import Utils

-- Ownership: MirOwnership says who owns each value of the heap, and native code frees values and changes lists in place on
-- the strength of it. A wrong answer here is a value used after it was freed, freed twice, or changed under a reader, which
-- the executor of the MIR cannot show, so these tests run the result on a model of the heap that fails on all of those, and
-- on a value that is still there when the program ends.

-- The model of the heap

-- (a struct or an enum value, held inline, is its fields; VP is the address of a value of the heap: a list, or a Box)
data Val = VI Integer | VB Bool | VP Int | VNull | VF Name | VS Name [(Variable, Val)]
    deriving (Eq, Show)

-- (OMem is the memory of Addr::alloc: the slots that hold a value, of so many; an address is the number of the cell times 2^32 and the slot)
data Obj = OList [Val] | OBox Val | OMem (Map Integer Val) Integer

data Cell = Cell {cellGeneration :: Int, cellObject :: Obj}

-- What a local holds, and for a local that only looks at a value, which one and how it was when it looked
data Slot = Slot {slotValue :: Val, slotLook :: Maybe [(Int, Int)]}

data Frame = Frame {frameFunction :: Function, frameSlots :: Map Local Slot}

data St = St
    { stHeap :: Map Int Cell
    , stNext :: Int
    , stFrames :: [Frame]
    , stFuel :: Int
    , stProgram :: Program
    }

newtype M a = M {runM :: St -> Either String (a, St)}

instance Functor M where
    fmap f (M g) = M (\s -> fmap (\(a, s') -> (f a, s')) (g s))

instance Applicative M where
    pure a = M (\s -> Right (a, s))
    M f <*> M g = M (\s -> f s >>= \(h, s') -> fmap (\(a, s'') -> (h a, s'')) (g s'))

instance Monad M where
    M g >>= f = M (\s -> g s >>= \(a, s') -> runM (f a) s')

failM :: String -> M a
failM e = M (\_ -> Left e)

getSt :: M St
getSt = M (\s -> Right (s, s))

putSt :: St -> M ()
putSt s = M (\_ -> Right ((), s))

tick :: M ()
tick = do
    s <- getSt
    if stFuel s <= 0 then failM "out of fuel" else putSt s{stFuel = stFuel s - 1}

alloc :: Obj -> M Val
alloc obj = do
    s <- getSt
    putSt s{stHeap = Map.insert (stNext s) (Cell 0 obj) (stHeap s), stNext = stNext s + 1}
    return (VP (stNext s))

cell :: Int -> M Cell
cell a = do
    s <- getSt
    maybe (failM ("use of freed memory at " ++ show a)) return (Map.lookup a (stHeap s))

setObject :: Int -> Obj -> M ()
setObject a obj = do
    c <- cell a
    s <- getSt
    putSt s{stHeap = Map.insert a (Cell (cellGeneration c + 1) obj) (stHeap s)}

-- Frees a value and what is in it
freeTree :: Val -> M ()
freeTree (VP a) = do
    s <- getSt
    case Map.lookup a (stHeap s) of
        Nothing -> failM ("double free of " ++ show a)
        Just c -> do
            putSt s{stHeap = Map.delete a (stHeap s)}
            mapM_ freeTree (children (cellObject c))
-- (a value of a type with a drop is given to its drop first, which frees what it holds by hand, and its fields are freed after)
freeTree v@(VS name fs) = do
    program <- stProgram <$> getSt
    case typeOfValue program name >>= dropFunction program >>= (`Map.lookup` progFunctions program) of
        Just fn -> callFunction program fn [v] >> return ()
        Nothing -> return ()
    mapM_ (freeTree . snd) fs
freeTree _ = return ()

-- The struct or the enum that a value of a struct or of a variant is of
typeOfValue :: Program -> Name -> Maybe Name
typeOfValue program name = case Map.lookup name (progTypes program) of
    Just StructDecl{} -> Just name
    _ -> case [n | (n, EnumDecl variants) <- Map.toList (progTypes program), name `elem` map fst variants] of
        n : _ -> Just n
        [] -> Nothing

-- The memory that a list of native code (a StdList, on an address) has its elements in
listCell :: [(Variable, Val)] -> Maybe Int
listCell fs = case lookup "addr" fs of
    Just (VI address) | address > 0 -> Just (fromInteger (address `div` (2 ^ (32 :: Integer))))
    _ -> Nothing

children :: Obj -> [Val]
children (OList vs) = vs
children (OBox v) = [v]
children (OMem slots _) = Map.elems slots

-- The values of the heap that a value holds, inline or not
pointersOf :: Val -> [Int]
pointersOf (VP a) = [a]
pointersOf (VS name fs) | isListStruct name || isBoxStruct name, Just a <- listCell fs = [a]
pointersOf (VS _ fs) = concatMap (pointersOf . snd) fs
pointersOf _ = []

cloneVal :: Val -> M Val
cloneVal (VP a) = do
    c <- cell a
    case cellObject c of
        OList vs -> mapM cloneVal vs >>= alloc . OList
        OBox v -> cloneVal v >>= alloc . OBox
        OMem _ _ -> failM "memory is copied"
-- (a copy of a list has memory of its own, with copies of the elements in use)
cloneVal (VS name fs) | isListStruct name, Just a <- listCell fs = do
    c <- cell a
    used <- case lookup "len" fs of
        Just (VI n) -> return n
        _ -> failM "a list without its length"
    case cellObject c of
        OMem slots _ -> do
            copies <- mapM (\(k, v) -> (,) k <$> cloneVal v) [(k, v) | (k, v) <- Map.toList slots, k < used]
            copy <- alloc (OMem (Map.fromList copies) used)
            case copy of
                VP b -> return (VS name [(f, if f == "addr" then VI (toInteger b * 2 ^ (32 :: Integer)) else if f == "cap" then VI used else v) | (f, v) <- fs])
                _ -> failM "an allocation is not on the heap"
        _ -> failM "a list that is not in memory"
-- (a copy of a Box of the library has room of its own, with a copy of the value)
cloneVal (VS name fs) | isBoxStruct name, Just a <- listCell fs = do
    c <- cell a
    case cellObject c of
        OMem slots size -> do
            copies <- mapM (\(k, v) -> (,) k <$> cloneVal v) (Map.toList slots)
            copy <- alloc (OMem (Map.fromList copies) size)
            case copy of
                VP b -> return (VS name [(f, if f == "addr" then VI (toInteger b * 2 ^ (32 :: Integer)) else v) | (f, v) <- fs])
                _ -> failM "an allocation is not on the heap"
        _ -> failM "a Box that is not in memory"
cloneVal (VS name fs) = VS name <$> mapM (\(f, v) -> (,) f <$> cloneVal v) fs
cloneVal v = return v

-- How many places own the value: locals (not those that only look) and slots of values
owners :: Int -> M Int
owners a = do
    s <- getSt
    let fromFrames = length [() | f <- stFrames s, Slot v Nothing <- Map.elems (frameSlots f), b <- pointersOf v, b == a]
        fromHeap = length [() | c <- Map.elems (stHeap s), v <- children (cellObject c), b <- pointersOf v, b == a]
    return (fromFrames + fromHeap)

currentFrame :: M Frame
currentFrame = do
    s <- getSt
    case stFrames s of
        f : _ -> return f
        [] -> failM "no frame"

putSlot :: Local -> Slot -> M ()
putSlot l slot = do
    s <- getSt
    case stFrames s of
        f : rest -> putSt s{stFrames = f{frameSlots = Map.insert l slot (frameSlots f)} : rest}
        [] -> failM "no frame"

-- Whether a local owns what it holds
localHeap :: Program -> Frame -> Local -> Bool
localHeap program f l = maybe False (needsDrop program . localType) (Map.lookup l (fnLocals (frameFunction f)))

-- Reading a local: it has to hold something, that has to be there, and be as it was when a local that only looks saw it
readLocal :: Local -> M Val
readLocal l = do
    f <- currentFrame
    case Map.lookup l (frameSlots f) of
        Nothing -> failM ("read of " ++ show l ++ " before it is given a value")
        Just (Slot VNull _) -> failM ("use of " ++ show l ++ " after it was moved from")
        Just (Slot v look) -> do
            -- (a local that only looks at a value sees it as it was when it looked)
            mapM_
                ( \(a, g) -> do
                    c <- cell a
                    if g /= cellGeneration c then failM (show l ++ " looks at a value that changed") else return ()
                )
                (maybe [] id look)
            return v

readOperand :: Operand -> M Val
readOperand (Copy l) = readLocal l
readOperand (Move l) = do
    v <- readLocal l
    f <- currentFrame
    case Map.lookup l (frameSlots f) of
        Just (Slot _ (Just _)) -> failM (show l ++ " only looks at a value, and is moved from")
        _ -> return ()
    putSlot l (Slot VNull Nothing)
    return v
readOperand (Const c) = constant c

constant :: Constant -> M Val
constant (CInt i) = return (VI i)
constant (CBool b) = return (VB b)
constant (CList cs) = mapM constant cs >>= alloc . OList
constant (CData name fs) = VS name <$> mapM (\(f, c) -> (,) f <$> constant c) fs
constant (CFn name) = return (VF name)

-- The values compared and shown
data Pure = PI Integer | PB Bool | PL [Pure] | PD Name [(Variable, Pure)] | PF Name
    deriving (Eq, Show)

toPure :: Val -> M Pure
toPure (VI i) = return (PI i)
toPure (VB b) = return (PB b)
toPure (VF n) = return (PF n)
toPure VNull = failM "a value that was moved from is compared"
toPure (VP a) = do
    c <- cell a
    case cellObject c of
        OList vs -> PL <$> mapM toPure vs
        OBox v -> toPure v
        OMem _ _ -> failM "memory is compared"
-- (a list of native code is the elements in use of the array it holds)
toPure (VS name fs)
    | isListStruct name, Just a <- listCell fs, Just (VI used) <- lookup "len" fs = do
        (_, obj) <- object (VP a)
        PL <$> mapM toPure (take (fromIntegral used) (children obj))
    -- (a Box of the library is the value it holds)
    | isBoxStruct name, Just a <- listCell fs = do
        (_, obj) <- object (VP a)
        case children obj of
            [v] -> toPure v
            _ -> failM "a Box that does not hold one value"
    | otherwise = PD name <$> mapM (\(f, v) -> (,) f <$> toPure v) fs

fromPure :: Pure -> MirValue
fromPure (PI i) = MInt i
fromPure (PB b) = MBool b
fromPure (PL ps) = MList (map fromPure ps)
fromPure (PD name fs) = MData name [(f, fromPure p) | (f, p) <- fs]
fromPure (PF n) = MFn n

object :: Val -> M (Int, Obj)
object (VP a) = do
    c <- cell a
    return (a, cellObject c)
-- (a list of native code is read where its elements are: the first field of the struct StdList is the Box of the array that holds them)
object (VS name fs) | isListStruct name, Just a <- listCell fs = object (VP a)
object v = failM ("not a value of the heap: " ++ show v)

isListStruct :: Name -> Bool
isListStruct name = takeWhile (/= '<') name == "StdList"

isBoxStruct :: Name -> Bool
isBoxStruct name = takeWhile (/= '<') name == "StdBox"

-- The fields of a struct or an enum value that a value is: held inline, or in a Box
dataValue :: Val -> M (Name, [(Variable, Val)])
dataValue (VS name fs) = return (name, fs)
dataValue v@(VP _) = do
    (_, obj) <- object v
    case obj of
        OBox inner -> dataValue inner
        _ -> failM "a field of a list"
dataValue v = failM ("not a struct or an enum: " ++ show v)

-- (a Box of the library is looked into, for a read of what it holds and not of its own field: what it holds is in the one slot at its address)
throughBox :: Name -> Val -> M Val
throughBox name v = case v of
    VS boxName fs | isBoxStruct boxName, boxName /= name, Just a <- listCell fs -> boxed a
    _ -> return v

-- The value in the slot of a Box of the library
boxed :: Int -> M Val
boxed a = do
    c <- cell a
    case cellObject c of
        OMem slots _ | Just v <- Map.lookup 0 slots -> return v
        _ -> failM "a Box of the library that holds nothing"

-- The value in a Box, taken out of it: the room of the Box is freed, and not what it held
unbox :: Val -> M Val
unbox v = do
    (a, obj) <- object v
    case obj of
        OBox inner -> do
            s <- getSt
            putSt s{stHeap = Map.delete a (stHeap s)}
            return inner
        _ -> failM "unbox of a list"

-- Running the MIR

evalRvalue :: Rvalue -> M Val
evalRvalue rv =
    case rv of
        Use o -> readOperand o
        MakeBox o -> readOperand o >>= alloc . OBox
        Unbox o -> readOperand o >>= unbox
        BinaryOp op a b -> do
            x <- readOperand a
            y <- readOperand b
            binary op x y
        MakeList os -> mapM readOperand os >>= alloc . OList
        MakeData name fs -> VS name <$> mapM (\(f, o) -> (,) f <$> readOperand o) fs
        ReadField o name field -> do
            (actual, fs) <- readOperand o >>= throughBox name >>= dataValue
            if actual == name then maybe (failM ("no field " ++ field)) return (lookup field fs) else failM ("expected a " ++ name ++ ", got a " ++ actual)
        IsVariant o name -> do
            (actual, _) <- readOperand o >>= throughBox name >>= dataValue
            return (VB (actual == name))
        -- (a Box that is cast is taken out of its room when the cast takes it, and is looked into when it does not)
        AsVariant o _ -> do
            v <- readOperand o
            case (v, o) of
                (VP _, Move _) -> unbox v
                (VP _, _) -> dataValueOf v
                -- (and so is a Box of the library)
                (VS name fs, Move _) | isBoxStruct name, Just a <- listCell fs -> do
                    inner <- boxed a
                    s <- getSt
                    putSt s{stHeap = Map.delete a (stHeap s)}
                    return inner
                (VS name fs, _) | isBoxStruct name, Just a <- listCell fs -> boxed a
                _ -> return v
        Clone o -> readOperand o >>= cloneVal
        TakeField l name field -> do
            f <- currentFrame
            case Map.lookup l (frameSlots f) of
                Just (Slot _ (Just _)) -> failM ("a field is taken from " ++ show l ++ ", which only looks")
                _ -> return ()
            v <- readLocal l
            case v of
                VS boxName boxFs | isBoxStruct boxName, Just a <- listCell boxFs -> do
                    c <- cell a
                    case cellObject c of
                        OMem slots size | Just (VS actual fs) <- Map.lookup 0 slots -> do
                            (taken, fs') <- takeFrom actual fs
                            setObject a (OMem (Map.insert 0 (VS actual fs') slots) size)
                            return taken
                        _ -> failM "a field of a Box of the library that holds nothing"
                VS actual fs -> do
                    (taken, fs') <- takeFrom actual fs
                    putSlot l (Slot (VS actual fs') Nothing)
                    return taken
                VP a -> do
                    (_, obj) <- object v
                    case obj of
                        OBox (VS actual fs) -> do
                            (taken, fs') <- takeFrom actual fs
                            setObject a (OBox (VS actual fs'))
                            return taken
                        _ -> failM "a field of a list"
                _ -> failM ("a field taken from " ++ show v)
          where
            takeFrom actual fs
                | actual /= name = failM ("expected a " ++ name ++ ", got a " ++ actual)
                | otherwise = case lookup field fs of
                    Nothing -> failM ("no field " ++ field)
                    Just VNull -> failM ("field " ++ field ++ " was taken twice")
                    Just v' -> return (v', [(g, if g == field then VNull else w) | (g, w) <- fs])
        ListOp op os -> listOp op os
  where
    dataValueOf v = do
        (name, fs) <- dataValue v
        return (VS name fs)

intOperand :: Operand -> M Integer
intOperand o = do
    v <- readOperand o
    case v of
        VI n -> return n
        _ -> failM "not an Int"

listOp :: ListOp -> [Operand] -> M Val
listOp op os =
    case (op, os) of
        (Length, [l]) -> do
            (_, obj) <- readOperand l >>= object
            return (VI (fromIntegral (length (children obj))))
        -- (n copies of the element, in room of their own on the heap, as an array in a Box)
        (NewBoxed, [n, x]) -> do
            count <- intOperand n
            v <- readOperand x
            copies <- mapM (const (cloneVal v)) [1 .. count]
            alloc (OList copies)
        (NewEmptyBoxed, []) -> alloc (OList [])
        (WriteByte, [b]) -> VI . fromIntegral <$> intOperand b
        (WriteError, [b]) -> VI . fromIntegral <$> intOperand b
        (ReadByte, []) -> pure (VI (-1))
        (ArgCount, []) -> pure (VI 0)
        (ArgByte, [_, _]) -> pure (VI (-1))
        (PathByte, [_]) -> pure (VI 0)
        (FileLoad, []) -> pure (VI (-1))
        (FileByte, [_]) -> pure (VI (-1))
        (StoreByte, [_]) -> pure (VI 0)
        (FileStore, []) -> pure (VI (-1))
        (ToByte, [x]) -> VI . fromIntegral <$> intOperand x
        (FromByte, [b]) -> VI . fromIntegral <$> intOperand b
        (First, [l]) -> item l (const 0)
        (Last, [l]) -> item l (\n -> n - 1)
        (Get, [l, i]) -> do
            n <- intOperand i
            item l (const (fromIntegral n))
        (Push, [l, x]) -> do
            list <- readOperand l
            v <- readOperand x
            (a, obj) <- object list
            inPlace a
            setObject a (OList (children obj ++ [v]))
            return list
        (Set, [l, i, x]) -> do
            list <- readOperand l
            n <- fromIntegral <$> intOperand i
            v <- readOperand x
            (a, obj) <- object list
            inPlace a
            let vs = children obj
            if n < 0 || n >= length vs
                then failM "Set index out of range"
                else do
                    freeTree (vs !! n)
                    setObject a (OList (take n vs ++ [v] ++ drop (n + 1) vs))
                    return list
        -- (the operations on memory, whose permissions are erased: what is in the slots is owned by the memory, and freeing it with a
        -- value left is a leak, which the check at the end finds)
        (AddrNull, []) -> pure (VI 0)
        (AddrOffset, [p, i]) -> (\a b -> VI (a + b)) <$> intOperand p <*> intOperand i
        (AddrCast, [p]) -> readOperand p
        (AddrToInt, [p]) -> readOperand p
        (AddrFromInt, [n]) -> readOperand n
        (AddrAlloc, [n]) -> do
            count <- intOperand n
            v <- alloc (OMem Map.empty count)
            case v of
                VP a -> pure (VI (toInteger a * memorySpan))
                _ -> failM "an allocation is not on the heap"
        (AddrGet, [p, i]) -> slotOf p i >>= \(_, slots, _, k) -> maybe (failM "a slot that holds no value is read") pure (Map.lookup k slots)
        (AddrTake, [p, i]) -> do
            (a, slots, size, k) <- slotOf p i
            v <- maybe (failM "a slot that holds no value is taken") pure (Map.lookup k slots)
            setObject a (OMem (Map.delete k slots) size)
            pure v
        (AddrWrite, [p, i, x]) -> do
            (a, slots, size, k) <- slotOf p i
            v <- readOperand x
            if Map.member k slots then failM "a value is written over a slot that holds one" else setObject a (OMem (Map.insert k v slots) size)
            pure (VI 0)
        (AddrDropValue, [p, i]) -> dropSlots p i (Const (CInt 1))
        (AddrDropRange, [p, i, n]) -> dropSlots p i n
        (AddrResize, [p, n]) -> do
            (a, slots, _, k) <- memoryOf p
            count <- intOperand n
            if k /= 0 || any (>= count) (Map.keys slots) then failM "memory is resized that is not whole, or to fewer slots than hold values" else pure ()
            s <- getSt
            putSt s{stHeap = Map.delete a (stHeap s)}
            v <- alloc (OMem slots count)
            case v of
                VP b -> pure (VI (toInteger b * memorySpan))
                _ -> failM "an allocation is not on the heap"
        (AddrFree, [p]) -> do
            (a, slots, _, k) <- memoryOf p
            if k /= 0 || not (Map.null slots) then failM "memory is freed that is not whole, or that holds a value" else pure ()
            s <- getSt
            putSt s{stHeap = Map.delete a (stHeap s)}
            pure (VI 0)
        -- (an empty Uninit is cleared bytes, which own nothing; a value taken apart is cleared so, MirGhost)
        (UninitEmpty, []) -> pure VNull
        _ -> failM ("list operation on the wrong operands: " ++ show op)
  where
    memorySpan = 2 ^ (32 :: Integer)
    memoryOf p = do
        address <- intOperand p
        let (a, k) = address `divMod` memorySpan
        c <- cell (fromInteger a)
        case cellObject c of
            OMem slots size -> pure (fromInteger a, slots, size, k)
            _ -> failM "an address that is not of memory"
    slotOf p i = do
        address <- intOperand p
        index <- intOperand i
        let (a, k) = (address + index * 1) `divMod` memorySpan
        c <- cell (fromInteger a)
        case cellObject c of
            OMem slots size | k < size -> pure (fromInteger a, slots, size, k)
            _ -> failM "an address out of its memory"
    dropSlots p i n = do
        count <- intOperand n
        index <- intOperand i
        mapM_ (\j -> do
            (a, slots, size, k) <- slotOf p (Const (CInt j))
            v <- maybe (failM "a slot that holds no value is dropped") pure (Map.lookup k slots)
            setObject a (OMem (Map.delete k slots) size)
            freeTree v) [index .. index + count - 1]
        pure (VI 0)
    item l pick = do
        (_, obj) <- readOperand l >>= object
        let vs = children obj
            i = pick (length vs)
        if i < 0 || i >= length vs then failM "index out of range" else return (vs !! i)

-- A list is changed in place only when nothing else holds it: the operand has been moved out of its local, so nothing
inPlace :: Int -> M ()
inPlace a = do
    n <- owners a
    if n == 0 then return () else failM ("a list is changed in place while " ++ show n ++ " other places hold it")

binary :: BinOp -> Val -> Val -> M Val
binary op x y =
    case (op, x, y) of
        (Add, VI a, VI b) -> int (a + b)
        (Sub, VI a, VI b) -> int (a - b)
        (Mul, VI a, VI b) -> int (a * b)
        (Div, VI _, VI 0) -> failM "Division by zero"
        (Div, VI a, VI b) -> int (a `div` b)
        (Mod, VI _, VI 0) -> failM "Modulo by zero"
        (Mod, VI a, VI b) -> return (VI (a `mod` b))
        (Compare rel, VI a, VI b) | rel `notElem` [Eq, NotEq] -> return (VB (relation rel a b))
        (Compare Eq, _, _) -> VB <$> same
        (Compare NotEq, _, _) -> VB . not <$> same
        _ -> failM "an operation on the wrong values"
  where
    int n = if inIntRange n then return (VI n) else failM "Integer overflow"
    same = (==) <$> toPure x <*> toPure y
    relation Lt = (<)
    relation Gt = (>)
    relation LtEq = (<=)
    relation GtEq = (>=)
    relation _ = (==)

execStatement :: Statement -> M ()
execStatement stmt = do
    tick
    case stmt of
        Ghost{} -> return ()
        Drop l -> do
            f <- currentFrame
            case Map.lookup l (frameSlots f) of
                Nothing -> return ()
                Just (Slot _ (Just _)) -> failM (show l ++ " only looks at a value, and is dropped")
                Just (Slot v Nothing) -> freeTree v >> putSlot l (Slot VNull Nothing)
        Peek d rv -> do
            v <- evalRvalue rv
            -- (a local that only looks remembers how what it looks at was)
            looks <- mapM (\a -> (\c -> (a, cellGeneration c)) <$> cell a) (pointersOf v)
            -- (and owns nothing, even when what it looks at holds nothing of the heap, as a value read where it is at an address;
            -- a value taken apart is cleared, and holds nothing)
            putSlot d (Slot v (if v == VNull then Nothing else Just looks))
        Assign d rv -> do
            v <- evalRvalue rv
            f <- currentFrame
            program <- stProgram <$> getSt
            if localHeap program f d
                then do
                    -- what it held is freed, and a value that is only looked at cannot be what it is given
                    case rv of
                        ListOp op _ | op `elem` [First, Last, Get] -> failM "a part of a value is assigned to a local that owns it"
                        ReadField{} -> failM "a field of a value is assigned to a local that owns it"
                        _ -> return ()
                    case Map.lookup d (frameSlots f) of
                        Just (Slot old Nothing) -> freeTree old
                        Just (Slot _ (Just _)) -> failM (show d ++ " only looks at a value, and is assigned")
                        Nothing -> return ()
                    putSlot d (Slot v Nothing)
                else putSlot d (Slot v Nothing)

-- Runs a function from its entry; what it returns is what _0 holds, moved out
callFunction :: Program -> Function -> [Val] -> M (Maybe Val)
callFunction program fn args = do
    -- (a parameter that is lent only looks at the value: the function owns nothing of it, and cannot move from it)
    -- (and remembers how it was, so that a change to it while it is lent is found)
    looks <- mapM (\(p, v) -> if p `elem` fnBorrowed fn then mapM (\a -> (\c -> (a, cellGeneration c)) <$> cell a) (pointersOf v) else return []) (zip (fnParams fn) args)
    s' <- getSt
    putSt s'{stFrames = Frame fn (Map.fromList [(p, Slot v (if p `elem` fnBorrowed fn then Just lk else Nothing)) | ((p, v), lk) <- zip (zip (fnParams fn) args) looks]) : stFrames s'}
    result <- runBlock program fn (BlockId 0)
    s' <- getSt
    case stFrames s' of
        f : rest -> do
            -- (the value a drop is given is not freed by it: its fields are freed after it)
            let dropped l = isDropFunction (fnName fn) && take 1 (fnParams fn) == [l]
                leftover = [l | (l, Slot v Nothing) <- Map.toList (frameSlots f), v /= VNull, l /= Local 0, localHeap program f l, not (dropped l)]
            if null leftover
                then putSt s'{stFrames = rest}
                else failM ("a function returns while it owns " ++ show leftover)
        [] -> failM "no frame"
    return result

runBlock :: Program -> Function -> BlockId -> M (Maybe Val)
runBlock program fn b = do
    tick
    BasicBlock stmts term <- maybe (failM ("no block " ++ show b)) return (Map.lookup b (fnBlocks fn))
    mapM_ execStatement stmts
    case term of
        Goto next -> runBlock program fn next
        SwitchBool o yes no -> do
            v <- readOperand o
            runBlock program fn (if v == VB True then yes else no)
        Unreachable -> failM "unreachable"
        Return -> do
            f <- currentFrame
            case Map.lookup (Local 0) (frameSlots f) of
                Just (Slot v Nothing) | v /= VNull -> do
                    putSlot (Local 0) (Slot VNull Nothing)
                    return (Just v)
                _ -> return Nothing
        Call callee args dest next -> do
            target <- readOperand callee
            values <- mapM readOperand args
            name <- case target of
                VF n -> return n
                _ -> failM "a call of something that is not a function"
            callee' <- maybe (failM ("no function " ++ name)) return (Map.lookup name (progFunctions program))
            result <- callFunction program callee' values
            v <- maybe (failM "a function did not return a value") return result
            f <- currentFrame
            case Map.lookup dest (frameSlots f) of
                Just (Slot old Nothing) | localHeap program f dest -> freeTree old
                _ -> return ()
            putSlot dest (Slot v Nothing)
            runBlock program fn next

-- Runs the whole program on the model, and checks that nothing is left on the heap
runOwned :: Program -> Either String (Maybe MirValue)
runOwned program =
    case runM go (St Map.empty 1 [] 1000000 program) of
        Left e -> Left e
        Right (r, _) -> Right r
  where
    go = do
        result <- callFunction program (progMain program) []
        shown <- case result of
            Nothing -> return Nothing
            Just v -> do
                p <- toPure v
                freeTree v
                return (Just (fromPure p))
        s <- getSt
        if Map.null (stHeap s) then return shown else failM ("the program ends with " ++ show (Map.size (stHeap s)) ++ " values on the heap")

-- Tests

-- The ownership pass runs on a program that is lowered, and the result checks out on the model with the answer of the executor
sameOnModel :: String -> Program -> TestResult
sameOnModel what program =
    let owned = insertOwnership (nativeProgram program)
     in case verifyProgram owned of
            Error e -> Just (what ++ ": the owned MIR is ill formed: " ++ e)
            Ok () -> case (runOwned owned, runProgram program) of
                (Right a, Ok b) -> testAssertEq a b
                (Left e, Error e') | e == e' -> Nothing
                (Left e, _) -> Just (what ++ ": " ++ e)
                (Right a, Error e) -> Just (what ++ ": the model returns " ++ show a ++ " where the executor stops with " ++ e)

-- A program lowered and run on the model, with the answer of the executor, as source
onSource :: String -> String -> TestResult
onSource name source =
    case compileSource source of
        Error e -> Just (name ++ " does not compile: " ++ e)
        Ok program -> sameOnModel name program

-- The same for a program that is lowered without being validated
onLowered :: String -> String -> TestResult
onLowered name source =
    case parseStatementBlock source of
        Left e -> Just (name ++ " does not parse: " ++ show e)
        Right stmts -> case lowerProgram stmts of
            Error e -> Just (name ++ " does not lower: " ++ e)
            Ok program -> sameOnModel name program

ownedText :: String -> Either String String
ownedText source = case ownedSource source of
    Error e -> Left e
    Ok program -> Right (renderProgram program)

count :: String -> String -> Int
count needle haystack = length [() | rest <- tails' haystack, take (length needle) rest == needle]
  where
    tails' [] = [[]]
    tails' xs@(_ : t) = xs : tails' t

-- The function of the text of a program, from its header to the closing brace
functionText :: String -> String -> String
functionText name text = unlines (takeWhile (/= "}") (dropWhile (not . isInfixOf ("fn " ++ name ++ "(")) (lines text)))

-- What the pass decides, for programs where the answer is clear
planTests :: [Test]
planTests =
    [ TestCase "a list pushed to in a loop is changed in place" . pure $
        withOwned "l = []; i = 0; while i < 4 [{ affirm i >= 0; }] shrinks 4 - i { l = push(l, i); i = i + 1; }; return size(l);" (\t -> let m = functionText "main" t in testAssertEq (count "clone" m) 0 `orElseT` testAssertTrue ("stdListPush<Int>(move _1" `isInfixOf` m))
    , -- an array is held inline and has nothing in it to free, so the pass leaves it alone (the model of the heap holds values of the
      -- heap, and the programs with arrays are not run on it)
      TestCase "an array is not owned: no copy, no move, nothing to free" . pure $
        withOwned "a = array(3, 0); b = set(a, 0, 1); return get(b, 0) + get(a, 1) + size(a);" (\t -> testAssertEq (count "clone" t, count "move" t, count "drop" t, count "peek" t) (0, 0, 0, 0))
    , TestCase "an array beside a list: only the list is freed" . pure $
        withOwned "l = [1]; a = array(2, 0); a = set(a, 1, size(l)); return get(a, 1);" (\t -> let m = functionText "main" t in testAssertEq (count "clone" m) 0 `orElseT` testAssertTrue (not ("drop _2" `isInfixOf` m) && "drop _1" `isInfixOf` m))
    , TestCase "a list that is cloned for a push is copied once" . pure $
        withOwned "x = [1]; y = push(clone(x), 2); return size(x) + size(y);" (\t -> testAssertEq (count "clone" (functionText "main" t)) 1)
    , TestCase "a match takes the fields out of the value" . pure $
        withOwned "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; fn sum(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; }; return sum(Box::new(T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Leaf) }));" (\t -> let f = functionText "sum" t in testAssertEq (count "clone" f, count "take " f) (0, 2))
    , TestCase "a part that is only read is looked at" . pure $
        withOwned "rows = [[1], [2, 3]]; return size(get(rows, 1));" (\t -> let m = functionText "main" t in testAssertEq (count "clone" m, count "peek Get" m) (0, 1))
    , TestCase "a part that is kept is copied" . pure $
        withOwned "rows = [[1], [2, 3]]; row = clone(get(rows, 1)); rows = set(rows, 0, clone(row)); return size(row);" (\t -> testAssertTrue (count "clone" (functionText "main" t) >= 1))
    , TestCase "a call with a clone of an argument that is used after it copies the argument" . pure $
        withOwned "fn n(l: List<Int>) -> Int { return size(l); }; l = [1, 2]; return n(clone(l)) + n(l);" (\t -> testAssertEq (count "clone" (functionText "main" t)) 1)
    , TestCase "a cast is read from the value itself" . pure $
        withOwned "enum S { A { r: Int }, C }; x = S::A { r: 4 }; return (x as S::A).r;" (\t -> testAssertEq (count "clone" t) 0 `orElseT` testAssertTrue (not (" as S::A;" `isInfixOf` t)))
    , TestCase "a parameter that is assigned a part is freed first" . pure $
        withOwned "fn f(row: List<Int>, rows: List<List<Int>>) -> Int [{ affirm size(rows) > 0; }] [{ }] { row = get(rows, 0); return size(row); }; return f([1], [[2, 3]]);" (\t -> let f = functionText "f" t in testAssertEq (count "peek" f, count "clone" f) (1, 1) `orElseT` testAssertTrue ("drop _1" `isInfixOf` f))
    , TestCase "a copy of a parameter is one copy" . pure $
        withOwned "fn f(a: List<Int>) -> List<Int> [{ affirm size(a) > 0; }] [{ }] { out = clone(a); out = set(out, 0, size(a)); return out; }; return f([5]);" (\t -> testAssertEq (count "clone" (functionText "f" t)) 1)
    , TestCase "a value moved on every path is not dropped at the return" . pure $
        withOwned "l = [1]; m = l; return size(m);" (\t -> let m = functionText "main" t in testAssertTrue (not ("drop _1" `isInfixOf` m) && "drop _2" `isInfixOf` m))
    , TestCase "a value moved on one path is dropped under a test of its flag" . pure $
        withOwned "l = [1, 2]; m = [0]; if size(l) = 2 { m = l; }; return size(m);" (\t -> let m = functionText "main" t in testAssertTrue (count "drop _1" m == 1 && "drop _2;" `isInfixOf` m && "const false;" `isInfixOf` m))
    , TestCase "a value that is overwritten is dropped before the assignment" . pure $
        withOwned "x = [1]; x = [1, 2]; return size(x);" (\t -> let m = functionText "main" t in testAssertEq (count "drop _1" m) 2)
    , TestCase "a field taken on one path is dropped under a test of its flag" . pure $
        withOwned "struct S { a: List<Int>, b: List<Int> }; s = S { a: [1, 2], b: [3, 4] }; n = 0; if size(s.b) = 2 { x = s.a; n = size(x); }; return n + size(s.b);" (\t -> let m = functionText "main" t in testAssertTrue ("take (_" `isInfixOf` m && "drop _" `isInfixOf` m && count "const false;" m >= 2))
    ]
  where
    withOwned source check = either Just check (ownedText source)
    orElseT Nothing b = b
    orElseT a _ = a

-- Owned MIR written by hand, with a mistake in each: the model has to see it
mistakeTests :: [Test]
mistakeTests =
    [ mistake "a value is used after it is moved" "after it was moved from"
        [Assign (Local 1) (Use (Const (CList [CInt 1]))), Assign (Local 2) (ListOp Push [Move (Local 1), Const (CInt 2)]), Assign (Local 3) (ListOp Length [Copy (Local 1)]), Drop (Local 2)]
    , mistake "a list is changed in place while it is held" "other places hold it"
        [Assign (Local 1) (Use (Const (CList [CInt 1]))), Assign (Local 2) (ListOp Push [Copy (Local 1), Const (CInt 2)]), Drop (Local 1)]
    , mistake "a value is freed twice" "double free"
        [Assign (Local 1) (Use (Const (CList [CInt 1]))), Assign (Local 2) (Use (Copy (Local 1))), Drop (Local 1), Drop (Local 2)]
    , mistake "a value is not freed" "owns"
        [Assign (Local 1) (Use (Const (CList [CInt 1])))]
    , mistake "a local that looks is used after the value is freed" "use of freed memory"
        [ Assign (Local 1) (Use (Const (CList [CList [CInt 1]])))
        , Peek (Local 5) (ListOp Get [Copy (Local 1), Const (CInt 0)])
        , Assign (Local 1) (ListOp Set [Move (Local 1), Const (CInt 0), Const (CList [CInt 2])])
        , Assign (Local 3) (ListOp Length [Copy (Local 5)])
        , Drop (Local 1)
        ]
    , mistake "a part of a value is assigned to a local that owns it" "assigned to a local that owns"
        [Assign (Local 1) (Use (Const (CList [CList [CInt 1]]))), Assign (Local 2) (ListOp Get [Copy (Local 1), Const (CInt 0)]), Drop (Local 1), Drop (Local 2)]
    ]
  where
    mistake name expected stmts =
        TestCase name . pure $ case runOwned (handMade stmts) of
            Left e -> if expected `isInfixOf` e then Nothing else Just ("expected an error with " ++ show expected ++ ", got " ++ e)
            Right _ -> Just "the model accepts it"
    handMade stmts =
        mainProgram
            [ (Local 1, onHeap)
            , (Local 2, onHeap)
            , (Local 3, TInt)
            , (Local 5, onHeap)
            ]
            stmts
    -- (the values the mistakes are made with are on the heap: a Box of an array, which the model holds as a list)
    onHeap = TBox (TArrayOf TInt SizeAny)

-- A program of a main function that is these statements and then returns nothing
mainProgram :: [(Local, Type)] -> [Statement] -> Program
mainProgram locals stmts =
    Program
        { progTypes = Map.empty
        , progFunctions = Map.empty
        , progMain =
            Function
                { fnName = "main"
                , fnParams = []
                , fnReturns = Nothing
                , fnLocals = Map.fromList [(l, LocalDecl t Nothing) | (l, t) <- locals]
                , fnBlocks = Map.singleton (BlockId 0) (BasicBlock stmts Return)
                , fnSizeParams = []
                , fnBorrowed = []
            , fnMutBorrowed = []
            , fnFrom = []
                , fnSpec = emptySpec
                }
        , progGenerics = Map.empty
        , progInvariants = Map.empty
        }

-- A part of a list that is read after the list changes is copied: the change of a list is a call, which ends the block, and a part that
-- is looked at is only looked at by the statements that follow it in its block
windowTests :: [Test]
windowTests =
    [ TestCase "a part is copied when what it is part of changes before it is read" . pure $
        let source = "rows = [[1, 2], [3]]; part = get(rows, 0); rows = set(rows, 0, [9]); return size(part);"
         in onSource "the part" source `orElseT` either Just (\t -> testAssertTrue (count "clone" (functionText "main" t) >= 1)) (ownedText source)
    , TestCase "a part is looked at when nothing changes before it is read" . pure $
        let source = "rows = [[1, 2], [3]]; n = size(get(rows, 0)); rows = set(rows, 0, [9]); return n + size(rows);"
         in onSource "the part" source `orElseT` either Just (\t -> let m = functionText "main" t in testAssertEq (count "peek Get" m, count "clone" m) (1, 0)) (ownedText source)
    ]
  where
    orElseT Nothing b = b
    orElseT a _ = a

-- The programs that have arrays are not run on the model of the heap, which holds the values of the heap (a program with arrays and
-- nothing else is checked structurally by the plan tests)
usesArrays :: String -> Bool
usesArrays source = any (`isInfixOf` source) ["Array<", "Array::", "array(", "#["]

testOwnership :: Test
testOwnership =
    TestList
        "testOwnership"
        [ TestList "examples" [TestCase path (readFile path >>= \source -> pure (if usesArrays source then Nothing else onSource path source)) | path <- nativeExamples]
        , TestList "programs" [TestCase name (pure (onSource name source)) | (name, source) <- validatedPrograms]
        , TestList "without validation" [TestCase name (pure (onLowered name source)) | (name, source) <- unvalidatedPrograms]
        , TestList "the plan" planTests
        , TestList "what a part may be read after" windowTests
        , TestList "mistakes the model finds" mistakeTests
        ]
