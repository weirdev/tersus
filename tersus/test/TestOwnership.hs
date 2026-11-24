{-# LANGUAGE PatternSynonyms #-}

module TestOwnership
    ( testOwnership
    , runOwned
    , usesArrays
    ) where

import Control.Monad (when)
import Data.List (isInfixOf, isPrefixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Mir
import MirEval (MirValue (..), runProgram)
import MirMoves (Role (..), operandLocal, roles)
import MirHousekeeping (expandRefWrites, insertOwnership, verifyProgram)
import Compile (lowerParts, parseSourceParts)
import Modules (LoadResult (..))
import Pipeline
import TestCopies (boxedClonePrograms)
import TestErgonomics (ergonomicsPrograms)
import TestNative (freshClone, lentPartPrograms, nativeExamples, ownRoleEntry, ownRoleFiles, ownRolePrograms, referenceWritePrograms, unvalidatedPrograms, validatedPrograms)
import Types (Arg (..), Name, OwnershipFacts (..), Rel (..), Size (..), Storage (..), Type (..), Variable, instanceName)
import TestStorage (pattern TList, pattern TBox)
import TestHarness
import Utils

-- Ownership: the ownership pass says who owns each value of the heap, and native code frees values and changes lists in place on
-- the strength of it. A wrong answer here is a value used after it was freed, freed twice, or changed under a reader, which
-- the executor of the MIR cannot show, so these tests run the result on a model of the heap that fails on all of those, and
-- on a value that is still there when the program ends.

-- The model of the heap

-- (a struct or an enum value, held inline, is its fields; VP is the address of a value of the heap: a list, or a Box)
data RefPath = RefFieldPath Name Variable | RefIndexPath Integer
    deriving (Eq, Show)

data Val = VI Integer | VB Bool | VP Int | VNull | VF Name | VS Name [(Variable, Val)] | VA [Val] | VR Int Local [RefPath] Bool Val [(Int, Int)]
    deriving (Eq, Show)

-- (OMem is the memory of Addr::alloc: the slots that hold a value, of so many; an address is the number of the cell times 2^32 and the slot)
data Obj = OList [Val] | OBox Val | OClosure Name Val | OMem (Map Integer Val) Integer

data Cell = Cell {cellGeneration :: Int, cellObject :: Obj}

-- What a local holds, and for a local that only looks at a value, which one and how it was when it looked
data Slot = Slot {slotValue :: Val, slotLook :: Maybe [(Int, Int)]}

data Frame = Frame {frameIdentity :: Int, frameFunction :: Function, frameSlots :: Map Local Slot}

data St = St
    { stHeap :: Map Int Cell
    , stNext :: Int
    , stNextFrame :: Int
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
freeTree (VA values) = mapM_ freeTree values
freeTree _ = return ()

-- Whether the value still holds something to free: a value of the heap, or one with a drop (a value whose owning fields were all taken
-- out holds nothing, and is not dropped)
holdsSomething :: Program -> Val -> Bool
holdsSomething _ VNull = False
holdsSomething _ (VP _) = True
holdsSomething program (VS name fs)
    | isListStruct (progStorage program) name || isBoxStruct (progStorage program) name = True
    | Just _ <- typeOfValue program name >>= dropFunction program = True
    | otherwise = any (holdsSomething program . snd) fs
holdsSomething program (VA values) = any (holdsSomething program) values
holdsSomething _ _ = False

-- Whether a part of the value, inline or on the heap, was moved out (native code drops a value whole, and frees nothing of a part
-- that is not there)
holdsMovedPart :: Val -> M Bool
holdsMovedPart VNull = return True
holdsMovedPart (VP a) = heapPart a
holdsMovedPart (VS name fs) = storageM >>= \st -> case listCell fs of
    Just a | isListStruct st name || isBoxStruct st name -> heapPart a
    _ -> or <$> mapM (holdsMovedPart . snd) fs
holdsMovedPart (VA values) = or <$> mapM holdsMovedPart values
holdsMovedPart _ = return False

heapPart :: Int -> M Bool
heapPart a = do
    s <- getSt
    case Map.lookup a (stHeap s) of
        Nothing -> return False
        Just c -> or <$> mapM holdsMovedPart (children (cellObject c))

-- The struct or the enum that a value of a struct or of a variant is of
typeOfValue :: Program -> Name -> Maybe Name
typeOfValue program name = case Map.lookup name (progTypes program) of
    Just StructDecl{} -> Just name
    _ -> case [n | (n, EnumDecl variants) <- Map.toList (progTypes program), name `elem` map fst variants] of
        n : _ -> Just n
        [] -> Nothing

-- The memory that a list of native code (a List, on an address) has its elements in
listCell :: [(Variable, Val)] -> Maybe Int
listCell fs = case lookup "addr" fs of
    Just (VI address) | address > 0 -> Just (fromInteger (address `div` (2 ^ (32 :: Integer))))
    _ -> Nothing

children :: Obj -> [Val]
children (OList vs) = vs
children (OBox v) = [v]
children (OClosure _ v) = [v]
children (OMem slots _) = Map.elems slots

-- The values of the heap that a value holds, inline or not
pointersOf :: Storage -> Val -> [Int]
pointersOf _ (VP a) = [a]
pointersOf st (VS name fs) | isListStruct st name || isBoxStruct st name, Just a <- listCell fs = [a]
pointersOf st (VS _ fs) = concatMap (pointersOf st . snd) fs
pointersOf st (VA values) = concatMap (pointersOf st) values
pointersOf _ _ = []

cloneVal :: Val -> M Val
cloneVal v = do
    frame <- currentFrame
    cloneIn (Just (fnName (frameFunction frame))) v

cloneIn :: Maybe Name -> Val -> M Val
cloneIn current v@(VS name _) = do
    program <- stProgram <$> getSt
    let owner = typeOfValue program name
        returnsOwner fn = owner /= Nothing && case fnReturns fn of
            Just (TNamed base args) -> Just (instanceName base args) == owner
            Just (TVariant variant) -> ownerOf program variant == owner
            _ -> False
        clones = [fn | fn <- Map.elems (progFunctions program), " as Clone>::clone" `isInfixOf` fnName fn, not (null (fnParams fn)), returnsOwner fn]
    case clones of
        fn : _ | Just (fnName fn) /= current -> do
            result <- callFunction program fn [v]
            maybe (failM "a Clone implementation did not return a value") return result
        _ -> cloneFields v
cloneIn _ v = cloneFields v

-- The self-copy guard belongs to CopyOf, not to copies of its fields.
cloneFields :: Val -> M Val
cloneFields v = storageM >>= \st -> cloneFieldsWith st v

cloneFieldsWith :: Storage -> Val -> M Val
cloneFieldsWith st (VP a) = do
    c <- cell a
    case cellObject c of
        OList vs -> mapM (cloneIn Nothing) vs >>= alloc . OList
        OBox v -> cloneIn Nothing v >>= alloc . OBox
        OClosure{} -> failM "a boxed closure is copied"
        OMem _ _ -> failM "memory is copied"
-- (a copy of a list has memory of its own, with copies of the elements in use)
cloneFieldsWith st (VS name fs) | isListStruct st name, Just a <- listCell fs = do
    c <- cell a
    used <- case lookup "len" fs of
        Just (VI n) -> return n
        _ -> failM "a list without its length"
    case cellObject c of
        OMem slots _ -> do
            copies <- mapM (\(k, v) -> (,) k <$> cloneIn Nothing v) [(k, v) | (k, v) <- Map.toList slots, k < used]
            copy <- alloc (OMem (Map.fromList copies) used)
            case copy of
                VP b -> return (VS name [(f, if f == "addr" then VI (toInteger b * 2 ^ (32 :: Integer)) else if f == "cap" then VI used else v) | (f, v) <- fs])
                _ -> failM "an allocation is not on the heap"
        _ -> failM "a list that is not in memory"
-- (a copy of a Box of the library has room of its own, with a copy of the value)
cloneFieldsWith st (VS name fs) | isBoxStruct st name, Just a <- listCell fs = do
    c <- cell a
    case cellObject c of
        OMem slots size -> do
            copies <- mapM (\(k, v) -> (,) k <$> cloneIn Nothing v) (Map.toList slots)
            copy <- alloc (OMem (Map.fromList copies) size)
            case copy of
                VP b -> return (VS name [(f, if f == "addr" then VI (toInteger b * 2 ^ (32 :: Integer)) else v) | (f, v) <- fs])
                _ -> failM "an allocation is not on the heap"
        _ -> failM "a Box that is not in memory"
cloneFieldsWith st (VS name fs) = VS name <$> mapM (\(f, v) -> (,) f <$> cloneIn Nothing v) fs
cloneFieldsWith st (VA values) = VA <$> mapM (cloneIn Nothing) values
cloneFieldsWith st v = return v

-- How many places own the value: locals (not those that only look) and slots of values
owners :: Int -> M Int
owners a = do
    s <- getSt
    let st = progStorage (stProgram s)
        fromFrames = length [() | f <- stFrames s, Slot v Nothing <- Map.elems (frameSlots f), b <- pointersOf st v, b == a]
        fromHeap = length [() | c <- Map.elems (stHeap s), v <- children (cellObject c), b <- pointersOf st v, b == a]
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

-- Whether a value of the type owns something to free, as the model counts it: a list or a Box, a struct or an enum with a
-- drop, or a struct, an enum or an array that holds one
needsDrop :: Program -> Type -> Bool
needsDrop program = owning
  where
    owning ty = case ty of
        TBox{} -> True
        TBoxedClosure{} -> True
        TArrayOf t _ -> owning t
        TNamed base args -> declared (instanceName base args)
        TVariant v -> maybe False declared (ownerOf v)
        _ -> False
    declared n
        | isListStruct (progStorage program) n = True
        | Just _ <- dropFunction program n = True
        | otherwise = case Map.lookup n (progTypes program) of
            Just (StructDecl fields) -> any (owning . snd) fields
            Just (EnumDecl variants) -> any (owning . snd) (concatMap snd variants)
            Nothing -> False
    ownerOf v = case Map.lookup v (progTypes program) of
        Just StructDecl{} -> Just v
        _ -> case [n | (n, EnumDecl variants) <- Map.toList (progTypes program), v `elem` map fst variants] of
            n : _ -> Just n
            [] -> Nothing

-- Whether a local owns what it holds
localHeap :: Program -> Frame -> Local -> Bool
localHeap program f l = maybe False (needsDrop program . localType) (Map.lookup l (fnLocals (frameFunction f)))

-- Reading a local: it has to hold something, that has to be there, and be as it was when a local that only looks saw it
readLocal :: Local -> M Val
readLocal l = do
    f <- currentFrame
    v <- readLocalAt (frameIdentity f) l
    case (v, Map.lookup l (fnLocals (frameFunction f))) of
        (VR{}, Just (LocalDecl ty _)) | l `elem` fnBorrowed (frameFunction f), not (refType ty) -> dereference v
        _ -> return v
  where
    refType TRef{} = True
    refType TMutRef{} = True
    refType _ = False

readLocalAt :: Int -> Local -> M Val
readLocalAt depth l = do
    s <- getSt
    f <- case [frame | frame <- stFrames s, frameIdentity frame == depth] of
        frame : _ -> return frame
        _ -> failM "a reference is to a frame that has returned"
    case Map.lookup l (frameSlots f) of
        Nothing -> failM ("read of " ++ show l ++ " before it is given a value")
        Just (Slot VNull _) -> failM ("use of " ++ show l ++ " after it was moved from")
        Just (Slot v look) -> do
            mapM_ (\(a, g) -> cell a >>= \c -> if g /= cellGeneration c then failM (show l ++ " looks at a value that changed") else return ()) (maybe [] id look)
            return v

refPath :: RefStep -> M RefPath
refPath (RefField ctor field) = return (RefFieldPath ctor field)
refPath (RefIndex o) = RefIndexPath <$> intOperand o

readPlace :: Int -> Local -> [RefPath] -> M Val
readPlace depth root steps = readLocalAt depth root >>= dereference >>= walk steps
  where
    walk [] VNull = failM "a reference reads a place that was moved from"
    walk [] v = return v
    walk (RefFieldPath ctor field : rest) value = do
        v <- dereference value
        (actual, fields) <- throughBox ctor v >>= dataValue
        if actual == ctor then return () else failM ("a reference expects " ++ ctor ++ ", got " ++ actual)
        sub <- maybe (failM ("a reference is to a missing field " ++ field)) return (lookup field fields)
        walk rest sub
    walk (RefIndexPath i : rest) value = do
        v <- dereference value
        values <- sequenceValues v
        if i < 0 || i >= toInteger (length values) then failM "a reference is to an index outside its owner" else walk rest (values !! fromIntegral i)

dereference :: Val -> M Val
dereference (VR depth root steps mutable old generations) = do
    v <- readPlace depth root steps
    if mutable then return v else do
        if v == old then return () else failM "a borrowed place changed before its last use"
        mapM_ (\(a, g) -> cell a >>= \c -> if g == cellGeneration c then return () else failM "a borrowed value changed before its last use") generations
        return v
dereference v = return v

borrowValue :: Local -> [RefPath] -> Bool -> M Val
borrowValue root steps mutable = do
    f <- currentFrame
    v <- readLocalAt (frameIdentity f) root
    case v of
        VR _ _ _ wasMutable _ _ -> do
            _ <- dereference v
            if mutable && not wasMutable then failM "an update reference is made through a read reference" else return ()
        _ -> return ()
    let (depth, owner, path) = case v of
            VR d r prior _ _ _ -> (d, r, prior ++ steps)
            _ -> (frameIdentity f, root, steps)
    current <- readPlace depth owner path
    st <- storageM
    generations <- mapM (\a -> cell a >>= \c -> return (a, cellGeneration c)) (pointersOf st current)
    return (VR depth owner path mutable current generations)

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
constant (CArray cs) = VA <$> mapM constant cs
constant (CData name fs) = VS name <$> mapM (\(f, c) -> (,) f <$> constant c) fs
constant (CFn name) = return (VF name)

-- The values compared and shown
data Pure = PI Integer | PB Bool | PL [Pure] | PD Name [(Variable, Pure)] | PF Name
    deriving (Eq, Show)

toPure :: Val -> M Pure
toPure v = storageM >>= \st -> toPureWith st v

toPureWith :: Storage -> Val -> M Pure
toPureWith st (VI i) = return (PI i)
toPureWith st (VB b) = return (PB b)
toPureWith st (VA values) = PL <$> mapM toPure values
toPureWith st (VF n) = return (PF n)
toPureWith st VNull = failM "a value that was moved from is compared"
toPureWith st v@VR{} = dereference v >>= toPure
toPureWith st (VP a) = do
    c <- cell a
    case cellObject c of
        OList vs -> PL <$> mapM toPure vs
        OBox v -> toPure v
        OClosure{} -> failM "an opaque boxed closure is observed directly"
        OMem _ _ -> failM "memory is compared"
-- (a list of native code is the elements in use of the array it holds)
toPureWith st (VS name fs)
    | isListStruct st name, Just a <- listCell fs, Just (VI used) <- lookup "len" fs = do
        (_, obj) <- object (VP a)
        PL <$> mapM toPure (take (fromIntegral used) (children obj))
    -- (a Box of the library is the value it holds)
    | isBoxStruct st name, Just a <- listCell fs = do
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

sequenceValues :: Val -> M [Val]
sequenceValues (VA values) = return values
sequenceValues value = children . snd <$> object value

object :: Val -> M (Int, Obj)
object v = storageM >>= \st -> objectWith st v

objectWith :: Storage -> Val -> M (Int, Obj)
objectWith _ (VP a) = do
    c <- cell a
    return (a, cellObject c)
-- (a native list or Box is read at the slots its first addr field owns)
objectWith st (VS name fs) | isListStruct st name || isBoxStruct st name, Just a <- listCell fs = objectWith st (VP a)
objectWith _ v = failM ("not a value of the heap: " ++ show v)

-- (the program's storage declarations; a fixture written without a storage record spells them List and Box)
isListStruct :: Storage -> Name -> Bool
isListStruct st name = takeWhile (/= '<') name == (if null (storageList st) then "List" else storageList st)

isBoxStruct :: Storage -> Name -> Bool
isBoxStruct st name = takeWhile (/= '<') name == (if null (storageBox st) then "Box" else storageBox st)

storageM :: M Storage
storageM = progStorage . stProgram <$> getSt

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
throughBox name v = storageM >>= \st -> case v of
    VS boxName fs | isBoxStruct st boxName, boxName /= name, Just a <- listCell fs -> boxed a
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
        Borrow root steps mutable -> mapM refPath steps >>= \path -> borrowValue root path mutable
        Deref o -> readOperand o >>= dereference
        MakeBox o -> readOperand o >>= alloc . OBox
        PackClosure o thunk -> readOperand o >>= alloc . OClosure thunk
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
            st <- storageM
            case (v, o) of
                (VP _, Move _) -> unbox v
                (VP _, _) -> dataValueOf v
                -- (and so is a Box of the library)
                (VS name fs, Move _) | isBoxStruct st name, Just a <- listCell fs -> do
                    inner <- boxed a
                    s <- getSt
                    putSt s{stHeap = Map.delete a (stHeap s)}
                    return inner
                (VS name fs, _) | isBoxStruct st name, Just a <- listCell fs -> boxed a
                _ -> return v
        CopyOf o -> readOperand o >>= cloneVal
        TakeField l name field -> do
            f <- currentFrame
            case Map.lookup l (frameSlots f) of
                Just (Slot _ (Just _)) -> failM ("a field is taken from " ++ show l ++ ", which only looks")
                _ -> return ()
            v <- readLocal l
            st <- storageM
            case v of
                VS boxName boxFs | isBoxStruct st boxName, Just a <- listCell boxFs -> do
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
        (Length, [l]) -> VI . toInteger . length <$> (readOperand l >>= sequenceValues)
        (NewArray, [n, x]) -> do
            count <- intOperand n
            v <- readOperand x
            copies <- mapM (const (cloneVal v)) [1 .. count]
            case x of Copy _ -> return (); _ -> freeTree v
            return (VA copies)
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
        (Pop, [l]) -> do
            list <- readOperand l
            (a, obj) <- object list
            inPlace a
            case children obj of
                [] -> failM "Pop of an empty list"
                vs -> do
                    freeTree (last vs)
                    setObject a (OList (init vs))
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
        -- (an empty Uninit is cleared bytes, which own nothing; a value taken apart is cleared so by the ghost erasure)
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
        vs <- readOperand l >>= sequenceValues
        let i = pick (length vs)
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
                Just (Slot VNull Nothing) -> failM (show l ++ " is dropped after it was moved from")
                Just (Slot v Nothing) -> do
                    moved <- holdsMovedPart v
                    when moved (failM (show l ++ " is dropped with a part that was moved out of it"))
                    freeTree v >> putSlot l (Slot VNull Nothing)
        Peek d rv -> do
            v <- evalRvalue rv
            -- (a local that only looks remembers how what it looks at was)
            storage <- storageM
            looks <- mapM (\a -> (\c -> (a, cellGeneration c)) <$> cell a) (pointersOf storage v)
            -- (and owns nothing, even when what it looks at holds nothing of the heap, as a value read where it is at an address;
            -- a value taken apart is cleared, and holds nothing)
            putSlot d (Slot v (if v == VNull then Nothing else Just looks))
        Assign d rv -> do
            v <- assignedValue d rv
            f <- currentFrame
            program <- stProgram <$> getSt
            case Map.lookup d (frameSlots f) of
                -- (an update parameter is assigned in its caller's place: native code stores over it and frees nothing)
                Just (Slot (VR depth owner prior True _ _) (Just _)) | d `elem` fnMutBorrowed (frameFunction f) -> writePlaceAt depth owner prior v
                _ -> assignLocal program f d rv v
        -- (native code stores over the place and frees nothing: what the place held must have been released before)
        AssignRef root steps rv -> do
            v <- evalRvalue rv
            path <- mapM refPath steps
            f <- currentFrame
            target <- readLocalAt (frameIdentity f) root
            case target of
                VR depth owner prior True _ _ -> writePlaceAt depth owner (prior ++ path) v
                VR{} -> failM "a place is assigned through a read reference"
                _ -> failM "a place is assigned through a local that is not a reference"

-- (MirLists makes a constant list of Ints, Bools or Bytes as Box::new of its array: a List over memory of its own that holds the
-- elements, with as much room as it has elements)
assignedValue :: Local -> Rvalue -> M Val
assignedValue d rv = do
    f <- currentFrame
    st <- storageM
    case (rv, localType <$> Map.lookup d (fnLocals (frameFunction f))) of
        (MakeBox (Const (CArray cs)), Just (TNamed base args)) | isListStruct st base -> do
            vs <- mapM constant cs
            let n = toInteger (length vs)
            memory <- alloc (OMem (Map.fromList (zip [0 ..] vs)) n)
            case memory of
                VP a -> return (VS (instanceName base args) [("addr", VI (toInteger a * 2 ^ (32 :: Integer))), ("len", VI n), ("cap", VI n)])
                _ -> failM "an allocation is not on the heap"
        _ -> evalRvalue rv

-- An assignment to a local of the frame: what it held is freed, and a value that is only looked at cannot be what it is given
assignLocal :: Program -> Frame -> Local -> Rvalue -> Val -> M ()
assignLocal program f d rv v =
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

writePlaceAt :: Int -> Local -> [RefPath] -> Val -> M ()
writePlaceAt depth root steps v = do
    s <- getSt
    case break (\frame -> frameIdentity frame == depth) (stFrames s) of
        (before, frame : after) -> do
            old <- case Map.lookup root (frameSlots frame) of
                Just (Slot value Nothing) -> return value
                Just (Slot _ (Just _)) -> failM "a reference writes a place that only looks at a value"
                Nothing -> failM "a reference writes a place that holds nothing"
            new <- replaceAt steps old
            s' <- getSt
            putSt s'{stFrames = before ++ frame{frameSlots = Map.insert root (Slot new Nothing) (frameSlots frame)} : after}
        _ -> failM "a reference is to a frame that has returned"
  where
    replaceAt [] _ = return v
    replaceAt (RefFieldPath ctor field : rest) (VS name fs) | name == ctor, Just sub <- lookup field fs = do
        sub' <- replaceAt rest sub
        return (VS name [(n, if n == field then sub' else x) | (n, x) <- fs])
    replaceAt (RefIndexPath i : rest) container@(VP a) = do
        c <- cell a
        case cellObject c of
            OList vs | i >= 0 && i < toInteger (length vs) -> do
                let k = fromInteger i
                sub' <- replaceAt rest (vs !! k)
                setObject a (OList (take k vs ++ [sub'] ++ drop (k + 1) vs))
                return container
            _ -> failM "a reference writes an element outside its list"
    replaceAt _ _ = failM "a reference writes a place of a shape the model does not have"

-- Runs a function from its entry; what it returns is what _0 holds, moved out
callFunction :: Program -> Function -> [Val] -> M (Maybe Val)
callFunction program fn args = do
    -- (a parameter that is lent only looks at the value: the function owns nothing of it, and cannot move from it)
    -- (and remembers how it was, so that a change to it while it is lent is found)
    storage <- storageM
    looks <- mapM (\(p, v) -> if p `elem` fnBorrowed fn then mapM (\a -> (\c -> (a, cellGeneration c)) <$> cell a) (pointersOf storage v) else return []) (zip (fnParams fn) args)
    s' <- getSt
    putSt s'{stNextFrame = stNextFrame s' + 1, stFrames = Frame (stNextFrame s') fn (Map.fromList [(p, Slot v (if p `elem` fnBorrowed fn then Just lk else Nothing)) | ((p, v), lk) <- zip (zip (fnParams fn) args) looks]) : stFrames s'}
    result <- runBlock program fn (BlockId 0)
    s' <- getSt
    case stFrames s' of
        f : rest -> do
            -- (the value a drop is given is not freed by it: its fields are freed after it)
            let dropped l = isDropFunction program (fnName fn) && take 1 (fnParams fn) == [l]
                leftover = [l | (l, Slot v Nothing) <- Map.toList (frameSlots f), holdsSomething program v, l /= Local 0, localHeap program f l, not (dropped l)]
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
            (name, capture) <- case target of
                VF n -> return (n, [])
                VR{} -> do
                    owner <- dereference target
                    (_, payload) <- object owner
                    case payload of
                        OClosure n v -> return (n, [v])
                        _ -> failM "a boxed call does not point to a closure"
                _ -> failM "a call of something that is not a function"
            callee' <- maybe (failM ("no function " ++ name)) return (Map.lookup name (progFunctions program))
            let (self, params) = splitAt (length capture) (fnParams callee')
            if any (`elem` fnMutBorrowed callee') self then failM "the heap model does not dispatch mutable boxed closures" else return ()
            values <- mapM (\(param, operand) -> case operandLocal operand of
                Just local | param `elem` fnBorrowed callee' -> borrowValue local [] (param `elem` fnMutBorrowed callee')
                _ -> readOperand operand) (zip params args)
            result <- callFunction program callee' (capture ++ values)
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
    case runM go (St Map.empty 1 0 [] 1000000 program) of
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
sameOnModel what program = case expandRefWrites program `bindResult` \_ -> nativeProgram program `bindResult` insertOwnership of
    Error e -> Just (what ++ ": " ++ e)
    Ok owned -> case verifyProgram owned of
        Error e -> Just (what ++ ": the owned MIR is ill formed: " ++ e)
        Ok () -> case (runOwned owned, runProgram program) of
            (Right a, Ok b) -> testAssertEq a b
            (Left e, Error e') | e == e' -> Nothing
            (Left e, _) -> Just (what ++ ": " ++ e)
            (Right a, Error e) -> Just (what ++ ": the model returns " ++ show a ++ " where the executor stops with " ++ e)

-- A program lowered and run on the model, with the answer of the executor, as source
-- (through TestHarness.compileOnce, so validated programs are compiled once and shared with other groups;
-- only successful compiles are cached by the harness)
onSource :: String -> String -> IO TestResult
onSource name source = do
    compiled <- compileOnce source
    pure (onProgram name compiled)

onProgram :: String -> Result Program String -> TestResult
onProgram name compiled =
    case compiled of
        Error e -> Just (name ++ " does not compile: " ++ e)
        Ok program -> sameOnModel name program

-- Array-using examples are excluded at list construction, not silently passed in onFile: the heap model
-- holds values of the heap and has no array heap model, so running these would be a blind spot (see the
-- explicit blind-spot case in testOwnership). This list is the usesArrays match over nativeExamples.
arrayExamples :: [FilePath]
arrayExamples =
    [ "examples/array_data.tersus", "examples/array_owners.tersus", "examples/array_sizes.tersus", "examples/arrays.tersus"
    , "examples/borrowing.tersus", "examples/box_array.tersus", "examples/generic_structs.tersus", "examples/list_methods.tersus"
    , "examples/sized_structs.tersus", "examples/type_parameters.tersus", "examples/vec.tersus"
    ]

ownershipExamples :: [FilePath]
ownershipExamples = [path | path <- nativeExamples, path `notElem` arrayExamples]

arrayErgonomicsPrograms :: [(String, String)]
arrayErgonomicsPrograms = [(name, source) | (name, source) <- ergonomicsPrograms, usesArrays source]

ownershipPrograms :: [(String, String)]
ownershipPrograms = [program | program <- validatedPrograms, program `notElem` arrayErgonomicsPrograms]

onFile :: FilePath -> IO TestResult
onFile path = do
    loaded <- loadFromFilesystem path
    case loaded of
        Right (PackageResult _) -> do
            compiled <- programFromFile path
            pure (onProgram path compiled)
        _ -> readFile path >>= onSource path

-- The same for a program that is lowered without being validated
onLowered :: String -> String -> TestResult
onLowered name source =
    case parseSourceParts True source of
        Error e -> Just (name ++ " does not parse: " ++ e)
        Ok parts -> case lowerParts parts of
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
    [TestCase label . pure $ withOwned source (\t -> testAssertEq (map (\needle -> count needle (scopeText t scope)) needles) expected) | (label, source, scope, needles, expected) <- countCases]
        ++ [ TestCase "a list pushed to in a loop is changed in place" . pure $
                withOwned "l = []; i = 0; while i < 4 [{ affirm i >= 0; }] shrinks 4 - i { l = push(l, i); i = i + 1; }; return size(l);" (\t -> let m = functionText "main" t in testAssertEq (count "clone" m) 0 `orElseT` testAssertTrue ("listPush<Int>(move _1" `isInfixOf` m))
           , TestCase "an array beside a list: only the list is freed" . pure $
                withOwned "l = [1]; a = array(2, 0); a = set(a, 1, size(l)); return get(a, 1);" (\t -> let m = functionText "main" t in testAssertEq (count "clone" m) 0 `orElseT` testAssertTrue (not ("drop _2" `isInfixOf` m) && "drop _1" `isInfixOf` m))
           , TestCase "a part that is kept is copied" . pure $
                withOwned "rows = [[1], [2, 3]]; row = clone(get(rows, 1)); rows = set(rows, 0, clone(row)); return size(row);" (\t -> testAssertTrue (count "clone" (functionText "main" t) >= 1))
           , TestCase "a cast is read from the value itself" . pure $
                withOwned "enum S { A { r: Int }, C }; x = S::A { r: 4 }; return (x as S::A).r;" (\t -> testAssertEq (count "clone" t) 0 `orElseT` testAssertTrue (not (" as S::A;" `isInfixOf` t)))
           , TestCase "a parameter that is assigned a part is freed first" . pure $
                withOwned "fn f(row: List<Int>, rows: List<List<Int>>) -> Int [{ affirm size(rows) > 0; }] [{ }] { row = get(rows, 0); return size(row); }; return f([1], [[2, 3]]);" (\t -> let f = functionText "f" t in testAssertEq (count "peek" f, count "copy" f) (1, 1) `orElseT` testAssertTrue ("drop _1" `isInfixOf` f))
           , TestCase "a value moved on every path is not dropped at the return" . pure $
                withOwned "l = [1]; m = l; return size(m);" (\t -> let m = functionText "main" t in testAssertTrue (not ("drop _1" `isInfixOf` m) && "drop _2" `isInfixOf` m))
           , TestCase "a value moved on one path is dropped under a test of its flag" . pure $
                withOwned "l = [1, 2]; m = [0]; if size(l) = 2 { m = l; }; return size(m);" (\t -> let m = functionText "main" t in testAssertTrue (count "drop _1" m == 1 && "drop _2;" `isInfixOf` m && "const false;" `isInfixOf` m))
           , TestCase "a field taken on one path is dropped under a test of its flag" . pure $
                withOwned "struct S { a: List<Int>, b: List<Int> }; s = S { a: [1, 2], b: [3, 4] }; n = 0; if size(s.b) = 2 { x = s.a; n = size(x); }; return n + size(s.b);" (\t -> let m = functionText "main" t in testAssertTrue ("take (_" `isInfixOf` m && "drop _" `isInfixOf` m && count "const false;" m >= 2))
           ]
  where
    -- Pure count-tuple cases: (label, source, function scope or "" for whole text, needles, expected counts)
    -- An array is held inline and has nothing in it to free, so the pass leaves it alone (the heap model
    -- holds values of the heap, and programs with arrays are not run on it).
    countCases =
        [ ("an array is not owned: no copy, no move, nothing to free", "a = array(3, 0); b = set(a, 0, 1); return get(b, 0) + get(a, 1) + size(a);", "", ["clone", "move", "drop", "peek"], [0, 0, 0, 0])
        , ("a list that is cloned for a push is copied once", "x = [1]; y = push(clone(x), 2); return size(x) + size(y);", "main", ["clone"], [1])
        -- (two takes in the arm, and two more that drop the fields left at the join of the arms, each under its flag)
        , ("a match takes the fields out of the value", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; fn sum(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; }; return sum(Box::new(T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Leaf) }));", "sum", ["clone", "take ("], [0, 4])
        , ("a part that is only read is looked at", "rows = [[1], [2, 3]]; return size(get(rows, 1));", "main", ["clone", "peek Get"], [0, 1])
        , ("a call with a clone of an argument that is used after it copies the argument", "fn n(l: List<Int>) -> Int { return size(l); }; l = [1, 2]; return n(clone(l)) + n(l);", "main", ["clone"], [1])
        , ("a copy of a parameter is one copy", "fn f(a: List<Int>) -> List<Int> [{ affirm size(a) > 0; }] [{ }] { out = clone(a); out = set(out, 0, size(a)); return out; }; return f([5]);", "f", ["clone"], [1])
        , ("a value that is overwritten is dropped before the assignment", "x = [1]; x = [1, 2]; return size(x);", "main", ["drop _1"], [2])
        , ("a struct taken apart is not dropped, and the field taken out is", "struct P { a: List<Int>, n: Int }; p = P { a: [1], n: 4 }; P { a: x, n: k } = p; return size(x) + k;", "main", ["peek UninitEmpty", "drop _"], [1, 1])
        , ("a value with a field taken out is dropped as the field left", "struct P { a: List<Int>, b: List<Int> }; fn f(p: P) -> Int { x = p.a; return size(x); }; return f(P { a: [1], b: [2, 3] });", "f", ["take (_1 as P).b;", "drop _3;", "drop _1;"], [1, 1, 0])
        , ("a value with every owning field taken out is not dropped", "struct P { a: List<Int>, b: List<Int>, n: Int }; fn f(p: P) -> Int { x = p.a; y = p.b; return size(x) + size(y) + p.n; }; return f(P { a: [1], b: [2, 3], n: 4 });", "f", ["drop _1;"], [0])
        , ("a field taken on one path is dropped once, under its flag", "struct P { a: List<Int>, b: List<Int> }; fn f(p: P, c: Bool) -> Int { n = size(p.b); if c { x = p.a; n = n + size(x); }; return n; }; return f(P { a: [1], b: [2, 3] }, true) * 10 + f(P { a: [1], b: [2, 3] }, false);", "f", ["take (_1 as P).a;", "take (_1 as P).b;", "drop _1;"], [2, 1, 0])
        , ("a payload left in a match is dropped on its own, under a test of the variant", "enum E { A { x: List<Int>, y: List<Int> }, B { z: List<Int> } }; fn f(e: E) -> Int { return match e { E::A { x: x } => size(x), E::B { z: z } => size(z) * 10 }; }; return f(E::A { x: [1], y: [2, 3] }) + f(E::B { z: [4] });", "f", ["as E::A).y;", "drop _3;"], [1, 0])
        , ("a Box with a field of its value taken out frees its room and the field left", "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; fn left(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v } => v + left(l) }; }; return left(Box::new(T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Leaf) }));", "left", ["move _3 as T::Node;", "as T::Node).r;", "drop _3;"], [1, 1, 1])
        , ("a tuple taken apart is not dropped", "fn two() -> (List<Int>, List<Int>) { return ([1], [2, 3]); }; (a, b) = two(); return size(a) * 10 + size(b);", "main", ["drop _1;", "drop _2;", "drop _3;"], [0, 1, 1])
        ]
        ++ [ ("the String " ++ helper ++ " takes apart is not dropped after", "s = \"ab\".concat(\"cd\"); s = s.push(toByte(101)); s = set(s, 0, toByte(65)); t = \"x = {}, ok = {}\\n\".format(1, true); return size(s) + size(t);", helper, ["drop _"], [0])
           | helper <- ["<String>::concat", "<String as Growable>::push", "<String as Sequence>::set", "<String>::formatPart", "<Int as Format>::writeTo", "<Bool as Format>::writeTo", "<String>::formatInto[Int, Bool]"] ]
        ++ [ ("the list " ++ helper ++ " takes apart is not dropped after", "l = [1]; l = push(l, 2); l = set(l, 0, 3); l = pop(l); return size(l);", helper ++ "<Int>", ["drop"], [0])
           | helper <- ["listPush", "listSet", "listPop"] ]
    scopeText t "" = t
    scopeText t scope = functionText scope t
    withOwned source check = either Just check (ownedText source)
    orElseT Nothing b = b
    orElseT a _ = a

-- No value that holds one with a drop of its own is ever copied (a CopyOf of it would be dropped twice, unless the type's Clone makes
-- a value of its own): a part of one is looked at in place, and MirMoves sees that what it is a part of does not change while it is
-- looked at
noDropCopyTests :: [Test]
noDropCopyTests =
    [TestCase name . pure $ noDropCopy (ownedSource source) | (name, source) <- validatedPrograms, "impl Drop" `isInfixOf` source]
        ++ [TestCase name (noDropCopy <$> ownedFromFiles ownRoleEntry files) | (name, files) <- ownRolePrograms]
  where
    noDropCopy result = case result of
        Error e -> Just e
        Ok owned -> case [(fnName fn, d) | fn <- progMain owned : Map.elems (progFunctions owned), BasicBlock stmts _ <- Map.elems (fnBlocks fn), Assign d (CopyOf _) <- stmts, Just decl <- [Map.lookup d (fnLocals fn)], holdsDropOf owned (localType decl)] of
            [] -> Nothing
            copies -> Just ("copies of values with a drop: " ++ show copies)

holdsDropOf :: Program -> Type -> Bool
holdsDropOf program = go Set.empty
  where
    go seen ty = case ty of
        TArrayOf t _ -> go seen t
        TNamed base args
            | isListStruct (progStorage program) n || isBoxStruct (progStorage program) n -> any (go seen) [t | ArgType t <- args]
            | n `Set.member` seen -> False
            | Just _ <- dropFunction program n -> not (ownClone n)
            | otherwise -> case Map.lookup n (progTypes program) of
                Just (StructDecl fields) -> any (go (Set.insert n seen) . snd) fields
                Just (EnumDecl variants) -> any (go (Set.insert n seen) . snd) (concatMap snd variants)
                Nothing -> any (go seen) [t | ArgType t <- args]
          where
            n = instanceName base args
        TVariant v -> maybe False (\owner -> go seen (TNamed owner [])) (ownerOf program v)
        _ -> False
    -- (as the emitter finds a Clone: the type's checked Clone, or without checked facts a function `<... as Clone>::clone` whose
    -- result is exactly the type)
    ownClone n
        | Just _ <- progOwnership program = maybe False (`Map.member` progFunctions program) (snd <$> (factsOf program n >>= ownershipClone))
        | otherwise = or [True | fn <- Map.elems (progFunctions program), " as Clone>::clone" `isInfixOf` fnName fn, Just (TNamed b a) <- [fnReturns fn], instanceName b a == n]

-- The ownership pass refuses, at the types native code is made of, what MirMoves refuses where the program says it: owned MIR given
-- straight to the pass, which MirMoves never saw, and the copy of a generic function that MirMoves checks only in general
passSafetyTests :: [Test]
passSafetyTests =
    [ testCase "the pass refuses a change to what a look at a value with a drop is a part of" $
        refused [Assign (Local 3) (ReadField (Copy (Local 1)) "G" "h"), Assign (Local 1) (Use (Move (Local 2))), Assign (Local 0) (ReadField (Copy (Local 3)) "H" "n")]
            "_1 is given another value while _3 still looks at a part of it that holds a value with a drop and cannot be copied"
    , testCase "the pass refuses a copy of a value with a drop and no Clone" $
        refused [Assign (Local 3) (CopyOf (Copy (Local 4))), Assign (Local 0) (ReadField (Copy (Local 3)) "H" "n")]
            "_3 would be a copy of a value with a drop that has no Clone of its own"
    , TestCase "the pass refuses the copy of a generic function that changes what a look is a part of" . pure $
        case ownedSource generic of
            Error e -> testAssertTrue ("w is given another value while v still looks at a part of it that holds a value with a drop" `isInfixOf` e) `orElse` Just e
            Ok _ -> Just "the pass accepted it"
    , testCase "the pass names the value that changes, not the first look it is through" $
        case insertOwnership (holderProgram [Assign (Local 5) (ReadField (Copy (Local 6)) "O" "g"), Assign (Local 3) (ReadField (Copy (Local 5)) "G" "h"), Assign (Local 6) (Use (Move (Local 7))), Assign (Local 0) (ReadField (Copy (Local 3)) "H" "n")]) of
            Error e -> testAssertTrue ("_6 is given another value while _3 still looks at" `isInfixOf` e) `orElse` Just e
            Ok _ -> Just "the pass accepted it"
    , TestCase "the pass refuses the copy of a generic function that changes what a look at an instance is a part of" . pure $
        case ownedSource genericInstance of
            Error e -> testAssertTrue ("w is given another value while v still looks at a part of it that holds a value with a drop" `isInfixOf` e) `orElse` Just e
            Ok _ -> Just "the pass accepted it"
    , TestCase "the pass refuses the copy of a generic function that changes what a look through a reference is a part of" . pure $
        case ownedSource genericThroughReference of
            Error e -> testAssertTrue ("o is given another value while v still looks at a part of it that holds a value with a drop" `isInfixOf` e) `orElse` Just e
            Ok _ -> Just "the pass accepted it"
    , testCase "the pass accepts a look whose owner does not change" $
        case insertOwnership (holderProgram [Assign (Local 3) (ReadField (Copy (Local 1)) "G" "h"), Assign (Local 0) (ReadField (Copy (Local 3)) "H" "n")]) of
            Error e -> Just e
            Ok _ -> Nothing
    ]
  where
    refused stmts expected = case insertOwnership (holderProgram stmts) of
        Error e -> testAssertTrue (expected `isInfixOf` e) `orElse` Just e
        Ok _ -> Just "the pass accepted it"
    orElse Nothing _ = Nothing
    orElse _ e = e
    h = TNamed "H" []
    g = TNamed "G" []
    generic = "struct H { addr: Addr<Int>, xs: List<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for H { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl H { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, xs: [1, 2], blk: b }; }; }; struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; fn f<T: Sz>(w: W<T>, w2: W<T>) -> Int { v = w.x; w = w2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));"
    genericInstance = "struct H { addr: Addr<Int>, xs: List<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for H { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl H { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, xs: [1, 2], blk: b }; }; }; struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; struct V<T> { x: T, n: Int }; impl<T: Clone> Clone for V<T> { }; fn keep<T>(x: &T) -> Int { return 1; }; fn f<T>(w: W<T>, w2: W<T>) -> Int { v = w.x; w = w2; return keep(v); }; k = clone(V { x: 1, n: 2 }); return f(W::new(V { x: H::new(), n: 3 }), W::new(V { x: H::new(), n: 4 })) + k.n;"
    genericThroughReference = "struct H { addr: Addr<Int>, xs: List<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for H { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl H { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, xs: [1, 2], blk: b }; }; }; struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; struct V<T> { x: T, n: Int }; impl<T: Clone> Clone for V<T> { }; fn keep<T>(x: &T) -> Int { return 1; }; fn f<T>(o: W<T>, o2: W<T>) -> Int { r = &o; v = (*r).x; o = o2; return keep(v); }; return f(W::new(H::new()), W::new(H::new()));"
    holderProgram stmts =
        let stub = progMain (mainProgram [] [])
            fn = stub{fnName = "f", fnParams = [Local 1, Local 2, Local 4, Local 6, Local 7], fnReturns = Just TInt, fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl g Nothing), (Local 2, LocalDecl g Nothing), (Local 3, LocalDecl h Nothing), (Local 4, LocalDecl h Nothing), (Local 5, LocalDecl g Nothing), (Local 6, LocalDecl (TNamed "O" []) Nothing), (Local 7, LocalDecl (TNamed "O" []) Nothing)], fnBlocks = Map.singleton (BlockId 0) (BasicBlock stmts Return)}
            dropOf ty = stub{fnParams = [Local 1], fnReturns = Just TInt, fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl ty Nothing)], fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Use (Const (CInt 0)))] Return)}
         in (mainProgram [] []){progTypes = Map.fromList [("H", StructDecl [("n", TInt), ("a", TAddr TInt)]), ("G", StructDecl [("h", h), ("m", TInt), ("a", TAddr TInt)]), ("O", StructDecl [("g", g), ("k", TInt), ("a", TAddr TInt)])], progFunctions = Map.fromList [("f", fn), ("<H as Drop>::drop", (dropOf h){fnName = "<H as Drop>::drop"}), ("<G as Drop>::drop", (dropOf g){fnName = "<G as Drop>::drop"}), ("<O as Drop>::drop", (dropOf (TNamed "O" [])){fnName = "<O as Drop>::drop"})]}

-- MirMoves.holdsDrop and holdsOwnDrop in lib/mir/ownership/common.tersus are one predicate, at the types of the program as written and
-- at the types native code is made of. For each shape, a look at a part of that shape whose owner changes is refused by MirMoves in a
-- function with the shape written out, and by the ownership pass in the copy of a generic function for it (which MirMoves takes to
-- hold no such value), exactly when the shape holds a value with a drop and no Clone; and accepted by both otherwise.
agreementTests :: [Test]
agreementTests =
    [ TestCase (name ++ (if holder then " holds a value with a drop" else " holds none")) $ do
        concrete <- owned (prelude ++ "fn f(w: W<" ++ ty ++ ">, w2: W<" ++ ty ++ ">) -> Int { v = w.x; w = w2; return keep(v); }; return f(W::new(" ++ value ++ "), W::new(" ++ value ++ "));")
        generic <- owned (prelude ++ "fn f<T>(w: W<T>, w2: W<T>) -> Int { v = w.x; w = w2; return keep(v); }; return f(W::new(" ++ value ++ "), W::new(" ++ value ++ "));")
        pure $ firstFailure
            [ verdict "MirMoves" holder ("Move error" `isInfixOf`) concrete
            , verdict "the ownership pass" holder ("still looks at a part of it that holds a value with a drop" `isInfixOf`) generic
            ]
    | (name, prelude, ty, value, holder) <- shapes
    , let owned source = if cloned `isPrefixOf` prelude then ownedFromFiles ownRoleEntry (ownRoleFiles source) else pure (ownedSource source)
    ]
  where
    verdict who holder refusal result = case (holder, result) of
        (True, Error e) | refusal e -> Nothing
        (True, Error e) -> Just (who ++ " refused it for another reason: " ++ e)
        (True, Ok _) -> Just (who ++ " accepted it")
        (False, Ok _) -> Nothing
        (False, Error e) -> Just (who ++ " refused it: " ++ e)
    firstFailure = foldr (\r acc -> maybe acc Just r) Nothing
    shapes =
        [ ("a value with a drop", base, "H", "H::new()", True)
        , ("a Box of one", base, "Box<H>", "Box::new(H::new())", True)
        , ("a list of them", base, "List<H>", "push([], H::new())", True)
        , ("one nine Boxes deep", base ++ "struct D { b: Box<Box<Box<Box<Box<Box<Box<Box<Box<H>>>>>>>>>, n: Int }; ", "D", "D { b: Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(Box::new(H::new()))))))))), n: 2 }", True)
        , ("a tuple with one", base, "(H, Int)", "(H::new(), 1)", True)
        , ("an enum with one", base ++ "enum E { A { h: H }, B }; ", "E", "E::A { h: H::new() }", True)
        , ("an instance whose Clone needs its argument's", base ++ "struct V<T> { x: T, n: Int }; impl<T: Clone> Clone for V<T> { }; " ++ "fn used() -> Int { k = clone(V { x: 1, n: 2 }); return k.n; }; ", "V<H>", "V { x: H::new(), n: 3 }", True)
        , ("an instance of a type with a Clone, with no value with a drop", base ++ "struct V<T> { x: T, n: Int }; impl<T: Clone> Clone for V<T> { }; ", "V<Int>", "V { x: 1, n: 3 }", False)
        , ("a number", base, "Int", "1", False)
        , ("a value with a drop and a Clone of its own", cloned, "C", "C::new(3)", False)
        , ("an instance with a Clone over a value with a Clone of its own", cloned ++ "struct U<T> { x: T, n: Int }; impl<T: Clone> Clone for U<T> { fn clone(self: &Self) -> Self { return U { x: clone(self.x), n: self.n }; }; }; fn used() -> Int { k = clone(U { x: C::new(1), n: 2 }); return k.n; }; ", "U<C>", "U { x: C::new(3), n: 4 }", False)
        -- (Foo<Int> has the Clone of its own, Foo<Baz> has none, and neither argument holds a value with a drop)
        , ("an instance of a type with a drop whose Clone it has", cloned ++ fooOwner, "Foo<Int>", "Foo::new(1)", False)
        , ("an instance of the same type whose Clone it has not", cloned ++ fooOwner, "Foo<Baz>", "Foo::new(Baz { n: 1 })", True)
        ]
    base = "struct H { addr: Addr<Int>, xs: List<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for H { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl H { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, xs: [1, 2], blk: b }; }; }; struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; fn keep<T>(x: &T) -> Int { return 1; }; "
    fooOwner = "struct Baz { n: Int }; struct Foo<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for Foo<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> Foo<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; impl<T: Clone> Clone for Foo<T> { fn clone(self: &Self) -> Self { return Foo::new(clone(self.x)); }; }; fn usedFoo() -> Int { k = clone(Foo::new(1)); return keep(k); }; "
    -- (C has a Clone of its own, which makes a value of its own, and a drop: its programs are a package that binds them)
    cloned = freshClone ++ "struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; fn keep<T>(x: &T) -> Int { return 1; }; "

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
    , mistake "a value is dropped after it is moved" "dropped after it was moved from"
        [Assign (Local 1) (Use (Const (CList [CInt 1]))), Assign (Local 2) (Use (Move (Local 1))), Drop (Local 2), Drop (Local 1)]
    , TestCase "a value is dropped with a field that was taken out of it" . pure $
        let holder = mainProgram [(Local 1, TNamed "Holder" []), (Local 2, onHeap)]
                [ Assign (Local 1) (Use (Const (CData "Holder" [("xs", CList [CInt 1]), ("ys", CList [CInt 2])])))
                , Assign (Local 2) (TakeField (Local 1) "Holder" "xs")
                , Drop (Local 2)
                , Drop (Local 1)
                ]
         in case runOwned holder{progTypes = Map.singleton "Holder" (StructDecl [("xs", onHeap), ("ys", onHeap)])} of
                Left e -> if "a part that was moved out" `isInfixOf` e then Nothing else Just ("expected a drop of a part that was moved out, got " ++ e)
                Right _ -> Just "the model accepts it"
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
                , fnTypeParams = []
                , fnBorrowed = []
            , fnMutBorrowed = []
            , fnFrom = []
                , fnSpec = emptySpec
                }
        , progGenerics = Map.empty
        , progInvariants = Map.empty
        , progBounded = Map.empty
        , progInstances = Map.empty
        , progCaptureStorage = Map.empty
        , progProtocols = Map.empty
        , progOwnership = Nothing
        }

-- A part of a list that is read after the list changes is copied: the change of a list is a call, which ends the block, and a part that
-- is looked at is only looked at by the statements that follow it in its block
windowTests :: [Test]
windowTests =
    [ TestCase "a part is copied when what it is part of changes before it is read" $ do
        let source = "rows = [[1, 2], [3]]; part = get(rows, 0); rows = set(rows, 0, [9]); return size(part);"
        model <- onSource "the part" source
        pure (model `orElseT` either Just (\t -> testAssertTrue (count "copy" (functionText "main" t) >= 1)) (ownedText source))
    , TestCase "a part is looked at when nothing changes before it is read" $ do
        let source = "rows = [[1, 2], [3]]; n = size(get(rows, 0)); rows = set(rows, 0, [9]); return n + size(rows);"
        model <- onSource "the part" source
        pure (model `orElseT` either Just (\t -> let m = functionText "main" t in testAssertEq (count "peek Get" m, count "copy" m) (1, 0)) (ownedText source))
    ]
  where
    orElseT Nothing b = b
    orElseT a _ = a

referenceModelTests :: [Test]
referenceModelTests =
    [ testCase "CopyOf dispatches a generic named Clone implementation" $ cloneCounter
        [ Peek (Local 2) (ReadField (Copy (Local 1)) "Counter<Int>" "n")
        , Assign (Local 3) (BinaryOp Add (Copy (Local 2)) (Const (CInt 1)))
        , Assign (Local 0) (MakeData "Counter<Int>" [("n", Copy (Local 3))])
        ] 8
    , testCase "a Clone implementation's self-copy does not call itself" $
        cloneCounter [Assign (Local 0) (CopyOf (Copy (Local 1)))] 7
    , testCase "a structural self-copy still dispatches member Clone implementations" $
        testAssertEq (runOwned clonedMembers) (Right (Just (MInt 4)))
    , TestCase "an indexed reference captures its index" (onSource "indexed reference" "xs = [7, 9]; i = 0; r = &get(xs, i); i = 1; return *r;")
    , TestCase "an intermediate reference field is followed" (onSource "reference field" "struct W { r: &List<Int> }; xs = [7]; w = W { r: &xs }; z = &get(*w.r, 0); return *z;")
    , TestCase "a reference copy keeps the same place" (onSource "reference copy" "xs = [7]; r = &xs; q = r; return get(*q, 0);")
    , TestCase "a returned reference keeps its caller's frame" (onSource "returned reference" "fn head(xs: &List<Int>) -> &Int from xs [{ affirm size(xs) > 0; }] [{ }] { return &get(xs, 0); }; xs = [7]; r = head(xs); return *r;")
    , rejects "a changed scalar loan cannot be refreshed by forwarding" TInt
        [ Assign (Local 1) (Use (Const (CInt 1)))
        , Assign (Local 2) (Borrow (Local 1) [] False)
        , Assign (Local 1) (Use (Const (CInt 2)))
        ] "a borrowed place changed"
    , rejects "a changed heap loan cannot be refreshed by forwarding" heap
        [ Assign (Local 1) (Use (Const (CList [CInt 1])))
        , Assign (Local 2) (Borrow (Local 1) [] False)
        , Assign (Local 1) (ListOp Set [Move (Local 1), Const (CInt 0), Const (CInt 2)])
        ] "a borrowed value changed"
    , rejects "a freed owner cannot be read through its reference" heap
        [ Assign (Local 1) (Use (Const (CList [CInt 1])))
        , Assign (Local 2) (Borrow (Local 1) [] False)
        , Drop (Local 1)
        ] "after it was moved from"
    , testCase "a returned frame identity cannot be reused by a later call" $
        let base = mainProgram [(Local 1, TRef TInt), (Local 2, TInt), (Local 3, TInt)] []
            bad = (progMain base){fnName = "bad", fnReturns = Just (TRef TInt), fnLocals = Map.fromList [(Local 0, LocalDecl (TRef TInt) Nothing), (Local 1, LocalDecl TInt Nothing)], fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 1) (Use (Const (CInt 7))), Assign (Local 0) (Borrow (Local 1) [] False)] Return)}
            later = (progMain base){fnName = "later", fnReturns = Just TInt, fnLocals = Map.singleton (Local 0) (LocalDecl TInt Nothing), fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Use (Const (CInt 9)))] Return)}
            main = (progMain base){fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "bad")) [] (Local 1) (BlockId 1))), (BlockId 1, BasicBlock [] (Call (Const (CFn "later")) [] (Local 2) (BlockId 2))), (BlockId 2, BasicBlock [Assign (Local 3) (Deref (Copy (Local 1)))] Return)]}
         in case runOwned base{progMain = main, progFunctions = Map.fromList [("bad", bad), ("later", later)]} of
                Left error -> testAssertTrue ("a frame that has returned" `isInfixOf` error)
                Right _ -> Just "the heap model accepted a reference to a returned frame"
    ]
  where
    cloneCounter body expected =
        let ty = TNamed "Counter" [ArgType TInt]
            base = mainProgram [(Local 0, TInt), (Local 1, ty), (Local 2, ty)]
                [ Assign (Local 1) (Use (Const (CData "Counter<Int>" [("n", CInt 7)])))
                , Assign (Local 2) (CopyOf (Copy (Local 1)))
                , Assign (Local 0) (ReadField (Copy (Local 2)) "Counter<Int>" "n")
                ]
            clone = (progMain base)
                { fnName = "<Counter as Clone>::clone<Int>", fnParams = [Local 1], fnBorrowed = [Local 1], fnReturns = Just ty
                , fnLocals = Map.fromList [(Local 0, LocalDecl ty Nothing), (Local 1, LocalDecl ty Nothing), (Local 2, LocalDecl TInt Nothing), (Local 3, LocalDecl TInt Nothing)]
                , fnBlocks = Map.singleton (BlockId 0) (BasicBlock body Return)
                }
            program = base{progTypes = Map.singleton "Counter<Int>" (StructDecl [("n", TInt)]), progFunctions = Map.singleton (fnName clone) clone}
         in testAssertEq (runOwned program) (Right (Just (MInt expected)))
    clonedMembers =
        let node = TNamed "Node" []
            kids = TList node
            leaf = CData "Node" [("n", CInt 3), ("kids", CList [])]
            base = mainProgram [(Local 0, TInt), (Local 1, node), (Local 2, node), (Local 3, kids), (Local 4, node)]
                [ Assign (Local 1) (Use (Const (CData "Node" [("n", CInt 7), ("kids", CList [leaf])])))
                , Assign (Local 2) (CopyOf (Copy (Local 1)))
                , Peek (Local 3) (ReadField (Copy (Local 2)) "Node" "kids")
                , Peek (Local 4) (ListOp Get [Copy (Local 3), Const (CInt 0)])
                , Assign (Local 0) (ReadField (Copy (Local 4)) "Node" "n")
                , Drop (Local 2), Drop (Local 1)
                ]
            clone = (progMain base)
                { fnName = "<Node as Clone>::clone", fnParams = [Local 1], fnBorrowed = [Local 1], fnReturns = Just node
                , fnLocals = Map.fromList [(Local 0, LocalDecl node Nothing), (Local 1, LocalDecl node Nothing), (Local 2, LocalDecl node Nothing), (Local 3, LocalDecl TInt Nothing), (Local 4, LocalDecl TInt Nothing), (Local 5, LocalDecl kids Nothing)]
                , fnBlocks = Map.singleton (BlockId 0) (BasicBlock
                    [ Assign (Local 2) (CopyOf (Copy (Local 1)))
                    , Peek (Local 3) (ReadField (Copy (Local 2)) "Node" "n")
                    , Assign (Local 4) (BinaryOp Add (Copy (Local 3)) (Const (CInt 1)))
                    , Assign (Local 5) (TakeField (Local 2) "Node" "kids")
                    , Assign (Local 0) (MakeData "Node" [("n", Copy (Local 4)), ("kids", Move (Local 5))])
                    ] Return)
                }
         in base{progTypes = Map.singleton "Node" (StructDecl [("n", TInt), ("kids", kids)]), progFunctions = Map.singleton (fnName clone) clone}
    heap = TBox (TArrayOf TInt SizeAny)
    rejects name ty stmts expected =
        let base = mainProgram [(Local 1, ty), (Local 2, TRef ty), (Local 3, TInt)] []
            reader = (progMain base){fnName = "read", fnParams = [Local 1], fnBorrowed = [Local 1], fnReturns = Just TInt, fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl ty Nothing)], fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (Use (Const (CInt 0)))] Return)}
            main = (progMain base){fnBlocks = Map.fromList [(BlockId 0, BasicBlock stmts (Call (Const (CFn "read")) [Copy (Local 2)] (Local 3) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]}
            program = base{progMain = main, progFunctions = Map.singleton "read" reader}
         in testCase name (case runOwned program of Left error -> testAssertTrue (expected `isInfixOf` error); Right _ -> Just "the heap model accepted an invalid reference")

borrowedRootTests :: [Test]
borrowedRootTests =
    [ testCase "a borrow reads its owner and indexes" (testAssertTrue (roles (Borrow (Local 1) [RefIndex (Copy (Local 2))] False) == [(Copy (Local 1), Read), (Copy (Local 2), Read)]))
    , testCase "a field stays in its owner through the reference's last use" $
        own [(Local 1, TNamed "Holder" []), (Local 2, TRef list), (Local 3, list), (Local 4, TInt), (Local 5, list)]
                [ (BlockId 0, BasicBlock
                    [ Assign (Local 2) (Borrow (Local 1) [RefField "Holder" "xs"] False)
                    , Assign (Local 3) (ReadField (Copy (Local 1)) "Holder" "xs")
                    , Assign (Local 4) (ListOp Length [Copy (Local 3)])
                    , Assign (Local 5) (Deref (Copy (Local 2)))
                    , Assign (Local 0) (ListOp Length [Copy (Local 5)])
                    ] Return)
                ]
          $ \fn -> testAssertEq [() | BasicBlock stmts _ <- Map.elems (fnBlocks fn), Assign _ (TakeField (Local 1) "Holder" "xs") <- stmts] []
    , testCase "an owner is replaced after a reference call across blocks" $
        own [(Local 1, list), (Local 2, TRef list), (Local 3, TInt)]
                [ (BlockId 0, BasicBlock [Assign (Local 2) (Borrow (Local 1) [] False)] (Call (Const (CFn "noop")) [] (Local 3) (BlockId 1)))
                , (BlockId 1, BasicBlock [] (Call (Const (CFn "dup")) [Copy (Local 2)] (Local 1) (BlockId 2)))
                , (BlockId 2, BasicBlock [Assign (Local 0) (ListOp Length [Copy (Local 1)])] Return)
                ]
          $ \fn -> testAssertTrue (any (\block -> case blockTerminator block of Call (Const (CFn "dup")) _ dest _ -> dest /= Local 1; _ -> False) (Map.elems (fnBlocks fn)))
    , testCase "reference reassignment releases the previous owner" $
        own [(Local 1, list), (Local 2, list), (Local 3, TRef list), (Local 4, list), (Local 5, list)]
                [ (BlockId 0, BasicBlock
                    [ Assign (Local 3) (Borrow (Local 1) [] False)
                    , Assign (Local 3) (Borrow (Local 2) [] False)
                    , Assign (Local 4) (Use (Copy (Local 1)))
                    , Assign (Local 5) (Deref (Copy (Local 3)))
                    , Assign (Local 0) (ListOp Length [Copy (Local 5)])
                    ] Return)
                ]
          $ \fn -> testAssertTrue (any (\stmt -> case stmt of Assign (Local 4) (Use (Move (Local 1))) -> True; _ -> False) [stmt | BasicBlock stmts _ <- Map.elems (fnBlocks fn), stmt <- stmts])
    , testCase "a reference through a non-reference view keeps the original field live" $
        own [(Local 1, TNamed "Holder" []), (Local 2, list), (Local 3, TRef list), (Local 4, list), (Local 5, TInt), (Local 6, list)]
                [ (BlockId 0, BasicBlock
                    [ Assign (Local 2) (ReadField (Copy (Local 1)) "Holder" "xs")
                    , Assign (Local 3) (Borrow (Local 2) [] False)
                    , Assign (Local 4) (ReadField (Copy (Local 1)) "Holder" "xs")
                    , Assign (Local 5) (ListOp Length [Copy (Local 4)])
                    , Assign (Local 6) (Deref (Copy (Local 3)))
                    , Assign (Local 0) (ListOp Length [Copy (Local 6)])
                    ] Return)
                ]
          $ \fn -> testAssertEq [() | BasicBlock stmts _ <- Map.elems (fnBlocks fn), Assign _ (TakeField (Local 1) "Holder" "xs") <- stmts] []
    , testCase "a disjoint field may still be taken while a scalar field is borrowed" $
        own [(Local 1, TNamed "Holder" []), (Local 2, TRef TInt), (Local 3, list), (Local 4, TInt)]
                [ (BlockId 0, BasicBlock
                    [ Assign (Local 2) (Borrow (Local 1) [RefField "Holder" "n"] False)
                    , Assign (Local 3) (ReadField (Copy (Local 1)) "Holder" "xs")
                    , Assign (Local 4) (Deref (Copy (Local 2)))
                    , Assign (Local 0) (Use (Copy (Local 4)))
                    ] Return)
                ]
          $ \fn -> testAssertTrue (any (\stmt -> case stmt of Assign (Local 3) (TakeField (Local 1) "Holder" "xs") -> True; _ -> False) [stmt | BasicBlock stmts _ <- Map.elems (fnBlocks fn), stmt <- stmts])
    , testCase "a reborrow keeps the old owner after its parent reference is reassigned" $
        own [(Local 1, list), (Local 2, list), (Local 3, TRef list), (Local 4, TRef list), (Local 5, list), (Local 6, list)]
                [ (BlockId 0, BasicBlock
                    [ Assign (Local 3) (Borrow (Local 1) [] False)
                    , Assign (Local 4) (Borrow (Local 3) [] False)
                    , Assign (Local 3) (Borrow (Local 2) [] False)
                    , Assign (Local 5) (Use (Copy (Local 2)))
                    , Assign (Local 6) (Deref (Copy (Local 4)))
                    , Assign (Local 0) (ListOp Length [Copy (Local 6)])
                    ] Return)
                ]
          $ \fn -> testAssertTrue (any (\stmt -> case stmt of Assign (Local 5) (Use (Move (Local 2))) -> True; _ -> False) [stmt | BasicBlock stmts _ <- Map.elems (fnBlocks fn), stmt <- stmts])
    , testCase "a late successor reference use keeps its owner field live" $
        own [(Local 1, TNamed "Holder" []), (Local 2, TRef list), (Local 3, list), (Local 4, list)]
                ([ (BlockId 0, BasicBlock [Assign (Local 2) (Borrow (Local 1) [RefField "Holder" "xs"] False)] (Goto (BlockId 1)))
                 , (BlockId 1, BasicBlock [Assign (Local 3) (ReadField (Copy (Local 1)) "Holder" "xs")] (Goto (BlockId 2)))
                 ] ++ [(BlockId i, BasicBlock [] (Goto (BlockId (i + 1)))) | i <- [2 .. 11]]
                   ++ [(BlockId 12, BasicBlock [Assign (Local 4) (Deref (Copy (Local 2))), Assign (Local 0) (ListOp Length [Copy (Local 4)])] Return)])
          $ \fn -> testAssertEq [() | BasicBlock stmts _ <- Map.elems (fnBlocks fn), Assign _ (TakeField (Local 1) "Holder" "xs") <- stmts] []
    , testCase "a changed loop entry propagates both reborrow owners to its successor" $
        own [(Local 1, list), (Local 2, list), (Local 3, TRef list), (Local 4, TRef list), (Local 5, list), (Local 6, list)]
                [ (BlockId 0, BasicBlock [Assign (Local 3) (Borrow (Local 1) [] False)] (Goto (BlockId 1)))
                , (BlockId 1, BasicBlock [Assign (Local 4) (Borrow (Local 3) [] False), Assign (Local 3) (Borrow (Local 2) [] False)] (SwitchBool (Const (CBool False)) (BlockId 1) (BlockId 2)))
                , (BlockId 2, BasicBlock [Assign (Local 5) (Use (Copy (Local 2))), Assign (Local 6) (Deref (Copy (Local 4))), Assign (Local 0) (ListOp Length [Copy (Local 6)])] Return)
                ]
          $ \fn ->
            let stmts = [stmt | BasicBlock statements _ <- Map.elems (fnBlocks fn), stmt <- statements]
             in testAssertTrue (any (\stmt -> case stmt of Assign _ (CopyOf (Copy (Local 2))) -> True; _ -> False) stmts
            && not (any (\stmt -> case stmt of Assign (Local 5) (Use (Move (Local 2))) -> True; _ -> False) stmts))
    ]
  where
    list = TNamed "List" [ArgType TInt]
    own locals blocks check =
        let stub = progMain (mainProgram [] [])
            fn = stub{fnName = "loan", fnParams = [Local 1] ++ [Local 2 | lookup (Local 2) locals == Just list], fnReturns = Just TInt, fnLocals = Map.fromList ((Local 0, LocalDecl TInt Nothing) : [(l, LocalDecl ty Nothing) | (l, ty) <- locals]), fnBlocks = Map.fromList blocks}
            dup = stub{fnName = "dup", fnParams = [Local 1], fnBorrowed = [Local 1], fnReturns = Just list, fnLocals = Map.fromList [(Local 0, LocalDecl list Nothing), (Local 1, LocalDecl list Nothing)], fnBlocks = Map.singleton (BlockId 0) (BasicBlock [Assign (Local 0) (CopyOf (Copy (Local 1)))] Return)}
            program = (mainProgram [] []){progTypes = Map.fromList [("Holder", StructDecl [("xs", list), ("n", TInt)]), ("List<Int>", StructDecl [("addr", TAddr TInt), ("len", TInt), ("cap", TInt)])], progFunctions = Map.fromList [("loan", fn), ("dup", dup)]}
         in case insertOwnership program of
                Error e -> Just e
                Ok owned -> check (progFunctions owned Map.! "loan")

-- The programs that have arrays are not run on the model of the heap, which holds the values of the heap (a program with arrays and
-- nothing else is checked structurally by the plan tests)
usesArrays :: String -> Bool
usesArrays source = any (`isInfixOf` source) ["Array<", "Array::", "array(", "#["]

withOwnership :: Program -> (Program -> TestResult) -> TestResult
withOwnership program check = case insertOwnership program of
    Error e -> Just e
    Ok owned -> check owned

stateJoinTests :: [Test]
stateJoinTests =
    [ testCase "equal live branch states keep one whole drop" $
        withOwnership (branchProgram True [] []) $ \owned ->
            testAssertEq (runOwned owned) (Right (Just (MInt 9)))
            `orElseT` testAssertEq (length [() | block <- Map.elems (fnBlocks (progMain owned)), Drop (Local 1) <- blockStatements block]) 1
    , testCase "equal empty branch states do not add a return drop" $
        withOwnership (branchProgram True [Drop (Local 1)] [Drop (Local 1)]) $ \owned ->
            testAssertEq (runOwned owned) (Right (Just (MInt 9)))
            `orElseT` testAssertEq [() | Drop (Local 1) <- blockStatements (fnBlocks (progMain owned) Map.! BlockId 3)] []
    , testCase "different branch states still guard the empty path" (mixed True)
    , testCase "different branch states still free the live path" (mixed False)
    , testCase "equal partial-field states retain empty-field overrides" $
        let list = TNamed "List" [ArgType TInt]
            base = mainProgram [(Local 0, TInt), (Local 1, TNamed "Holder" []), (Local 2, list)] []
            fn = (progMain base){fnReturns = Just TInt, fnBlocks = Map.fromList
                [ (BlockId 0, BasicBlock [Assign (Local 1) (Use (Const (CData "Holder" [("xs", CList [CInt 1]), ("ys", CList [CInt 2, CInt 3])]))), Assign (Local 2) (ReadField (Copy (Local 1)) "Holder" "xs")] (SwitchBool (Const (CBool True)) (BlockId 1) (BlockId 2)))
                , (BlockId 1, BasicBlock [] (Goto (BlockId 3)))
                , (BlockId 2, BasicBlock [] (Goto (BlockId 3)))
                , (BlockId 3, BasicBlock [Assign (Local 0) (ListOp Length [Copy (Local 2)])] Return)
                ]}
         in withOwnership base{progTypes = Map.singleton "Holder" (StructDecl [("xs", list), ("ys", list)]), progMain = fn} $ \owned ->
                testAssertEq (runOwned owned) (Right (Just (MInt 1)))
    ]
  where
    orElseT Nothing next = next
    orElseT failure _ = failure
    branchProgram condition left right =
        let list = TNamed "List" [ArgType TInt]
            base = mainProgram [(Local 0, TInt), (Local 1, list)] []
         in base{progMain = (progMain base){fnReturns = Just TInt, fnBlocks = Map.fromList
            [ (BlockId 0, BasicBlock [Assign (Local 1) (Use (Const (CList [CInt 7])))] (SwitchBool (Const (CBool condition)) (BlockId 1) (BlockId 2)))
            , (BlockId 1, BasicBlock left (Goto (BlockId 3)))
            , (BlockId 2, BasicBlock right (Goto (BlockId 3)))
            , (BlockId 3, BasicBlock [Assign (Local 0) (Use (Const (CInt 9)))] Return)
            ]}}
    mixed condition =
        withOwnership (branchProgram condition [Drop (Local 1)] []) $ \owned ->
            testAssertEq (runOwned owned) (Right (Just (MInt 9)))
            `orElseT` testAssertTrue (any ((== TBool) . localType) (Map.elems (fnLocals (progMain owned))))

testOwnership :: Test
testOwnership =
    TestList
        "testOwnership"
        [ TestList "examples" [TestCase path (onFile path) | path <- ownershipExamples]
        , TestCase "array examples are excluded: the heap model has no array model (blind spot)" . pure $
            testAssertTrue (all (`notElem` ownershipExamples) arrayExamples && not (null arrayExamples) && usesArrays "a = array(3, 0); return get(a, 0);")
        , TestCase "array ergonomics retain native coverage and stay out of the arrayless heap model" . pure $
            testAssertTrue (not (null arrayErgonomicsPrograms) && all (`elem` validatedPrograms) arrayErgonomicsPrograms && all (`notElem` ownershipPrograms) arrayErgonomicsPrograms)
        , TestList "programs" ([TestCase name (onSource name source) | (name, source) <- ownershipPrograms] ++ [TestCase name (onProgram name <$> programFromFiles ownRoleEntry files) | (name, files) <- ownRolePrograms])
        , TestList "boxed Clone" [TestCase name (onSource name source) | (name, source, _, _) <- boxedClonePrograms]
        , TestList "reference writes" [TestCase name (onSource name source) | (name, source) <- referenceWritePrograms]
        , TestList "lent parts" [TestCase name (onSource name source) | (name, source) <- lentPartPrograms]
        , TestList "without validation" [TestCase name (pure (onLowered name source)) | (name, source) <- unvalidatedPrograms]
        , TestList "the plan" planTests
        , TestList "no copy of a value with a drop" noDropCopyTests
        , TestList "the ownership pass's own refusals" passSafetyTests
        , TestList "MirMoves and the ownership pass agree on what holds a value with a drop" agreementTests
        , TestList "what a part may be read after" windowTests
        , TestList "reference heap model" referenceModelTests
        , TestList "borrowed roots" borrowedRootTests
        , TestList "joined ownership states" stateJoinTests
        , TestList "mistakes the model finds" mistakeTests
        ]
