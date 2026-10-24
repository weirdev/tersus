module TestOwnership
    ( testOwnership
    , runOwned
    ) where

import Data.List (isInfixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Mir
import MirEval (MirValue (..), runProgram)
import MirOwnership (insertOwnership)
import MirVerify (verifyProgram)
import MirLower (lowerProgram)
import Parse (parseStatementBlock)
import Pipeline
import TestNative (nativeExamples, unvalidatedPrograms, validatedPrograms)
import TersusTypes (Name, Rel (..), Type (..), Variable)
import TestHarness
import Utils

-- Ownership: MirOwnership says who owns each value of the heap, and native code frees values and changes lists in place on
-- the strength of it. A wrong answer here is a value used after it was freed, freed twice, or changed under a reader, which
-- the executor of the MIR cannot show, so these tests run the result on a model of the heap that fails on all of those, and
-- on a value that is still there when the program ends.

-- The model of the heap

data Val = VI Integer | VB Bool | VP Int | VNull | VF Name
    deriving (Eq, Show)

data Obj = OList [Val] | OData Name [(Variable, Val)]

data Cell = Cell {cellGeneration :: Int, cellObject :: Obj}

-- What a local holds, and for a local that only looks at a value, which one and how it was when it looked
data Slot = Slot {slotValue :: Val, slotLook :: Maybe (Int, Int)}

data Frame = Frame {frameFunction :: Function, frameSlots :: Map Local Slot}

data St = St
    { stHeap :: Map Int Cell
    , stNext :: Int
    , stFrames :: [Frame]
    , stFuel :: Int
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
freeTree _ = return ()

children :: Obj -> [Val]
children (OList vs) = vs
children (OData _ fs) = map snd fs

cloneVal :: Val -> M Val
cloneVal (VP a) = do
    c <- cell a
    case cellObject c of
        OList vs -> mapM cloneVal vs >>= alloc . OList
        OData name fs -> mapM (\(f, v) -> (,) f <$> cloneVal v) fs >>= alloc . OData name
cloneVal v = return v

-- How many places own the value: locals (not those that only look) and slots of values
owners :: Int -> M Int
owners a = do
    s <- getSt
    let fromFrames = length [() | f <- stFrames s, Slot (VP b) Nothing <- Map.elems (frameSlots f), b == a]
        fromHeap = length [() | c <- Map.elems (stHeap s), VP b <- children (cellObject c), b == a]
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

localHeap :: Frame -> Local -> Bool
localHeap f l = maybe False (heapType . localType) (Map.lookup l (fnLocals (frameFunction f)))

heapType :: Type -> Bool
heapType TList{} = True
heapType TBox{} = True
heapType TNamed{} = True
heapType TVariant{} = True
heapType _ = False

-- Reading a local: it has to hold something, that has to be there, and be as it was when a local that only looks saw it
readLocal :: Local -> M Val
readLocal l = do
    f <- currentFrame
    case Map.lookup l (frameSlots f) of
        Nothing -> failM ("read of " ++ show l ++ " before it is given a value")
        Just (Slot VNull _) -> failM ("use of " ++ show l ++ " after it was moved from")
        Just (Slot v look) -> do
            case v of
                VP a -> do
                    c <- cell a
                    case look of
                        Just (_, g) | g /= cellGeneration c -> failM (show l ++ " looks at a value that changed")
                        _ -> return ()
                _ -> return ()
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
constant (CData name fs) = mapM (\(f, c) -> (,) f <$> constant c) fs >>= alloc . OData name
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
        OData name fs -> PD name <$> mapM (\(f, v) -> (,) f <$> toPure v) fs

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
object v = failM ("not a value of the heap: " ++ show v)

-- Running the MIR

evalRvalue :: Rvalue -> M Val
evalRvalue rv =
    case rv of
        Use o -> readOperand o
        -- (a Box is the object that a struct or an enum is, until they are held inline)
        MakeBox o -> readOperand o
        Unbox o -> readOperand o
        BinaryOp op a b -> do
            x <- readOperand a
            y <- readOperand b
            binary op x y
        MakeList os -> mapM readOperand os >>= alloc . OList
        MakeData name fs -> mapM (\(f, o) -> (,) f <$> readOperand o) fs >>= alloc . OData name
        ReadField o name field -> do
            (_, obj) <- readOperand o >>= object
            case obj of
                OData actual fs
                    | actual == name -> maybe (failM ("no field " ++ field)) return (lookup field fs)
                    | otherwise -> failM ("expected a " ++ name ++ ", got a " ++ actual)
                _ -> failM "a field of a list"
        IsVariant o name -> do
            (_, obj) <- readOperand o >>= object
            case obj of
                OData actual _ -> return (VB (actual == name))
                _ -> failM "is of a list"
        AsVariant o _ -> readOperand o
        Clone o -> readOperand o >>= cloneVal
        TakeField l name field -> do
            f <- currentFrame
            case Map.lookup l (frameSlots f) of
                Just (Slot _ (Just _)) -> failM ("a field is taken from " ++ show l ++ ", which only looks")
                _ -> return ()
            (a, obj) <- readLocal l >>= object
            case obj of
                OData actual fs
                    | actual == name -> case lookup field fs of
                        Nothing -> failM ("no field " ++ field)
                        Just VNull -> failM ("field " ++ field ++ " was taken twice")
                        Just v -> do
                            setObject a (OData actual [(g, if g == field then VNull else w) | (g, w) <- fs])
                            return v
                    | otherwise -> failM ("expected a " ++ name ++ ", got a " ++ actual)
                _ -> failM "a field of a list"
        ListOp op os -> listOp op os

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
        _ -> failM ("list operation on the wrong operands: " ++ show op)
  where
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
            look <- case v of
                VP a -> do
                    c <- cell a
                    return (Just (a, cellGeneration c))
                _ -> return Nothing
            putSlot d (Slot v look)
        Assign d rv -> do
            v <- evalRvalue rv
            f <- currentFrame
            if localHeap f d
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
    s <- getSt
    putSt s{stFrames = Frame fn (Map.fromList [(p, Slot v Nothing) | (p, v) <- zip (fnParams fn) args]) : stFrames s}
    result <- runBlock program fn (BlockId 0)
    s' <- getSt
    case stFrames s' of
        f : rest -> do
            let leftover = [l | (l, Slot v Nothing) <- Map.toList (frameSlots f), v /= VNull, l /= Local 0, localHeap f l]
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
                Just (Slot old Nothing) | localHeap f dest -> freeTree old
                _ -> return ()
            putSlot dest (Slot v Nothing)
            runBlock program fn next

-- Runs the whole program on the model, and checks that nothing is left on the heap
runOwned :: Program -> Either String (Maybe MirValue)
runOwned program =
    case runM go (St Map.empty 0 [] 1000000) of
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
    let owned = insertOwnership program
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
        withOwned "l = []; i = 0; while i < 4 [{ affirm i >= 0; }] shrinks 4 - i { l = push(l, i); i = i + 1; }; return size(l);" (\t -> testAssertEq (count "clone" t) 0 `orElseT` testAssertTrue ("Push(move _1" `isInfixOf` t))
    , -- an array is held inline and has nothing in it to free, so the pass leaves it alone (the model of the heap holds values of the
      -- heap, and the programs with arrays are not run on it)
      TestCase "an array is not owned: no copy, no move, nothing to free" . pure $
        withOwned "a = array(3, 0); b = set(a, 0, 1); return get(b, 0) + get(a, 1) + size(a);" (\t -> testAssertEq (count "clone" t, count "move" t, count "drop" t, count "peek" t) (0, 0, 0, 0))
    , TestCase "an array beside a list: only the list is freed" . pure $
        withOwned "l = [1]; a = array(2, 0); a = set(a, 1, size(l)); return get(a, 1);" (\t -> testAssertEq (count "clone" t, count "drop" t) (0, 1))
    , TestCase "a list that is used after a push is copied once" . pure $
        withOwned "x = [1]; y = push(x, 2); return size(x) + size(y);" (\t -> testAssertEq (count "clone" t) 1)
    , TestCase "a match takes the fields out of the value" . pure $
        withOwned "enum T { Leaf, Node { l: Box<T>, v: Int, r: Box<T> } }; fn sum(t: Box<T>) -> Int shrinks t { return match t { T::Leaf => 0, T::Node { l: l, v: v, r: r } => v + sum(l) + sum(r) }; }; return sum(Box::new(T::Node { l: Box::new(T::Leaf), v: 1, r: Box::new(T::Leaf) }));" (\t -> let f = functionText "sum" t in testAssertEq (count "clone" f, count "take " f) (0, 2))
    , TestCase "a part that is only read is looked at" . pure $
        withOwned "rows = [[1], [2, 3]]; return size(get(rows, 1));" (\t -> testAssertEq (count "clone" t, count "peek Get" t) (0, 1))
    , TestCase "a part that is kept is copied" . pure $
        withOwned "rows = [[1], [2, 3]]; row = get(rows, 1); rows = set(rows, 0, row); return size(row);" (\t -> testAssertTrue (count "clone" t >= 1))
    , TestCase "a call with an argument that is used after it copies the argument" . pure $
        withOwned "fn n(l: List<Int>) -> Int { return size(l); }; l = [1, 2]; return n(l) + n(l);" (\t -> testAssertEq (count "clone" (functionText "main" t)) 1)
    , TestCase "a cast is read from the value itself" . pure $
        withOwned "enum S { A { r: Int }, C }; x = S::A { r: 4 }; return (x as S::A).r;" (\t -> testAssertEq (count "clone" t) 0 `orElseT` testAssertTrue (not (" as S::A;" `isInfixOf` t)))
    , TestCase "a parameter that is assigned a part is freed first" . pure $
        withOwned "fn f(row: List<Int>, rows: List<List<Int>>) -> Int [{ affirm size(rows) > 0; }] [{ }] { row = get(rows, 0); return size(row); }; return f([1], [[2, 3]]);" (\t -> let f = functionText "f" t in testAssertEq (count "peek" f, count "clone" f) (1, 1) `orElseT` testAssertTrue ("drop _1" `isInfixOf` f))
    , TestCase "a copy of a parameter is one copy" . pure $
        withOwned "fn f(a: List<Int>) -> List<Int> [{ affirm size(a) > 0; }] [{ }] { out = a; out = set(out, 0, size(a)); return out; }; return f([5]);" (\t -> testAssertEq (count "clone" (functionText "f" t)) 1)
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
            [ (Local 1, TList TInt)
            , (Local 2, TList TInt)
            , (Local 3, TInt)
            , (Local 5, TList TInt)
            ]
            stmts

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
                , fnSpec = emptySpec
                }
        }

-- Lowering never puts a change of a list between a part of it and the read of that part in one block, so the rule that a part
-- is copied when it would be read after that is checked on MIR written by hand
windowTests :: [Test]
windowTests =
    [ TestCase "a part is copied when what it is part of changes before it is read" . pure $
        let program = windowProgram [Assign (Local 1) (Use (Const (CList [CList [CInt 1, CInt 2], CList [CInt 3]]))), Assign (Local 2) (ListOp Get [Copy (Local 1), Const (CInt 0)]), Assign (Local 1) (ListOp Set [Copy (Local 1), Const (CInt 0), Const (CList [CInt 9])]), Assign (Local 3) (ListOp Length [Copy (Local 2)])]
         in sameOnModel "the part" program `orElseT` testAssertTrue (count "clone" (renderProgram (insertOwnership program)) >= 1)
    , TestCase "a part is looked at when nothing changes before it is read" . pure $
        let program = windowProgram [Assign (Local 1) (Use (Const (CList [CList [CInt 1, CInt 2], CList [CInt 3]]))), Assign (Local 2) (ListOp Get [Copy (Local 1), Const (CInt 0)]), Assign (Local 3) (ListOp Length [Copy (Local 2)]), Assign (Local 1) (ListOp Set [Copy (Local 1), Const (CInt 0), Const (CList [CInt 9])])]
         in sameOnModel "the part" program `orElseT` testAssertEq (count "peek" (renderProgram (insertOwnership program)), count "clone" (renderProgram (insertOwnership program))) (1, 0)
    ]
  where
    windowProgram = mainProgram [(Local 1, TList (TList TInt)), (Local 2, TList TInt), (Local 3, TInt)]
    orElseT Nothing b = b
    orElseT a _ = a

-- The programs that have arrays are not run on the model of the heap, which holds the values of the heap (a program with arrays and
-- nothing else is checked structurally by the plan tests)
usesArrays :: String -> Bool
usesArrays source = any (`isInfixOf` source) ["Array<", "array(", "#["]

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
