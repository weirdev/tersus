{-# LANGUAGE PatternSynonyms #-}

module TestMirCopies (testMirCopies) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map

import Mir
import MirCopies (makeCopies)
import Syntax (Proof (..), ValidationStatement (..), Value (..))
import TestHarness
import Types (Arg (..), BuiltinFunct (..), Rel (..), Size (..), Type (..), pattern TBox, pattern TList)
import StdLib (builtinFunct)
import Utils

-- The copy step (MirCopies) on MIR written by hand: the copies a program names are made from the functions with bounds,
-- with their types and bounded sizes put in, their references named for the copies, and their calls through a bound made
-- what a copy calls for the type.
testMirCopies :: Test
testMirCopies =
    TestList
        "testMirCopies"
        [ testCase "a program with no functions with bounds is unchanged" (testAssertEq (makeCopies plain) (Ok plain))
        , testCase "a copy has the types put in and the function with bounds is dropped" substituted
        , testCase "a bounded size is a constant in the copy and stays a parameter" boundedSize
        , testCase "a struct instance the body builds is named for the copy's types" structNamed
        , testCase "two references to one copy make it once" deduplicated
        , testCase "a lifted function is copied with its function" liftedCopied
        , testCase "references in calls, proofs and environments name the copies" referencesRenamed
        , testCaseNamedSeq "calls through a bound" resolutionRows
        , testCase "the check of an impl function is copied with it" companionCopied
        , testCase "a copy for a bigger type at each call is refused" growthRefused
        , testCase "an array a copy makes too big for a frame is the call's refusal" frameRefused
        , testCase "the marker of a function with bounds goes, and its copies are defined where the program starts" markersReplaced
        , testCase "a variadic copy has a parameter for each argument, lent with the pack, and size(args) is their number" packParameters
        , testCase "a copy for no arguments has no parameters" emptyPack
        , testCase "get(args, k) is the parameter at k, in blocks and environments" literalElement
        , testCase "get(args, k) out of range is the obligation k < N" outOfRange
        , testCase "a branch the copy does not take goes with its references and obligations" pruning
        , testCase "a loop over the pack is a copy of its body for each argument" unrolled
        , testCase "a forall over the pack in a contract is a fact for each argument" packForall
        , testCase "the blocks after an element read out of range go" outOfRangePruned
        , testCase "a variadic copy's locals are checked against the frame" variadicFrame
        , testCase "a forwarded slice is spread into the callee's arguments, whose copy is the one a direct call names" forwardSpread
        , testCase "a forwarded slice out of range is the obligation on its bounds" forwardOutOfRange
        ]

blockOf :: [Statement] -> Terminator -> Map.Map BlockId BasicBlock
blockOf stmts term = Map.singleton (BlockId 0) (BasicBlock stmts term)

-- A function whose parameters are its first locals
function :: String -> [(Type, String)] -> Type -> [(Type, Maybe String)] -> Map.Map BlockId BasicBlock -> Function
function name params result others blocks =
    Function
        { fnName = name
        , fnParams = [Local i | i <- [1 .. length params]]
        , fnReturns = Just result
        , fnLocals = Map.fromList ((Local 0, LocalDecl result Nothing) : [(Local i, LocalDecl t (Just n)) | (i, (t, n)) <- zip [1 ..] params] ++ [(Local i, LocalDecl t n) | (i, (t, n)) <- zip [length params + 1 ..] others])
        , fnBlocks = blocks
        , fnSizeParams = []
        , fnTypeParams = []
        , fnBorrowed = []
        , fnMutBorrowed = []
        , fnFrom = []
        , fnSpec = emptySpec
        }

mainCalling :: [Statement] -> [(String, Type)] -> Function
mainCalling ghosts calls =
    (function "main" [] TInt [(t, Nothing) | (_, t) <- calls] (Map.fromList (zip (map BlockId [0 ..]) blocks))){fnReturns = Nothing}
  where
    blocks =
        [ BasicBlock (if i == 0 then ghosts else []) (Call (Const (CFn callee)) [Const (CInt 1)] (Local (i + 1)) (BlockId (i + 1)))
        | (i, (callee, _)) <- zip [0 ..] calls
        ]
            ++ [BasicBlock [] Return]

program :: [Function] -> Function -> [(String, BoundedFn)] -> [(String, (String, [Arg]))] -> Program
program fns main' bounded instances = Program Map.empty (Map.fromList [(fnName f, f) | f <- fns]) main' Map.empty Map.empty (Map.fromList bounded) (Map.fromList instances)

plain :: Program
plain = program [function "f" [(TInt, "x")] TInt [] (blockOf [Assign (Local 0) (Use (Copy (Local 1)))] Return)] (mainCalling [] [("f", TInt)]) [] []

-- fn ident<T: Eq>(x: T) -> T { return x; }
ident :: Function
ident = (function "ident" [(TParam "T", "x")] (TParam "T") [] (blockOf [Assign (Local 0) (Use (Copy (Local 1)))] Return)){fnTypeParams = ["T"]}

withCopies :: Program -> (Program -> TestResult) -> TestResult
withCopies p check = case makeCopies p of
    Ok out -> check out
    Error e -> Just ("the copy step failed: " ++ e)

substituted :: TestResult
substituted = withCopies (program [ident] (mainCalling [] [("ident[Int]", TInt)]) [("ident", BoundedFn [] [] [] [])] [("ident[Int]", ("ident", [ArgType TInt]))]) $ \out ->
    case Map.lookup "ident[Int]" (progFunctions out) of
        Just copy
            | Map.member "ident" (progFunctions out) -> Just "the function with bounds is still there"
            | fnTypeParams copy /= [] -> Just "the copy has type parameters"
            | map localType (Map.elems (fnLocals copy)) /= [TInt, TInt] -> Just ("the copy's locals are " ++ show (Map.elems (fnLocals copy)))
            | not (Map.null (progBounded out) && Map.null (progInstances out)) -> Just "the tables were kept"
            | otherwise -> Nothing
        Nothing -> Just ("no copy: " ++ show (Map.keys (progFunctions out)))

-- fn wrap<T: Eq>(x: T) -> Pair<T> { return Pair<T> { a: x }; }
structNamed :: TestResult
structNamed = withCopies (program [wrap] (mainCalling [] [("wrap[Int]", TNamed "Pair" [ArgType TInt])]) [("wrap", BoundedFn [] [] [] [])] [("wrap[Int]", ("wrap", [ArgType TInt]))]) $ \out ->
    case blockStatements <$> (Map.lookup "wrap[Int]" (progFunctions out) >>= Map.lookup (BlockId 0) . fnBlocks) of
        Just [Assign (Local 0) (MakeData "Pair<Int>" [("a", Copy (Local 1))])] -> Nothing
        other -> Just (show other)
  where
    pair = TNamed "Pair" [ArgType (TParam "T")]
    wrap = (function "wrap" [(TParam "T", "x")] pair [] (blockOf [Assign (Local 0) (MakeData "Pair<'T>" [("a", Copy (Local 1))])] Return)){fnTypeParams = ["T"]}

-- fn sized<T: Feed<Array<Int, n>>, n>(a: Array<T, n>, n: Int) -> Int { return n; }
sizedFn :: Function
sizedFn =
    (function "sized" [(TArrayOf (TParam "T") (SizeParam "n"), "a"), (TInt, "n")] TInt [] (blockOf [Assign (Local 0) (Use (Copy (Local 2)))] Return))
        { fnTypeParams = ["T"]
        , fnSizeParams = ["n"]
        , fnSpec = emptySpec{specEnv = Map.fromList [("n", Copy (Local 2))]}
        }

boundedSize :: TestResult
boundedSize = withCopies (program [sizedFn] (mainCalling [] [("sized[Bool, 3]", TInt)]) [("sized", BoundedFn ["n"] [] [] [])] [("sized[Bool, 3]", ("sized", [ArgType TBool, ArgSize (SizeConst 3)]))]) $ \out ->
    case Map.lookup "sized[Bool, 3]" (progFunctions out) of
        Just copy
            | fnSizeParams copy /= ["n"] || length (fnParams copy) /= 2 -> Just "the size parameter was dropped"
            | (localType <$> Map.lookup (Local 1) (fnLocals copy)) /= Just (TArrayOf TBool (SizeConst 3)) -> Just "the size was not put in the type"
            | Map.lookup "n" (specEnv (fnSpec copy)) /= Just (Const (CInt 3)) -> Just "the size is not a constant where a proof reads it"
            | (blockStatements <$> Map.lookup (BlockId 0) (fnBlocks copy)) /= Just [Assign (Local 0) (Use (Const (CInt 3)))] -> Just "a read of the size is not the constant"
            | otherwise -> Nothing
        Nothing -> Just "no copy"

deduplicated :: TestResult
deduplicated = withCopies (program [ident] (mainCalling [] [("ident[Int]", TInt), ("again", TInt)]) [("ident", BoundedFn [] [] [] [])] [("ident[Int]", ("ident", [ArgType TInt])), ("again", ("ident", [ArgType TInt]))]) $ \out ->
    let copies = [n | n <- Map.keys (progFunctions out), n `elem` ["ident[Int]", "again"]]
     in if length copies == 1 then Nothing else Just ("copies: " ++ show copies)

-- fn outer<T: Eq>(x: T) -> T { fn inner(y: T) -> T { return y; }; return inner(x); }
liftedCopied :: TestResult
liftedCopied = withCopies (program [outer, inner] (mainCalling [] [("outer[Int]", TInt)]) [("outer", BoundedFn [] [] ["outer::inner"] [])] [("outer[Int]", ("outer", [ArgType TInt]))]) $ \out ->
    case (Map.lookup "outer[Int]" (progFunctions out), Map.lookup "outer[Int]::inner" (progFunctions out)) of
        (Just copy, Just innerCopy)
            | Map.member "outer::inner" (progFunctions out) -> Just "the lifted function with type parameters is still there"
            | (blockTerminator <$> Map.lookup (BlockId 0) (fnBlocks copy)) /= Just (Call (Const (CFn "outer[Int]::inner")) [Copy (Local 1)] (Local 0) (BlockId 1)) -> Just "the call of the lifted function is not of its copy"
            | (localType <$> Map.lookup (Local 1) (fnLocals innerCopy)) /= Just TInt -> Just "the lifted copy has no types put in"
            | otherwise -> Nothing
        _ -> Just ("functions: " ++ show (Map.keys (progFunctions out)))
  where
    outer = (function "outer" [(TParam "T", "x")] (TParam "T") [] (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "outer::inner")) [Copy (Local 1)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)])){fnTypeParams = ["T"]}
    inner = (function "outer::inner" [(TParam "T", "y")] (TParam "T") [] (blockOf [Assign (Local 0) (Use (Copy (Local 1)))] Return))

-- fn caller<T: Eq>(x: T) -> T [{ affirm ident['T](x) = x; }] { return ident['T](x); }
referencesRenamed :: TestResult
referencesRenamed = withCopies (program [ident, caller] (mainCalling [] [("caller[Bool]", TBool)]) [("ident", BoundedFn [] [] [] []), ("caller", BoundedFn [] [] [] [])] [("caller[Bool]", ("caller", [ArgType TBool])), ("ident['T]", ("ident", [ArgType (TParam "T")]))]) $ \out ->
    case Map.lookup "caller[Bool]" (progFunctions out) of
        Just copy
            | not (Map.member "ident[Bool]" (progFunctions out)) -> Just ("the copy the body names was not made: " ++ show (Map.keys (progFunctions out)))
            | (blockTerminator <$> Map.lookup (BlockId 0) (fnBlocks copy)) /= Just (Call (Const (CFn "ident[Bool]")) [Copy (Local 1)] (Local 0) (BlockId 1)) -> Just "the call is not of the copy"
            | specRequires (fnSpec copy) /= [ProofAssert (FApp (CTerm (builtinFunct (Rel Eq))) [FApp (ATerm "ident[Bool]") [ATerm "x"], ATerm "x"])] -> Just ("the proof is " ++ show (specRequires (fnSpec copy)))
            | Map.member "ident['T]" (specEnv (fnSpec copy)) -> Just "the environment keeps the name the unit gave the copy"
            | Map.lookup "ident[Bool]" (specEnv (fnSpec copy)) /= Just (Const (CFn "ident[Bool]")) -> Just "the environment does not have the copy"
            | otherwise -> Nothing
        Nothing -> Just "no copy"
  where
    caller =
        (function "caller" [(TParam "T", "x")] (TParam "T") [] (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "ident['T]")) [Copy (Local 1)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]))
            { fnTypeParams = ["T"]
            , fnSpec = emptySpec{specRequires = [ProofAssert (FApp (CTerm (builtinFunct (Rel Eq))) [FApp (ATerm "ident['T]") [ATerm "x"], ATerm "x"])], specEnv = Map.fromList [("x", Copy (Local 1)), ("ident['T]", Const (CFn "ident['T]"))]}
            }

-- fn through<T: Tr>(x: T) -> R { return <$param T as Tr>::g(x); } for each row of the table
boundCall :: String -> Type -> Type -> Function
boundCall callee param result =
    (function "through" [(param, "x")] result [] (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn callee)) [Copy (Local 1)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)])){fnTypeParams = ["T"]}

rowCopy :: [Function] -> [(String, BoundedFn)] -> Function -> Type -> (Function -> Program -> TestResult) -> TestResult
rowCopy others bounded through t check = withCopies (program (through : others) (mainCalling [] [("through[x]", TInt)]) (("through", BoundedFn [] [] [] []) : bounded) [("through[x]", ("through", [ArgType t]))]) $ \out ->
    case Map.lookup "through[x]" (progFunctions out) of
        Just copy -> check copy out
        Nothing -> Just "no copy"

lastBlock :: Function -> Maybe BasicBlock
lastBlock copy = Map.lookup (BlockId 0) (fnBlocks copy)

resolutionRows :: [(String, TestResult)]
resolutionRows =
    [ ("Clone of a word is a copy of it", rowCopy [] [] (boundCall "<$param T as Clone>::clone" (TParam "T") (TParam "T")) TInt $ \copy _ -> case lastBlock copy of
        Just (BasicBlock [Assign (Local 0) (CopyOf (Copy (Local 1)))] Return) -> Nothing
        other -> Just (show other))
    , ("Eq of words is a comparison", rowCopy [] [] (eqCall "<$param T as Eq>::eq") TByte $ \copy _ -> case lastBlock copy of
        Just (BasicBlock stmts Return) | Assign (Local 0) (BinaryOp (Compare Eq) (Copy (Local 1)) (Copy (Local 2))) `elem` stmts -> Nothing
        other -> Just (show other))
    , ("Eq of Boxes of arrays of no size calls eqBoxedArrays", rowCopy [eqBoxed] [("eqBoxedArrays", BoundedFn [] [] [] [])] (eqCall "<$param T as Eq>::eq") (TBox (TArrayOf TInt SizeAny)) $ \copy out -> case lastBlock copy of
        Just (BasicBlock _ (Call (Const (CFn "eqBoxedArrays[Int]")) _ _ _)) | Map.member "eqBoxedArrays[Int]" (progFunctions out) -> Nothing
        other -> Just (show other))
    , ("a reference argument is read where it is to", rowCopy [] [] (boundCall "<$param T as Clone>::clone" (TRef (TParam "T")) (TParam "T")) TInt $ \copy _ -> case lastBlock copy of
        Just (BasicBlock [Assign tmp (Deref (Copy (Local 1))), Assign (Local 0) (CopyOf (Copy tmp'))] Return) | tmp == tmp' -> Nothing
        other -> Just (show other))
    , ("a sequence function of a list that no impl gives is the builtin", rowCopy [] [] (boundCall "<$param T as Sequence>::size" (TRef (TParam "T")) TInt) (TList TInt) $ \copy _ -> case lastBlock copy of
        Just (BasicBlock stmts Return) | any (\s -> case s of Assign (Local 0) (ListOp Length [_]) -> True; _ -> False) stmts -> Nothing
        other -> Just (show other))
    , ("a sequence function in a proof is the builtin's term", rowCopy [] [] ((boundCall "<$param T as Sequence>::size" (TRef (TParam "T")) TInt){fnSpec = emptySpec{specEnsures = [ProofAssert (FApp (ATerm "<$param T as Sequence>::size") [ATerm "x"])]}}) (TList TInt) $ \copy _ ->
        if specEnsures (fnSpec copy) == [ProofAssert (FApp (CTerm (builtinFunct Size)) [ATerm "x"])] then Nothing else Just (show (specEnsures (fnSpec copy))))
    , ("a sequence function of the library's traits is the builtin, though the list has the impl", withCopies (program [boundCall "<$param T as Sequence>::size" (TRef (TParam "T")) TInt, listSize] (mainCalling [] [("through[x]", TInt)]) [("through", BoundedFn [] [] [] [])] [("through[x]", ("through", [ArgType (TList TInt)])), ("<$param T as Sequence>::size", ("$builtin", []))]) $ \out -> case Map.lookup "through[x]" (progFunctions out) >>= lastBlock of
        Just (BasicBlock stmts Return) | any (\s -> case s of Assign (Local 0) (ListOp Length [_]) -> True; _ -> False) stmts -> Nothing
        other -> Just (show other))
    , ("Clone of a struct with a Clone impl calls it", rowCopy [cloneS] [] (boundCall "<$param T as Clone>::clone" (TParam "T") (TParam "T")) (TNamed "S" []) $ \copy _ -> case lastBlock copy of
        Just (BasicBlock _ (Call (Const (CFn "<S as Clone>::clone")) [Copy (Local 1)] (Local 0) _)) -> Nothing
        other -> Just (show other))
    , ("a clone of a value of a type parameter in a lifted function calls the Clone impl of the type", withCopies (program [outer, inner, cloneS] (mainCalling [] [("outer[S]", TNamed "S" [])]) [("outer", BoundedFn [] [] ["outer::inner"] [])] [("outer[S]", ("outer", [ArgType (TNamed "S" [])]))]) $ \out -> case fnBlocks <$> Map.lookup "outer[S]::inner" (progFunctions out) of
        Just blocks | [(BlockId 0, BasicBlock [] (Call (Const (CFn "<S as Clone>::clone")) [Copy (Local 1)] (Local 0) next)), (next', BasicBlock [Assign (Local 0) (Use (Copy (Local 0)))] Return)] <- Map.toList blocks, next == next' -> Nothing
        other -> Just (show other))
    , ("a clone of what a Box holds is given a borrow of it, and the value is not read", rowCopy [cloneS] [] unboxClone (TNamed "S" []) $ \copy _ -> case Map.lookup (BlockId 0) (fnBlocks copy) of
        Just (BasicBlock [Assign r (Borrow (Local 1) [] False)] (Call (Const (CFn "<S as Clone>::clone")) [Copy r'] (Local 0) _)) | r == r' -> Nothing
        other -> Just (show other))
    , ("and a Box of an array is given the array", rowCopy [arrayClone] [("<Array as Clone>::clone", BoundedFn [] [] [] [])] unboxClone (TArrayOf TInt (SizeConst 2)) $ \copy out -> case Map.lookup (BlockId 0) (fnBlocks copy) of
        Just (BasicBlock [Assign (Local 2) (Unbox (Copy (Local 1)))] (Call (Const (CFn "<Array as Clone>::clone[Int]")) [Copy (Local 2), Const (CInt 2)] (Local 0) _)) | Map.member "<Array as Clone>::clone[Int]" (progFunctions out) -> Nothing
        other -> Just (show other))
    , ("an impl with sizes is given the sizes of the arguments", rowCopy [arraySize] [] (boundCall "<$param T as Sequence>::size" (TRef (TParam "T")) TInt) (TArrayOf TInt (SizeConst 3)) $ \copy _ -> case lastBlock copy of
        Just (BasicBlock _ (Call (Const (CFn "<Array as Sequence>::size")) [Copy (Local 1), Const (CInt 3)] (Local 0) _)) -> Nothing
        other -> Just (show other))
    , ("a sequence function of a list that an impl gives is the impl's", rowCopy [listSize] [] (boundCall "<$param T as Sequence>::size" (TRef (TParam "T")) TInt) (TList TInt) $ \copy _ -> case lastBlock copy of
        Just (BasicBlock _ (Call (Const (CFn "<List as Sequence>::size")) _ _ _)) -> Nothing
        other -> Just (show other))
    , ("anything else calls the type's impl", rowCopy [hashInt] [] (boundCall "<$param T as Hash>::hash" (TRef (TParam "T")) TInt) TInt $ \copy _ -> case lastBlock copy of
        Just (BasicBlock _ (Call (Const (CFn "<Int as Hash>::hash")) [Copy (Local 1)] (Local 0) _)) -> Nothing
        other -> Just (show other))
    , ("an impl with bounds is copied for the types the call gives it", rowCopy [listEq] [("<List as Eq>::eq", BoundedFn [] [] [] [])] (eqCall "<$param T as Eq>::eq") (TList TBool) $ \copy out -> case lastBlock copy of
        Just (BasicBlock _ (Call (Const (CFn "<List as Eq>::eq[Bool]")) _ _ _)) | Map.member "<List as Eq>::eq[Bool]" (progFunctions out) -> Nothing
        other -> Just (show other ++ show (Map.keys (progFunctions out))))
    , ("a type with no impl of the trait is an internal error", testAssertErrorContains "internal compiler error" (makeCopies (program [boundCall "<$param T as Hash>::hash" (TRef (TParam "T")) TInt] (mainCalling [] [("through[x]", TInt)]) [("through", BoundedFn [] [] [] [])] [("through[x]", ("through", [ArgType TBool]))])))
    ]
  where
    eqCall callee = (function "through" [(TParam "T", "a"), (TParam "T", "b")] TBool [] (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn callee)) [Copy (Local 1), Copy (Local 2)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)])){fnTypeParams = ["T"]}
    eqBoxed = (function "eqBoxedArrays" [(TRef (TBox (TArrayOf (TParam "T") SizeAny)), "a"), (TRef (TBox (TArrayOf (TParam "T") SizeAny)), "b")] TBool [] (blockOf [Assign (Local 0) (Use (Const (CBool True)))] Return)){fnTypeParams = ["T"]}
    outer = (function "outer" [(TParam "T", "x")] (TParam "T") [] (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "outer::inner")) [Copy (Local 1)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)])){fnTypeParams = ["T"]}
    inner = (function "outer::inner" [(TParam "T", "y")] (TParam "T") [] (blockOf [Assign (Local 0) (CopyOf (Copy (Local 1))), Assign (Local 0) (Use (Copy (Local 0)))] Return))
    unboxClone = (function "through" [(TBox (TParam "T"), "b")] (TParam "T") [] (Map.fromList [(BlockId 0, BasicBlock [Assign (Local 2) (Unbox (Copy (Local 1))), Assign (Local 0) (CopyOf (Copy (Local 2)))] Return)])){fnTypeParams = ["T"], fnLocals = Map.fromList [(Local 0, LocalDecl (TParam "T") Nothing), (Local 1, LocalDecl (TBox (TParam "T")) (Just "b")), (Local 2, LocalDecl (TParam "T") Nothing)]}
    arrayClone = (function "<Array as Clone>::clone" [(TArrayOf (TParam "T") (SizeParam "n"), "self"), (TInt, "n")] (TArrayOf (TParam "T") (SizeParam "n")) [] (blockOf [Assign (Local 0) (Use (Copy (Local 1)))] Return)){fnTypeParams = ["T"], fnSizeParams = ["n"]}
    cloneS = function "<S as Clone>::clone" [(TNamed "S" [], "self")] (TNamed "S" []) [] (blockOf [Assign (Local 0) (Use (Copy (Local 1)))] Return)
    arraySize = (function "<Array as Sequence>::size" [(TArrayOf (TParam "T") (SizeParam "n"), "self"), (TInt, "n")] TInt [] (blockOf [Assign (Local 0) (Use (Copy (Local 2)))] Return)){fnTypeParams = ["T"], fnSizeParams = ["n"]}
    listSize = (function "<List as Sequence>::size" [(TRef (TList (TParam "T")), "self")] TInt [] (blockOf [Assign (Local 0) (Use (Const (CInt 0)))] Return)){fnTypeParams = ["T"]}
    hashInt = function "<Int as Hash>::hash" [(TRef TInt, "self")] TInt [] (blockOf [Assign (Local 0) (Use (Const (CInt 0)))] Return)
    listEq = (function "<List as Eq>::eq" [(TRef (TList (TParam "T")), "self"), (TRef (TList (TParam "T")), "other")] TBool [] (blockOf [Assign (Local 0) (Use (Const (CBool True)))] Return)){fnTypeParams = ["T"]}

companionCopied :: TestResult
companionCopied = withCopies (program [listEq, check] (mainCalling [] [("<List as Eq>::eq[Int]", TBool)]) [("<List as Eq>::eq", BoundedFn [] [] [] []), ("Eq for List::eq", BoundedFn [] [] [] [])] [("<List as Eq>::eq[Int]", ("<List as Eq>::eq", [ArgType TInt])), ("<List as Eq>::eq['T]", ("<List as Eq>::eq", [ArgType (TParam "T")]))]) $ \out ->
    if Map.member "Eq for List::eq[Int]" (progFunctions out) then Nothing else Just (show (Map.keys (progFunctions out)))
  where
    listEq = (function "<List as Eq>::eq" [(TRef (TList (TParam "T")), "self"), (TRef (TList (TParam "T")), "other")] TBool [] (blockOf [Assign (Local 0) (Use (Const (CBool True)))] Return)){fnTypeParams = ["T"]}
    check = (function "Eq for List::eq" [(TRef (TList (TParam "T")), "self"), (TRef (TList (TParam "T")), "other")] TBool [] (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "<List as Eq>::eq['T]")) [Copy (Local 1), Copy (Local 2)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)])){fnTypeParams = ["T"]}

-- fn grow<T: Eq>(x: T) -> Int { return grow[List<'T>](push([], x)); }
growthRefused :: TestResult
growthRefused = testAssertErrorContains "Type error: grow calls itself with the types List<List<Int>>, which are not those it is made for" (makeCopies (program [grow] (mainCalling [] [("grow[List<Int>]", TInt)]) [("grow", BoundedFn [] [] [] [])] [("grow[List<Int>]", ("grow", [ArgType (TList TInt)])), ("grow[List<'T>]", ("grow", [ArgType (TList (TParam "T"))]))]))
  where
    grow = (function "grow" [(TParam "T", "x")] TInt [(TList (TParam "T"), Nothing)] (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "grow[List<'T>]")) [Copy (Local 2)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)])){fnTypeParams = ["T"]}

-- fn big<T: Clone>(x: T) -> Int { a = array(3000, x); return 0; } for an array of 3
frameRefused :: TestResult
frameRefused = testAssertErrorContains "Type error: big cannot be made as big[Array<Int, 3>] for this call: Array<Array<Int, 3>, 3000> takes 9000 words, more than the 8192 that an array held in a frame can have" (makeCopies (program [big] (mainCalling [] [("big[Array<Int, 3>]", TInt)]) [("big", BoundedFn [] [] [] [])] [("big[Array<Int, 3>]", ("big", [ArgType (TArrayOf TInt (SizeConst 3))]))]))
  where
    big = (function "big" [(TParam "T", "x")] TInt [(TArrayOf (TParam "T") (SizeConst 3000), Just "a")] (blockOf [Assign (Local 0) (Use (Const (CInt 0)))] Return)){fnTypeParams = ["T"]}

markersReplaced :: TestResult
markersReplaced = withCopies (program [ident] (mainCalling [Ghost Map.empty (GhostFunction "ident" "ident" True)] [("ident[Int]", TInt), ("ident[Bool]", TBool)]) [("ident", BoundedFn [] [] [] [])] [("ident[Int]", ("ident", [ArgType TInt])), ("ident[Bool]", ("ident", [ArgType TBool]))]) $ \out ->
    let markers = [n | BasicBlock stmts _ <- Map.elems (fnBlocks (progMain out)), Ghost _ (GhostFunction n _ _) <- stmts]
     in if markers == ["ident[Bool]", "ident[Int]"] then Nothing else Just ("markers: " ++ show markers)

-- A variadic function as lowering writes it (MirLower.lowerPackLoop): the pack is its parameter _1 of type ..T, lent
variadic :: String -> Type -> Map.Map BlockId BasicBlock -> [(Type, Maybe String)] -> Function
variadic name result blocks others = (function name [(TParam "..T", "args")] result others blocks){fnTypeParams = ["..T"], fnBorrowed = [Local 1]}

-- fn sz<..T>(args: &..T) -> Int { return size(args); }
sizeOfPack :: Function
sizeOfPack = variadic "sz" TInt (blockOf [Assign (Local 0) (ListOp Length [Copy (Local 1)])] Return) []

packProgram :: [Function] -> [(String, Type)] -> [(String, (String, [Arg]))] -> [String] -> Program
packProgram fns calls instances bounded = program fns (mainCalling [] calls) [(b, BoundedFn [] [] [] loops) | b <- bounded, let loops = if b == "count" then [countLoop] else []] instances

copyOf :: Program -> String -> (Function -> TestResult) -> TestResult
copyOf p name check = withCopies p $ \out -> case Map.lookup name (progFunctions out) of
    Just copy -> check copy
    Nothing -> Just ("no copy " ++ name ++ ": " ++ show (Map.keys (progFunctions out)))

packParameters :: TestResult
packParameters = copyOf (packProgram [sizeOfPack] [("sz[Int, Bool, Int]", TInt), ("sz[]", TInt)] [("sz[Int, Bool, Int]", ("sz", map ArgType [TInt, TBool, TInt])), ("sz[]", ("sz", []))] ["sz"]) "sz[Int, Bool, Int]" $ \copy ->
    let params = [(localType d, localName d) | p <- fnParams copy, Just d <- [Map.lookup p (fnLocals copy)]]
     in if params /= [(TInt, Just "args 0"), (TBool, Just "args 1"), (TInt, Just "args 2")] then Just ("the parameters are " ++ show params)
        else if fnBorrowed copy /= fnParams copy then Just "a lent pack's parameters are not all lent"
        else if fnTypeParams copy /= [] then Just ("type parameters " ++ show (fnTypeParams copy))
        else if (blockStatements <$> Map.lookup (BlockId 0) (fnBlocks copy)) /= Just [Assign (Local 0) (Use (Const (CInt 3)))] then Just "size(args) is not the number of arguments"
        else Nothing

emptyPack :: TestResult
emptyPack = copyOf (packProgram [sizeOfPack] [("sz[]", TInt)] [("sz[]", ("sz", []))] ["sz"]) "sz[]" $ \copy ->
    if null (fnParams copy) && (blockStatements <$> Map.lookup (BlockId 0) (fnBlocks copy)) == Just [Assign (Local 0) (Use (Const (CInt 0)))] then Nothing else Just (show copy)

-- fn second<..T>(args: ..T) -> Int { x = get(args, 1); return size(args); }, by value
secondOfPack :: Function
secondOfPack = (variadic "second" TInt (blockOf [Assign (Local 2) (ReadField (Copy (Local 1)) "$pack" "1"), Ghost (Map.fromList [("x", Copy (Local 2)), ("args", Copy (Local 1))]) (GhostValidation (ProofAssert (FApp (CTerm (builtinFunct (Rel Eq))) [ATerm "x", ATerm "x"]))), Assign (Local 0) (Use (Const (CInt 0)))] Return) [(TParam "..T#1", Just "x")]){fnBorrowed = []}

literalElement :: TestResult
literalElement = copyOf (packProgram [secondOfPack] [("second[Int, Bool]", TInt)] [("second[Int, Bool]", ("second", map ArgType [TInt, TBool]))] ["second"]) "second[Int, Bool]" $ \copy -> case Map.lookup (BlockId 0) (fnBlocks copy) of
    Just (BasicBlock [Ghost env _, Assign (Local 0) _] Return)
        | Map.lookup "x" env /= Just (Copy (fnParams copy !! 1)) -> Just ("the element is not the parameter: " ++ show env)
        | Map.member "args" env || Map.lookup "args 0" env /= Just (Copy (head (fnParams copy))) -> Just ("the environment names the pack: " ++ show env)
        | Map.member (Local 2) (fnLocals copy) -> Just "the local of the element is kept"
        | (localType <$> Map.lookup (fnParams copy !! 1) (fnLocals copy)) /= Just TBool -> Just "the element's type is not the argument's"
        | not (null (fnBorrowed copy)) -> Just "a pack taken by value is lent"
        | otherwise -> Nothing
    other -> Just (show other)

outOfRange :: TestResult
outOfRange = copyOf (packProgram [secondOfPack] [("second[Int]", TInt)] [("second[Int]", ("second", [ArgType TInt]))] ["second"]) "second[Int]" $ \copy -> case Map.lookup (BlockId 0) (fnBlocks copy) of
    Just (BasicBlock [Ghost names (GhostValidation (ProofAssert (FApp (CTerm f) [ATerm index, ATerm count]))), Ghost _ (GhostValidation (Assume _))] Return)
        | show f == show (builtinFunct (Rel Lt)), Map.lookup index names == Just (Const (CInt 1)), Map.lookup count names == Just (Const (CInt 1)), "get(args, ...)" `isInfixOf` index -> Nothing
    other -> Just (show other)

-- fn show1<..T: Tr>(args: &..T) -> Int { if size(args) > 0 { return show['..T#0](get(args, 0)); }; return 0; }
pruned :: Function
pruned =
    variadic "pick" TInt (Map.fromList
        [ (BlockId 0, BasicBlock [Assign (Local 2) (ListOp Length [Copy (Local 1)]), Assign (Local 3) (BinaryOp (Compare Gt) (Copy (Local 2)) (Const (CInt 0)))] (SwitchBool (Copy (Local 3)) (BlockId 1) (BlockId 2)))
        , (BlockId 1, BasicBlock [Assign (Local 4) (ReadField (Copy (Local 1)) "$pack" "0")] (Call (Const (CFn "ident['..T#0]")) [Copy (Local 4)] (Local 0) (BlockId 3)))
        , (BlockId 2, BasicBlock [Assign (Local 0) (Use (Const (CInt 0)))] (Goto (BlockId 3)))
        , (BlockId 3, BasicBlock [] Return)
        ]) [(TInt, Nothing), (TBool, Nothing), (TParam "..T#0", Nothing)]

pruning :: TestResult
pruning = withCopies (program [pruned, ident] (mainCalling [] [("pick[]", TInt), ("pick[Bool]", TInt)]) [("pick", BoundedFn [] [] [] []), ("ident", BoundedFn [] [] [] [])] [("pick[]", ("pick", [])), ("pick[Bool]", ("pick", [ArgType TBool])), ("ident['..T#0]", ("ident", [ArgType (TParam "..T#0")]))]) $ \out ->
    case (Map.lookup "pick[]" (progFunctions out), Map.lookup "pick[Bool]" (progFunctions out)) of
        (Just none, Just one)
            | Map.member "ident[Int]" (progFunctions out) -> Just "a copy for a type no call gives"
            | or [True | BasicBlock ss _ <- Map.elems (fnBlocks none), Ghost _ (GhostValidation (Assume _)) <- ss] -> Just "the branch the empty pack does not take has an obligation"
            | or [True | BasicBlock _ (Call{}) <- Map.elems (fnBlocks none)] -> Just "the branch the empty pack does not take is kept"
            | not (or [True | BasicBlock _ (Call (Const (CFn "ident[Bool]")) [Copy p] _ _) <- Map.elems (fnBlocks one), p == head (fnParams one)]) -> Just ("the call of the copy for the argument is missing: " ++ show (fnBlocks one))
            | not (Map.member "ident[Bool]" (progFunctions out)) -> Just "the copy the branch names was not made"
            | otherwise -> Nothing
        _ -> Just (show (Map.keys (progFunctions out)))

-- fn count<..T: Tr>(args: &..T) -> Int { n = 0; for a in &args { n = n + Tr::f(a); }; return n; }, as lowering writes it
countFn :: Function
countFn =
    variadic "count" TInt (Map.fromList
        [ (BlockId 0, BasicBlock [Assign (Local 8) (Use (Const (CInt 0))), Assign (Local 2) (Use (Const (CInt 0))), Assign (Local 3) (ListOp Length [Copy (Local 1)]), Assign (Local 4) (Use (Copy (Local 2)))] (Goto (BlockId 1)))
        , (BlockId 1, BasicBlock [Assign (Local 5) (BinaryOp (Compare Lt) (Copy (Local 4)) (Copy (Local 3)))] (SwitchBool (Copy (Local 5)) (BlockId 2) (BlockId 3)))
        , (BlockId 2, BasicBlock [Assign (Local 6) (ListOp Mir.Get [Copy (Local 1), Copy (Local 4)])] (Call (Const (CFn "<$param ..T@0 as Tr>::f")) [Copy (Local 6)] (Local 7) (BlockId 4)))
        , (BlockId 4, BasicBlock [Assign (Local 8) (BinaryOp Add (Copy (Local 8)) (Copy (Local 7))), Assign (Local 4) (BinaryOp Add (Copy (Local 4)) (Const (CInt 1)))] (Goto (BlockId 1)))
        , (BlockId 3, BasicBlock [Assign (Local 0) (Use (Copy (Local 8)))] Return)
        ]) [(TInt, Nothing), (TInt, Nothing), (TInt, Just "$index"), (TBool, Nothing), (TParam "..T@0", Just "a"), (TInt, Nothing), (TInt, Just "n")]

countLoop :: PackLoop
countLoop = PackLoop (BlockId 1) (BlockId 2) (BlockId 3) [BlockId 2, BlockId 4] [Local 7] (Local 4) (Local 6) "..T@0" (Local 2) (Local 3) Nothing

trImpl :: String -> Type -> Function
trImpl owner t = function ("<" ++ owner ++ " as Tr>::f") [(t, "self")] TInt [] (blockOf [Assign (Local 0) (Use (Const (CInt 1)))] Return)

unrolled :: TestResult
unrolled = copyOf (packProgram [countFn, trImpl "Int" TInt, trImpl "Bool" TBool] [("count[Int, Bool]", TInt)] [("count[Int, Bool]", ("count", map ArgType [TInt, TBool])), ("<$param ..T@0 as Tr>::f", ("", []))] ["count"]) "count[Int, Bool]" $ \copy ->
    let calls = [(f, args, d) | BasicBlock _ (Call (Const (CFn f)) args d _) <- Map.elems (fnBlocks copy)]
        params = fnParams copy
     in case calls of
            [("<Int as Tr>::f", [Copy a], d1), ("<Bool as Tr>::f", [Copy b], d2)]
                | [a, b] /= params -> Just ("the iterations do not read the arguments in order: " ++ show calls)
                | d1 == d2 -> Just "the iterations share a local"
                | or [True | BasicBlock ss _ <- Map.elems (fnBlocks copy), Assign _ (ListOp Mir.Get _) <- ss] -> Just "an element read is left"
                | or [True | BasicBlock _ (SwitchBool{}) <- Map.elems (fnBlocks copy)] -> Just "the loop's test is left"
                | otherwise -> Nothing
            _ -> Just ("the calls are " ++ show calls)

-- [{ affirm forall i in 0..size(args): Tr::f(get(args, i)) >= 0; affirm size(args) >= 1; }]
forallFn :: Function
forallFn = (variadic "all" TInt (blockOf [Assign (Local 0) (Use (Const (CInt 0)))] Return) []){fnSpec = emptySpec{specRequires = [forallFact, sizeFact], specEnv = Map.fromList [("args", Copy (Local 1))]}}
  where
    rel r = CTerm (builtinFunct (Rel r))
    forallFact = ProofAssert (Forall "i" [FApp (rel LtEq) [CTerm (VInt 0), BVar "i"], FApp (rel Lt) [BVar "i", FApp (CTerm (builtinFunct Size)) [ATerm "args"]]] (FApp (rel GtEq) [FApp (ATerm "<$param ..T@1 as Tr>::f") [FApp (CTerm (builtinFunct Types.Get)) [ATerm "args", BVar "i"]], CTerm (VInt 0)]))
    sizeFact = ProofAssert (FApp (rel GtEq) [FApp (CTerm (builtinFunct Size)) [ATerm "args"], CTerm (VInt 1)])

packForall :: TestResult
packForall = copyOf (packProgram [forallFn, trImpl "Int" TInt, trImpl "Bool" TBool] [("all[Int, Bool]", TInt)] [("all[Int, Bool]", ("all", map ArgType [TInt, TBool])), ("<$param ..T@1 as Tr>::f", ("", []))] ["all"]) "all[Int, Bool]" $ \copy ->
    let rel r = CTerm (builtinFunct (Rel r))
        fact owner k = ProofAssert (FApp (rel GtEq) [FApp (ATerm ("<" ++ owner ++ " as Tr>::f")) [ATerm ("args " ++ show (k :: Int))], CTerm (VInt 0)])
        expected = [fact "Int" 0, fact "Bool" 1, ProofAssert (FApp (rel GtEq) [CTerm (VInt 2), CTerm (VInt 1)])]
     in if specRequires (fnSpec copy) == expected then Nothing else Just (show (specRequires (fnSpec copy)))

-- fn after<..T>(args: ..T) -> Int { x = get(args, 1); return x; }, for one argument
outOfRangePruned :: TestResult
outOfRangePruned =
    let afterFn = (variadic "after" (TParam "..T#1") (Map.fromList [(BlockId 0, BasicBlock [Assign (Local 2) (ReadField (Copy (Local 1)) "$pack" "1")] (Goto (BlockId 1))), (BlockId 1, BasicBlock [Assign (Local 0) (Use (Copy (Local 2)))] Return)]) [(TParam "..T#1", Just "x")]){fnBorrowed = []}
     in copyOf (packProgram [afterFn] [("after[Int]", TInt)] [("after[Int]", ("after", [ArgType TInt]))] ["after"]) "after[Int]" $ \copy ->
            if Map.keys (fnBlocks copy) == [BlockId 0] then Nothing else Just ("blocks: " ++ show (fnBlocks copy))

-- fn big<..T: Clone>(args: &..T) -> Int { a = array(3000, get(args, 0)); return 0; }, for an array of 3
variadicFrame :: TestResult
variadicFrame =
    let bigFn = variadic "big" TInt (blockOf [Assign (Local 3) (ReadField (Copy (Local 1)) "$pack" "0"), Assign (Local 2) (ListOp Mir.NewArray [Const (CInt 3000), Copy (Local 3)]), Assign (Local 0) (Use (Const (CInt 0)))] Return) [(TArrayOf (TParam "..T#0") (SizeConst 3000), Just "a"), (TParam "..T#0", Nothing)]
     in testAssertErrorContains "Array<Array<Int, 3>, 3000> takes 9000 words" (makeCopies (packProgram [bigFn] [("big[Array<Int, 3>]", TInt)] [("big[Array<Int, 3>]", ("big", [ArgType (TArrayOf TInt (SizeConst 3))]))] ["big"]))

-- fn fw<..T>(args: &..T) -> Int { return sz(slice(args, 1, 3)); }, which lowering gives as sz['..T](args, 1, 3)
forwarder :: Integer -> Integer -> Function
forwarder lo hi = variadic "fw" TInt (Map.fromList [(BlockId 0, BasicBlock [] (Call (Const (CFn "sz['..T]")) [Copy (Local 1), Const (CInt lo), Const (CInt hi)] (Local 0) (BlockId 1))), (BlockId 1, BasicBlock [] Return)]) []

forwardProgram :: Integer -> Integer -> [(String, Type)] -> [(String, (String, [Arg]))] -> Program
forwardProgram lo hi calls instances = packProgram [sizeOfPack, forwarder lo hi] calls (("sz['..T]", ("sz", [ArgType (TParam "..T")])) : instances) ["sz", "fw"]

forwardSpread :: TestResult
forwardSpread =
    withCopies (forwardProgram 1 3 [("fw[Int, Bool, Int]", TInt), ("sz[Bool, Int]", TInt)] [("fw[Int, Bool, Int]", ("fw", map ArgType [TInt, TBool, TInt])), ("sz[Bool, Int]", ("sz", map ArgType [TBool, TInt]))]) $ \out ->
        case Map.lookup "fw[Int, Bool, Int]" (progFunctions out) of
            Nothing -> Just ("no copy of fw: " ++ show (Map.keys (progFunctions out)))
            Just copy -> case blockTerminator <$> Map.lookup (BlockId 0) (fnBlocks copy) of
                Just (Call (Const (CFn callee)) args _ _)
                    | callee /= "sz[Bool, Int]" -> Just ("the forward calls " ++ callee)
                    | [localName d | Copy l <- args, Just d <- [Map.lookup l (fnLocals copy)]] /= [Just "args 1", Just "args 2"] -> Just ("the forward gives " ++ show args)
                    | length [n | n <- Map.keys (progFunctions out), "sz[" `isPrefixOf` n] /= 1 -> Just ("copies of sz: " ++ show (Map.keys (progFunctions out)))
                    | otherwise -> Nothing
                other -> Just ("the block ends with " ++ show other)

forwardOutOfRange :: TestResult
forwardOutOfRange =
    copyOf (forwardProgram 0 2 [("fw[Int]", TInt)] [("fw[Int]", ("fw", [ArgType TInt]))]) "fw[Int]" $ \copy -> case Map.lookup (BlockId 0) (fnBlocks copy) of
        Just (BasicBlock [Ghost names (GhostValidation (ProofAssert (FApp (CTerm f) [ATerm end, ATerm count]))), Ghost _ (GhostValidation (Assume _))] Return)
            | show f == show (builtinFunct (Rel LtEq)), Map.lookup end names == Just (Const (CInt 2)), Map.lookup count names == Just (Const (CInt 1)), "slice(args, ...)" `isInfixOf` end -> Nothing
        other -> Just ("block 0 is " ++ show other)
