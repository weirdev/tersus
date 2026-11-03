{-# LANGUAGE PatternSynonyms #-}

module TestMirVerify (testMirVerify, testMirVerifyPrograms) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))

import Cli (World (..), noWorld, runProgramIn)
import Compile (lowerSource)
import Mir
import MirData (forNative, readProgram, writeProgram)
import MirHousekeeping (verifyProgram)
import MirOwnership (insertOwnership)
import MirLower (lowerProgram)
import Parse (parseStatementBlock)
import Pipeline (nativeProgram)
import PreludeSource (boxSource, listsSource)
import Types (Type (..), pattern TList, pattern TBox)
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, unvalidatedPrograms, validatedPrograms)
import Utils

-- The MIR housekeeping of REPLACING_HASKELL.md target 3, in Tersus (examples/mir/mir_verify/mir_verify.tersus): the check that a program
-- as MirData writes it is well formed (the shape, and the types of statements, switches and calls), run over the data of
-- a program. The verdict of each case below is the one the check has to give; the native sweep compares the verdict with
-- the one the host gives (MirHousekeeping, which runs this program), program by program. Ghost erasure is not here:
-- MirData.forNative has already erased what it would erase, and a data form that still held it would be needed to check that in Tersus.
testMirVerify :: Test
testMirVerify =
    TestList
        "testMirVerify"
        [ TestCase "constructor and block lookups borrow aggregates" borrowedLookups
        , TestList
            "interpreted"
            [ TestCase "a well formed program is accepted" (interpreted goodSource id True)
            , TestCase "a program with a list is accepted" (interpreted "xs = [1, 2, 3]; return size(xs) + first(xs);" id True)
            , TestCase "no entry block" (interpreted goodSource noEntryBlock False)
            , TestCase "a local of no known type" (interpreted goodSource varLocal False)
            , TestCase "a switch on an Int" (interpreted goodSource switchOnInt False)
            , TestCase "a call of a function that is not there" (interpreted goodSource unknownCall False)
            , TestCase "an unknown constructor reports its name" (interpretedWithMessage (Just "there is no constructor MissingCtor") constructorSource unknownConstructor False)
            , TestCase "a missing jump target reports its block" (interpretedWithMessage (Just "jumps to bb999999, which is not there") goodSource missingTarget False)
            , TestCase "an array with the same size parameter is accepted" (interpreted sizedSource id True)
            , TestCase "a named type that starts with a builtin's name is accepted" (interpreted integerSource id True)
            , TestCase "an instance with another array size is refused" (interpreted holderSource wrongHolderArg False)
            , TestCase "an array of lists that does not fit in a frame is refused" (interpreted "xs = array(3000, 0); return get(xs, 0);" arrayOfLists False)
            , TestCase "what is not the MIR is refused" refused
            ]
        , TestList "pre-erasure, interpreted"
            ( TestCase "raw lists and Boxes library" (rawInterpreted True rawLibrary)
                : [TestCase name (rawInterpreted expected (Ok text)) | (name, text, expected) <- blockCases]
            )
        , TestList "raw borrow protocol and structural metadata, interpreted"
            [TestCase name (rawInterpreted expected (Ok text)) | (name, text, expected) <- rawBorrowCases]
        , TestCase "Uninit function type round trips through MIR data" uninitRoundTrip
        , TestList "function-list identity, interpreted"
            [TestCase name (rawInterpreted expected input) | (name, input, expected) <- functionCases]
        , TestList "call metadata, interpreted"
            [TestCase name (rawInterpreted expected input) | (name, input, expected) <- callCases]
        , TestCase "pre-erasure and function-list cases, natively" rawNative
        , TestParallel
            "every example, natively"
            [TestCase path (readFile path >>= nativeCheck path) | path <- nativeExamples]
        ]

-- The validated programs of the sweep as a group of their own, so the suite's group processes balance: this sweep
-- and testMirEmit's were the longest groups, and a group is a process.
testMirVerifyPrograms :: Test
testMirVerifyPrograms =
    TestParallel
        "testMirVerifyPrograms"
        [TestCase name (nativeCheck name source) | (name, source) <- validatedPrograms]

borrowedLookups :: IO TestResult
borrowedLookups = do
    loaded <- validatedFromFile "examples/mir/mir_verify/mir_verify.tersus"
    pure $ case loaded of
        Error e -> Just e
        Ok program ->
            let owned = insertOwnership program
                check (name, owner, field, tableType, elementType) = case Map.lookup name (progFunctions owned) of
                    Nothing -> Just ("the verifier has no " ++ name ++ " function")
                    Just fn ->
                        let copied = [dest | block <- Map.elems (fnBlocks fn), Assign dest (ReadField _ actualOwner actualField) <- blockStatements block, actualOwner == owner, actualField == field, Just decl <- [Map.lookup dest (fnLocals fn)], localType decl == tableType]
                            elementCopies = [dest | Just raw <- [Map.lookup name (progFunctions program)], block <- Map.elems (fnBlocks raw), Assign dest (ListOp Get _) <- blockStatements block, Just decl <- [Map.lookup dest (fnLocals raw)], localType decl == elementType]
                         in if null (copied ++ elementCopies) then Nothing else Just (name ++ " clones its input aggregate into " ++ show (copied ++ elementCopies))
                targets = [("ctorInfo", "mir$reader$reader$Program", "types", TList (TNamed "mir$reader$reader$TypeDecl" []), TNamed "mir$reader$reader$TypeDecl" []), ("findBlock", "mir$reader$reader$Function", "blocks", TList (TNamed "mir$reader$reader$MirBlock" []), TNamed "mir$reader$reader$MirBlock" []), ("findLocal", "mir$reader$reader$Function", "locals", TList (TNamed "mir$reader$reader$LocalDecl" []), TNamed "mir$reader$reader$LocalDecl" [])]
                errors = [message | Just message <- map check targets]
             in if null errors then Nothing else Just (unlines errors)

goodSource :: String
goodSource = "fn double(n: Int) -> Int [{ }] [{ }] { return n + n; }; if double(2) = 4 { return 1; }; return 0;"

sizedSource :: String
sizedSource = "fn copyOf<n>(a: Array<Int, n>) -> Array<Int, n> [{ }] [{ }] { b = a; return b; }; xs = #[1, 2]; return size(copyOf(xs));"

integerSource :: String
integerSource = "struct Integer { n: Int }; struct Holder<T> { x: T }; fn take<T>(h: Holder<T>) -> Int [{ }] [{ }] { return 1; }; a = Holder<Integer> { x: Integer { n: 3 } }; return take(a);"

holderSource :: String
holderSource = "struct Holder<T> { x: T }; fn take2(h: Holder<Array<Int, 2>>) -> Int [{ }] [{ }] { return get(h.x, 0); }; a = Holder<Array<Int, 2>> { x: #[1, 2] }; b = Holder<Array<Int, 3>> { x: #[1, 2, 3] }; return take2(a);"

-- The verifier compiled once for every interpreted case: compiling it is the expensive part, and every case
-- runs the same program over a different input (the pattern of TestMirEmit's emitterProgram).
verifierProgram :: IO (Result Program String)
verifierProgram = programFromFile "examples/mir/mir_verify/mir_verify.tersus"

-- Whether the host's check accepts the program, as MirData writes it
referenceAccepts :: Program -> Bool
referenceAccepts program = case verifyProgram (forNative program) of
    Ok () -> True
    Error _ -> False

-- Run the verifier in the interpreter over the data of the mutated program, and compare its verdict with the one it has to give
interpreted :: String -> (Program -> Program) -> Bool -> IO TestResult
interpreted = interpretedWithMessage Nothing

interpretedWithMessage :: Maybe String -> String -> (Program -> Program) -> Bool -> IO TestResult
interpretedWithMessage message source mutate expected = do
    verifier <- verifierProgram
    ownedResult <- ownedOnce source
    pure $ case verifier of
        Error e -> Just ("the verifier does not compile: " ++ e)
        Ok verifierProgram -> case ownedResult of
            Error e -> Just e
            Ok owned ->
                let program = mutate owned
                    text = writeProgram program
                 in case runProgramIn noWorld{worldInput = text} verifierProgram of
                        Error e -> Just e
                        Ok ((output, errors), _)
                            | expected && sameText output "OK" && null errors -> Nothing
                            | not expected && output == "1" && not (null errors) && maybe True (`isInfixOf` errors) message -> Nothing
                            | otherwise -> Just ("expected " ++ verdict expected ++ ", got output " ++ show output ++ " and errors " ++ show errors ++ " for\n" ++ text)
  where
    verdict True = "acceptance"
    verdict False = "refusal"

rawLibrary :: Result String String
rawLibrary = mapResult writeProgram (lowerSource False (listsSource ++ "\n" ++ boxSource))

rawInterpreted :: Bool -> Result String String -> IO TestResult
rawInterpreted expected input = do
    verifier <- verifierProgram
    pure $ case input of
        Error e -> Just e
        Ok text -> case readProgram text of
            Error e -> Just ("the raw fixture does not read: " ++ e)
            Ok _ -> case verifier of
                Error e -> Just ("the verifier does not compile: " ++ e)
                Ok checker -> case runProgramIn noWorld{worldInput = text} checker of
                    Error e -> Just e
                    Ok ((output, errors), _)
                        | expected && sameText output "OK" && null errors -> Nothing
                        | not expected && output == "1" && not (null errors) && not ("not the MIR as data" `isInfixOf` errors) -> Nothing
                        | otherwise -> Just ("expected " ++ show expected ++ ", got output " ++ show output ++ " and errors " ++ show errors ++ " for\n" ++ text)

rawNative :: IO TestResult
rawNative = withVerifier $ \exe -> case rawLibrary of
    Error e -> pure (Just e)
    Ok library -> do
        failures <- mapM (check exe) (("raw lists and Boxes library", library, True) : blockCases ++ rawBorrowCases)
        functionFailures <- mapM (\(name, input, expected) -> case input of
            Error e -> pure (Just (name ++ ": " ++ e))
            Ok text -> check exe (name, text, expected)) (functionCases ++ callCases)
        pure $ case [failure | Just failure <- failures ++ functionFailures] of
            [] -> Nothing
            bad -> Just (unlines bad)
  where
    check exe (name, text, expected) = do
        (code, output, errors) <- runExecutableBytes exe [] text
        pure $
            if expected && code == ExitSuccess && sameText output "OK" && null errors
                || not expected && code == ExitSuccess && sameText output "1" && not (null errors) && not ("not the MIR as data" `isInfixOf` errors)
                then Nothing
                else Just (name ++ ": expected " ++ show expected ++ ", got " ++ show (code, output, errors))

callCases :: [(String, Result String String, Bool)]
callCases =
    [(name, mapResult writeProgram (lowerSource True source), True) | (name, source) <- sources]
        ++ [(name, mapResult (writeProgram . mutate) (lowerSource True source), False) | (name, source, mutate) <- negatives]
        ++ [(name, Ok (blockCall expected actual borrowed), accepted) | (name, expected, actual, borrowed, accepted) <- blocks]
        ++ [(name, Ok (derefFixture parameter borrowed result operand), False) | (name, parameter, borrowed, result, operand) <- badDerefs]
  where
    mutableSource = "fn take(n: &mut Int) -> Int { return 0; }; x = 1; return take(&mut x);"
    sources =
        [ ("read callee accepts mutable borrow", "fn read(n: &Int) -> Int { return n; }; x = 1; return read(&mut x);")
        , ("mutable parameter with contract", "fn increment(n: &mut Int) -> Int writes(n) [{ affirm *n < 100; }] [{ affirm *n = old(*n) + 1; affirm return = *n; }] { *n = *n + 1; return *n; }; x = 4; y = increment(&mut x); return x * 10 + y;")
        , ("mutable field parameter", "struct Point { x: Int, y: Int }; fn bumpX(p: &mut Point) -> Int writes(p.x) [{ }] [{ affirm (*p).x = old((*p).x) + 1; affirm (*p).y = old((*p).y); }] { (*p).x = (*p).x + 1; return (*p).x; }; pt = Point { x: 1, y: 2 }; n = bumpX(&mut pt); return n * 100 + pt.x * 10 + pt.y;")
        , ("mutable parameter in loop", "fn inc(n: &mut Int) -> Int [{ }] [{ affirm *n = old(*n) + 1; }] { *n = *n + 1; return *n; }; x = 0; while x < 3 [{ affirm x >= 0; affirm x <= 3; }] shrinks 3 - x { y = inc(&mut x); }; return x;")
        , ("mutable call reaches old-fact proof check", "fn inc(n: &mut Int) -> Int [{ }] [{ }] { *n = *n + 1; return *n; }; x = 4; y = inc(&mut x); affirm x = 4; return y;")
        , ("mutable call reaches new-fact proof check", "fn inc(n: &mut Int) -> Int [{ }] [{ affirm *n = old(*n) + 1; }] { *n = *n + 1; return *n; }; x = 4; y = inc(&mut x); affirm x = 5; return y;")
        , ("mutable field reborrow", "struct Point { x: Int, y: Int }; fn good(p: &mut Point) -> Int writes(p.x) [{ }] [{ }] { q = &mut (*p).x; *q = 9; return (*p).x; }; pt = Point { x: 1, y: 2 }; return good(&mut pt);")
        , ("mutable reference returned with contract", "fn upd(n: &mut Int) -> &mut Int from n [{ }] [{ }] { return n; }; x = 1; r = upd(&mut x); *r = 7; return x;")
        , ("mutable reference returned", "fn f(x: &mut Int) -> &mut Int from x { return x; }; a = 1; r = f(&mut a); *r = 9; return a;")
        , ("mutable reference returned through parameter", "fn f(x: &mut Int) -> &mut Int from x { return &mut *x; }; a = 1; r = f(&mut a); *r = 9; return a;")
        , ("mutable result read after write", "fn f(x: &mut Int) -> &mut Int from x { return x; }; a = 1; r = f(&mut a); *r = 9; return *r;")
        , ("native returned update reference", "fn f(x: &mut Int) -> &mut Int from x { return x; }; a = 1; r = f(&mut a); *r = 9; return a;")
        , ("native update parameter", "fn inc(x: &mut Int) -> Int { *x = *x + 1; return *x; }; a = 41; inc(&mut a); return a;")
        , ("generic Block cast reaches erasure", "fn f<T>(p: Addr<T>, ghost b: Block<T>) -> Int [{ affirm base(b) = p; affirm whole(b); affirm cap(b) >= 1; affirm count(b) = 0; }] [{ }] { c = Block::cast(b); q = Addr::cast(p); c = Addr::write(q, 0, 7, c); c = Addr::dropValue(q, 0, c); return Addr::free(q, c); }; (p, b) = Addr::alloc(1); return f(p, b);")
        ]
    negatives =
        [ ("read borrow is not an update argument", mutableSource, readInsteadOfMutable)
        , ("owned value is not an update argument", mutableSource, ownedInsteadOfMutable)
        , ("wrong update pointee", mutableSource, wrongMutablePointee)
        , ("mutable function value is not a read function", "fn take(n: &mut Int) -> Int { return 0; }; g = take; x = 1; return g(&mut x);", wrongFunctionKind False)
        , ("read function value is not an update function", "fn take(n: &Int) -> Int { return 0; }; g = take; x = 1; return g(&mut x);", wrongFunctionKind True)
        ]
    blocks =
        [ ("generic Block payload is resolved", "param \"T\"", "int", False, True)
        , ("concrete Block payload matches", "int", "int", False, True)
        , ("concrete Block payload mismatch", "int", "bool", False, False)
        , ("generic Block argument is not a reference", "param \"T\"", "int", True, False)
        , ("Block payload keeps nested reference kind", "list int", "list ref int", False, False)
        , ("unknown Block payload is refused", "param \"T\"", "var 0", False, False)
        ]
    badDerefs =
        [ ("ordinary local is not a reference slot", False, False, "int", "copy 1")
        , ("stray borrowed flag is not a parameter slot", False, True, "int", "copy 1")
        , ("constant is not a reference slot", True, True, "int", "const int 0")
        , ("borrowed slot keeps its pointee type", True, True, "bool", "copy 1")
        ]
    derefFixture parameter borrowed result operand = unlines $
        [ "tersus-mir 1"
        , "function \"probe\" params " ++ (if parameter then "1 1" else "0") ++ " returns some " ++ result ++ " sizeparams 0 typeparams 0 borrowed " ++ (if borrowed then "1 1" else "0") ++ " mutborrowed " ++ (if borrowed then "1 1" else "0") ++ " from 0"
        , "local 0 none " ++ result, "local 1 none int", "block 0"
        ] ++ ["assign 1 use const int 4" | not parameter]
          ++ ["assign 0 deref " ++ operand, "return", "end", "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0", "block 0", "return", "end"]
    blockCall expected actual borrowed = unlines $
        [ "tersus-mir 1"
        , "function \"take\" params 1 1 returns some int sizeparams 0 typeparams " ++ (if expected == "param \"T\"" then "1 \"T\"" else "0") ++ " borrowed 0"
        , "local 0 none int", "local 1 none block " ++ expected
        , "block 0", "assign 0 use const int 0", "return", "end"
        , "main \"main\" params 0 returns some int sizeparams 0 typeparams 0 borrowed 0"
        , "local 0 none int", "local 1 none addr " ++ actual, "local 2 none block " ++ actual
        ] ++ ["local 3 none ref block " ++ actual | borrowed]
          ++ ["block 0", "assign 1 listop addrAlloc 1 const int 1", "assign 2 listop blockNew 2 copy 1 const int 1"]
          ++ ["assign 3 borrow 2 0" | borrowed]
          ++ ["call const fn \"take\" 1 copy " ++ (if borrowed then "3" else "2") ++ " 0 1", "block 1", "return", "end"]

readInsteadOfMutable :: Program -> Program
readInsteadOfMutable program = program{progMain = main{fnLocals = Map.map decl (fnLocals main), fnBlocks = Map.map block (fnBlocks main)}}
  where
    main = progMain program
    decl d = d{localType = case localType d of TMutRef t -> TRef t; other -> other}
    block b = b{blockStatements = map statement (blockStatements b)}
    statement (Assign dest (Borrow root steps True)) = Assign dest (Borrow root steps False)
    statement other = other

ownedInsteadOfMutable :: Program -> Program
ownedInsteadOfMutable program = case localNamed (progMain program) "x" of
    Nothing -> program
    Just x -> program{progMain = main{fnBlocks = Map.map block (fnBlocks main)}}
      where
        main = progMain program
        block b = b{blockTerminator = case blockTerminator b of Call callee [_] dest next -> Call callee [Copy x] dest next; other -> other}

wrongMutablePointee :: Program -> Program
wrongMutablePointee program = case localNamed (progMain program) "x" of
    Nothing -> program
    Just x -> program{progMain = main{fnLocals = Map.mapWithKey decl (fnLocals main), fnBlocks = Map.map block (fnBlocks main)}}
      where
        main = progMain program
        decl l d = d{localType = if l == x then TBool else case localType d of TMutRef TInt -> TMutRef TBool; other -> other}
        block b = b{blockStatements = map statement (blockStatements b)}
        statement (Assign dest (Use _)) | dest == x = Assign dest (Use (Const (CBool True)))
        statement other = other

wrongFunctionKind :: Bool -> Program -> Program
wrongFunctionKind mutable program = case localNamed (progMain program) "g" of
    Nothing -> program
    Just g -> program{progMain = main{fnLocals = Map.adjust (\d -> d{localType = TFn [if mutable then TMutRef TInt else TRef TInt] TInt}) g (fnLocals main)}}
      where main = progMain program

uninitRoundTrip :: IO TestResult
uninitRoundTrip = pure $ case [input | (name, input, _) <- functionCases, name == "function list Uninit argument"] of
    [Ok text] -> case readProgram text of
        Error e -> Just e
        Ok program -> case Map.lookup "probe" (progFunctions program) >>= Map.lookup (Local 0) . fnLocals of
            Nothing -> Just "the Uninit fixture has no return local"
            Just decl -> case testAssertEq (localType decl) (TFn [TUninit TInt] TInt) of
                Just e -> Just e
                Nothing -> case readProgram (writeProgram program) of
                    Error e -> Just e
                    Ok restored -> testAssertEq restored (forNative program)
    _ -> Just "there is no Uninit function fixture"

functionCases :: [(String, Result String String, Bool)]
functionCases =
    [ ("existing function program: " ++ name, sourceData name, True)
    | name <- ["in a list", "a function that lends is a value"]
    ]
        ++ [(name, Ok (fixture element result borrowed), expected) | (name, element, result, borrowed, expected) <- signatures]
        ++ [("function list malformed " ++ label ++ " closer", Ok (fixtureWithLocal (badName, goodType) goodType False ("named \"List<" ++ badName ++ ">\" 0")), False) | (label, badName, goodType) <- malformed]
  where
    sourceData name = case lookup name unvalidatedPrograms of
        Nothing -> Error ("no function program named " ++ name)
        Just source -> case parseStatementBlock source of
            Left e -> Error (show e)
            Right stmts -> mapResult (writeProgram . insertOwnership . nativeProgram) (lowerProgram stmts)
    ordinary = ("fn(Int) -> Int", "fn 1 int int")
    borrowedArg = ("fn(&List<Int>) -> Int", "fn 1 ref list int int")
    namedArg = ("fn(Integer) -> Int", "fn 1 named \"Integer\" 0 int")
    signatures =
        [ ("function list exact signature", ordinary, ordinary, False, True)
        , ("function list through a borrowed list", ordinary, ordinary, True, True)
        , ("function list zero arguments", ("fn() -> Int", "fn 0 int"), ("fn() -> Int", "fn 0 int"), False, True)
        , ("function list two arguments", ("fn(Int, Bool) -> Int", "fn 2 int bool int"), ("fn(Int, Bool) -> Int", "fn 2 int bool int"), False, True)
        , ("function list borrowed argument", borrowedArg, borrowedArg, False, True)
        , ("function list nested argument", ("fn(fn(Int) -> Int) -> Int", "fn 1 fn 1 int int int"), ("fn(fn(Int) -> Int) -> Int", "fn 1 fn 1 int int int"), False, True)
        , ("function list nested result", ("fn() -> fn(Int) -> Int", "fn 0 fn 1 int int"), ("fn() -> fn(Int) -> Int", "fn 0 fn 1 int int"), False, True)
        , ("function list named argument with builtin prefix", namedArg, namedArg, False, True)
        , ("function list wrong argument", ordinary, ("fn(Bool) -> Int", "fn 1 bool int"), False, False)
        , ("function list wrong result", ordinary, ("fn(Int) -> Bool", "fn 1 int bool"), False, False)
        , ("function list missing argument", ordinary, ("fn() -> Int", "fn 0 int"), False, False)
        , ("function list extra argument", ordinary, ("fn(Int, Int) -> Int", "fn 2 int int int"), False, False)
        , ("function list borrowed argument is not owned", borrowedArg, ("fn(List<Int>) -> Int", "fn 1 list int int"), False, False)
        , ("function list read reference is not mutable", borrowedArg, ("fn(&mut List<Int>) -> Int", "fn 1 mutref list int int"), False, False)
        , ("function list mutable argument", ("fn(&mut List<Int>) -> Int", "fn 1 mutref list int int"), ("fn(&mut List<Int>) -> Int", "fn 1 mutref list int int"), False, True)
        , ("function list borrowed result is not owned", ("fn() -> &Integer", "fn 0 ref named \"Integer\" 0"), ("fn() -> Integer", "fn 0 named \"Integer\" 0"), False, False)
        , ("function list read result is not mutable", ("fn() -> &Integer", "fn 0 ref named \"Integer\" 0"), ("fn() -> &mut Integer", "fn 0 mutref named \"Integer\" 0"), False, False)
        , ("function list nested List reference", ("fn(List<&Int>) -> Int", "fn 1 list ref int int"), ("fn(List<Int>) -> Int", "fn 1 list int int"), False, False)
        , ("function list nested Box reference", ("fn(Box<&Int>) -> Int", "fn 1 box ref int int"), ("fn(Box<Int>) -> Int", "fn 1 box int int"), False, False)
        , ("function list nested Addr reference", ("fn(Addr<&Int>) -> Int", "fn 1 addr ref int int"), ("fn(Addr<Int>) -> Int", "fn 1 addr int int"), False, False)
        , ("function list nested Array reference", ("fn(Array<&Int, 2>) -> Int", "fn 1 array ref int c 2 int"), ("fn(Array<Int, 2>) -> Int", "fn 1 array int c 2 int"), False, False)
        , ("function list nested named reference", ("fn(Holder<&Int>) -> Int", "fn 1 named \"Holder\" 1 type ref int int"), ("fn(Holder<Int>) -> Int", "fn 1 named \"Holder\" 1 type int int"), False, False)
        , ("function list nested function reference", ("fn(fn(List<&Int>) -> Int) -> Int", "fn 1 fn 1 list ref int int int"), ("fn(fn(List<Int>) -> Int) -> Int", "fn 1 fn 1 list int int int"), False, False)
        , ("function list nested result reference", ("fn() -> List<&Int>", "fn 0 list ref int"), ("fn() -> List<Int>", "fn 0 list int"), False, False)
        , ("function list array argument", ("fn(Array<Int, 2>) -> Int", "fn 1 array int c 2 int"), ("fn(Array<Int, 2>) -> Int", "fn 1 array int c 2 int"), False, True)
        , ("function list Uninit argument", ("fn(Uninit<Int>) -> Int", "fn 1 uninit int int"), ("fn(Uninit<Int>) -> Int", "fn 1 uninit int int"), False, True)
        , ("function list explicit generic argument", ("fn(List<'T>) -> Int", "fn 1 list param \"T\" int"), ("fn(List<Int>) -> Int", "fn 1 list int int"), False, True)
        , ("function list named argument is not builtin", namedArg, ordinary, False, False)
        ]
    malformed =
        [ ("List", "fn(List<Int)) -> Int", "fn 1 list int int")
        , ("Box", "fn(Box<Int)) -> Int", "fn 1 box int int")
        , ("Addr", "fn(Addr<Int)) -> Int", "fn 1 addr int int")
        , ("Array", "fn(Array<Int, 2)) -> Int", "fn 1 array int c 2 int")
        , ("Uninit", "fn(Uninit<Int)) -> Int", "fn 1 uninit int int")
        ]
    fixture element@(_, elementType) (_, resultType) borrowed =
        fixtureWithLocal element resultType borrowed ("named \"List\" 1 type " ++ elementType)
    fixtureWithLocal (elementName, elementType) resultType borrowed listType = unlines
        [ "tersus-mir 1"
        , "struct \"Integer\" 1 \"n\" int"
        , "struct \"List<" ++ elementName ++ ">\" 3 \"addr\" addr " ++ elementType ++ " \"len\" int \"cap\" int"
        , "function \"probe\" params 1 1 returns some " ++ resultType ++ " sizeparams 0 typeparams " ++ (if "param \"T\"" `isInfixOf` elementType then "1 \"T\"" else "0") ++ " borrowed " ++ if borrowed then "1 1" else "0"
        , "local 0 none " ++ resultType
        , "local 1 none " ++ listType
        , "block 0"
        , "assign 0 listop get 2 copy 1 const int 0"
        , "return"
        , "end"
        , "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0"
        , "block 0"
        , "return"
        , "end"
        ]

rawBorrowCases :: [(String, String, Bool)]
rawBorrowCases = concatMap cases [False, True]
  where
    cases erased =
        [(label name, change (rawBorrowFixture erased), accepted) | (name, change, accepted) <- protocol erased]
            ++ [(label name, rawBorrowChain erased localOwner namedCallee fromOwner, accepted)
               | (name, localOwner, namedCallee, fromOwner, accepted) <-
                    [ ("forward and reborrow through the owner", False, True, True, True)
                    , ("known function value preserves owner origins", False, False, True, True)
                    ]]
            ++ [(label "reference relay preserves its actual from parameter", rawBorrowRelay erased False, True)
               , (label "forged relay from cannot launder a local raw origin", rawBorrowRelay erased True, False)
               , (label "scalar call result cannot forge a reference origin", scalarRelay erased, False)
               ]
      where label name = "addrBorrow " ++ name ++ if erased then " after erasure" else " before erasure"
    protocol erased =
        [ ("accepts its exact protocol", id, True)
        , ("rejects a missing operand", line borrow (borrowWith (init operands)), False)
        , ("rejects an extra operand", line borrow (borrowWith (operands ++ ["copy 4"])), False)
        , ("checks exact index type", line "local 2 none int" "local 2 none bool", False)
        , ("does not unwrap an index reference", line "local 2 none int" "local 2 none ref int", False)
        , ("does not unwrap an update index reference", line "local 2 none int" "local 2 none mutref int", False)
        , ("checks address element against reference element", line "local 1 none addr int" "local 1 none addr bool", False)
        , ("does not unwrap an address reference", line "local 1 none addr int" "local 1 none ref addr int", False)
        , ("rejects a non-reference result", result "int", False)
        , ("rejects an update reference result", result "mutref int", False)
        , ("rejects a reference-bearing raw payload", result "ref ref int" . line "local 1 none addr int" "local 1 none addr ref int" . line "local 3 none block int" "local 3 none block ref int", False)
        , ("function payload rejects an unresolved return", payload "fn 0 param \"T\"", False)
        , ("function payload rejects quantified types", payload "forall 0 1 \"T\" fn 0 param \"T\"", False)
        , ("function payload rejects reference arguments", payload "fn 1 ref int int", False)
        , ("function payload rejects reference returns", payload "fn 0 ref int", False)
        , ("function payload accepts a concrete scalar signature", payload "fn 1 int int", True)
        , ("rejects a missing owner", owner "copy 999", False)
        , ("rejects a constant owner", owner "const int 0", False)
        , ("rejects a moved owner operand", owner "move 4", False)
        , ("rejects a ghost owner", line ownerLocal "local 4 some \"owner\" block int", False)
        , ("rejects a reference to a ghost owner", line ownerLocal "local 4 some \"owner\" ref block int", False)
        , ("rejects an owner without known runtime representation", line ownerLocal "local 4 some \"owner\" param \"T\"", False)
        , ("rejects an all-ghost struct owner", line ownerLocal "local 4 some \"owner\" named \"GhostOwner\" 0", False)
        , ("owner must be in from", line header (rawBorrowHeader erased "probe" "ref int" True "1 2"), False)
        , ("owner must be borrowed", line header (rawBorrowHeader erased "probe" "ref int" False "1 4"), False)
        , ("owner must be a parameter", line header (removeOwnerParam erased (rawBorrowHeader erased "probe" "ref int" True "1 4")), False)
        , ("dropped owner cannot support a raw return", line borrow ("drop 4\n" ++ borrow), False)
        , ("consumed owner cannot support a raw return", line borrow ("peek 9 use move 4\n" ++ borrow) . addLocalOwner, False)
        , ("scalar address from cannot forge an escaping owner", line header scalarHeader . owner "copy 1", False)
        , ("scalar address anchor is accepted for a local read", localRead . owner "copy 1", True)
        , ("a borrowed owner is not droppable after a scalar read", result "int" . line borrow ("assign 5" ++ drop (length "assign 0") borrow ++ "\nassign 0 deref copy 5\ndrop 4"), False)
        , ("copy chain remains structurally well typed", line borrow ("assign 5" ++ drop (length "assign 0") borrow ++ "\nassign 0 use copy 5"), True)
        , ("reborrow chain remains structurally well typed", line borrow ("assign 5" ++ drop (length "assign 0") borrow ++ "\nassign 6 borrow 5 0\nassign 0 use copy 6"), True)
        , ("overwriting cannot hide a local origin", line borrow ("assign 5" ++ drop (length "assign 0") (borrowWith (init operands ++ ["copy 9"])) ++ "\nassign 5" ++ drop (length "assign 0") borrow ++ "\nassign 0 use copy 5") . addLocalOwner, False)
        , ("every raw owner operand must match from metadata at a branch", branch erased . addLocalOwner, False)
        , ("reference cycle remains structurally well typed", line borrow ("assign 5" ++ drop (length "assign 0") borrow ++ "\nassign 6 use copy 5\nassign 5 use copy 6\nassign 0 use copy 6"), True)
        , ("manual tuple anchor needs no Drop or library name", tupleAnchor, True)
        ]
            ++ [("checks exact permission element", line "local 3 none block int" "local 3 none block bool", False) | not erased]
            ++ [("does not unwrap a permission reference", line "local 3 none block int" "local 3 none ref block int", False) | not erased]
      where
        operands = rawBorrowOperands erased
        borrow = borrowWith operands
        borrowWith os = "assign 0 listop addrBorrow " ++ show (length os) ++ " " ++ unwords os
        owner o = line borrow (borrowWith (init operands ++ [o]))
        ownerLocal = "local 4 some \"owner\" named \"Owner\" 0"
        header = rawBorrowHeader erased "probe" "ref int" True "1 4"
        scalarHeader = lineText "borrowed 1 4" "borrowed 1 1" (rawBorrowHeader erased "probe" "ref int" True "1 1")
        result ty = line header (rawBorrowHeader erased "probe" ty True (if ty == "int" then "0" else "1 4")) . line "local 0 none ref int" ("local 0 none " ++ ty)
        payload ty = result ("ref " ++ ty)
            . line "local 1 none addr int" ("local 1 none addr " ++ ty)
            . line "local 3 none block int" ("local 3 none block " ++ ty)
        localRead = result "int" . line scalarBorrow ("assign 5" ++ drop (length "assign 0") scalarBorrow ++ "\nassign 0 deref copy 5")
        scalarBorrow = borrowWith (init operands ++ ["copy 1"])
        tupleAnchor = line ownerLocal "local 4 some \"owner\" named \"AllocationTuple\" 0"
            . line ("struct \"Owner\" " ++ if erased then "1 \"addr\" addr int" else "2 \"addr\" addr int \"blk\" block int")
                ("struct \"AllocationTuple\" " ++ if erased then "1 \"0\" addr int" else "2 \"0\" addr int \"1\" block int")
        addLocalOwner = line "block 0" "local 9 some \"localOwner\" named \"Owner\" 0\nblock 0"
        branch erased' = line borrow ("switch const bool true 1 2\nblock 1\nassign 5" ++ drop (length "assign 0") borrow ++ "\ngoto 3\nblock 2\nassign 5" ++ drop (length "assign 0") (borrowWith (init (rawBorrowOperands erased') ++ ["copy 9"])) ++ "\ngoto 3\nblock 3\nassign 0 use copy 5")
    scalarRelay erased = lineText (relay "ref int" ++ "\nlocal 0 none ref int") (relay "int" ++ "\nlocal 0 none int")
        . line "assign 0 use copy 1" "assign 0 use const int 0" $ rawBorrowRelay erased False
      where relay result = "function \"relay\" params 2 1 2 returns some " ++ result ++ " sizeparams 0 typeparams 0 borrowed 2 1 2 mutborrowed 0 from 1 1"
    line old new = unlines . map (\text -> if text == old then new else text) . lines
    lineText old new text = case splitAtPrefix old text of
        Just (before, after) -> before ++ new ++ after
        Nothing -> text
    splitAtPrefix prefix text
        | prefix `isPrefixOf` text = Just ("", drop (length prefix) text)
        | c : rest <- text = do
            (before, after) <- splitAtPrefix prefix rest
            pure (c : before, after)
        | otherwise = Nothing
    removeOwnerParam erased = lineText (if erased then "params 3 1 2 4" else "params 4 1 2 3 4") (if erased then "params 2 1 2" else "params 3 1 2 3")

rawBorrowOperands :: Bool -> [String]
rawBorrowOperands erased = ["copy 1", "copy 2"] ++ ["copy 3" | not erased] ++ ["copy 4"]

rawBorrowHeader :: Bool -> String -> String -> Bool -> String -> String
rawBorrowHeader erased name result borrowed from =
    "function \"" ++ name ++ "\" params " ++ (if erased then "3 1 2 4" else "4 1 2 3 4")
        ++ " returns some " ++ result ++ " sizeparams 0 typeparams 0 borrowed " ++ (if borrowed then "1 4" else "0") ++ " mutborrowed 0 from " ++ from

rawBorrowFixture :: Bool -> String
rawBorrowFixture erased = unlines $
    [ "tersus-mir 1"
    , "struct \"Owner\" " ++ if erased then "1 \"addr\" addr int" else "2 \"addr\" addr int \"blk\" block int"
    , "struct \"GhostOwner\" 1 \"blk\" block int"
    , rawBorrowHeader erased "probe" "ref int" True "1 4"
    , "local 0 none ref int", "local 1 none addr int", "local 2 none int"
    ] ++ ["local 3 none block int" | not erased]
      ++ [ "local 4 some \"owner\" named \"Owner\" 0", "local 5 none ref int", "local 6 none ref int"
         , "block 0", "assign 0 listop addrBorrow " ++ show (length operands) ++ " " ++ unwords operands
         , "return", "end", "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0", "block 0", "return", "end"
         ]
  where operands = rawBorrowOperands erased

rawBorrowChain :: Bool -> Bool -> Bool -> Bool -> String
rawBorrowChain erased localOwner namedCallee fromOwner = unlines $
    map (\text -> if text == rawBorrowHeader erased "probe" "ref int" True "1 4" then rawBorrowHeader erased "pick" "ref int" True "1 4" else text)
        (takeWhile (not . isPrefixOf "main ") (lines (rawBorrowFixture erased)))
        ++ [ header
           , "local 0 none ref int", "local 1 none addr int", "local 2 none int"
           ] ++ ["local 3 none block int" | not erased]
        ++ ["local 4 some \"owner\" named \"Owner\" 0", "local 5 none ref int", "local 6 none ref int"]
        ++ ["local 8 none fn " ++ show (length operands) ++ " addr int int " ++ (if erased then "" else "block int ") ++ "ref named \"Owner\" 0 ref int" | not namedCallee]
        ++ ["block 0"] ++ ["assign 8 use const fn \"pick\"" | not namedCallee]
        ++ [ "call " ++ (if namedCallee then "const fn \"pick\"" else "copy 8") ++ " " ++ show (length operands) ++ " " ++ unwords operands ++ " 5 1"
           , "block 1", "assign 6 borrow 5 0", "assign 0 use copy 6", "return", "end"
           , "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0", "block 0", "return", "end"
           ]
  where
    operands = rawBorrowOperands erased
    header = "function \"forward\" params " ++ (if localOwner then if erased then "2 1 2" else "3 1 2 3" else if erased then "3 1 2 4" else "4 1 2 3 4")
        ++ " returns some ref int sizeparams 0 typeparams 0 borrowed 1 4 mutborrowed 0 from " ++ (if fromOwner then "1 4" else "1 2")

rawBorrowRelay :: Bool -> Bool -> String
rawBorrowRelay erased forged = unlines $
    concatMap (\text -> if "assign 0 listop addrBorrow " `isPrefixOf` text
        then ["assign 5 listop addrBorrow " ++ show (length operands) ++ " " ++ unwords operands, "call const fn \"relay\" 2 copy 5 copy 4 0 1", "block 1"]
        else if text == "block 0" && forged then ["local 9 some \"localOwner\" named \"Owner\" 0", text]
        else [text]) (takeWhile (not . isPrefixOf "main ") (lines (rawBorrowFixture erased)))
        ++ [ "function \"relay\" params 2 1 2 returns some ref int sizeparams 0 typeparams 0 borrowed 2 1 2 mutborrowed 0 from 1 " ++ (if forged then "2" else "1")
           , "local 0 none ref int", "local 1 none ref int", "local 2 none named \"Owner\" 0"
           , "block 0", "assign 0 use copy 1", "return", "end"
           , "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0", "block 0", "return", "end"
           ]
  where operands = init (rawBorrowOperands erased) ++ [if forged then "copy 9" else "copy 4"]

blockCases :: [(String, String, Bool)]
blockCases = concatMap cases signatures
  where
    signatures =
        [ ("blockNew", ["addr int", "int"])
        , ("blockTaken", ["block int", "int"])
        , ("blockResized", ["block int", "addr int", "int"])
        , ("blockSplitLo", ["block int", "int"])
        , ("blockSplitHi", ["block int", "int"])
        , ("blockJoin", ["block int", "block int"])
        , ("blockAssume", ["addr int", "int"])
        , ("blockCast", ["block int"])
        ]
    cases (op, types) =
        [ (op ++ " accepts its signature", fixture op "block int" types types, True)
        , (op ++ " refuses a missing operand", fixture op "block int" types (init types), False)
        , (op ++ " refuses an extra operand", fixture op "block int" (types ++ ["int"]) (types ++ ["int"]), False)
        , (op ++ " refuses a non-Block result", fixture op "int" types types, False)
        , (op ++ " refuses a reference result", fixture op "ref block int" types types, False)
        , (op ++ " checks result element type", fixture op "block bool" types types, op == "blockCast")
        ]
            ++ [ (op ++ " refuses operand " ++ show i ++ " as " ++ wrong, fixture op "block int" (replace i wrong types) types, False)
               | (i, ty) <- zip [0 ..] types
               , wrong <- ["bool", "ref " ++ ty, "mutref " ++ ty] ++ [different | op /= "blockCast", different <- differentElement ty]
               ]
    differentElement "addr int" = ["addr bool"]
    differentElement "block int" = ["block bool"]
    differentElement _ = []
    replace i ty types = take i types ++ [ty] ++ drop (i + 1) types
    fixture op result locals operands = unlines $
        [ "tersus-mir 1"
        , "function \"probe\" params " ++ show (length locals) ++ concatMap ((" " ++) . show) [1 .. length locals] ++ " returns some " ++ result ++ " sizeparams 0 typeparams 0 borrowed 0"
        , "local 0 none " ++ result
        ]
            ++ ["local " ++ show i ++ " none " ++ ty | (i, ty) <- zip [1 :: Int ..] locals]
            ++ [ "block 0"
               , "assign 0 listop " ++ op ++ " " ++ show (length operands) ++ concatMap ((" copy " ++) . show) [1 .. length operands]
               , "return"
               , "end"
               , "main \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0"
               , "block 0"
               , "return"
               , "end"
               ]

refused :: IO TestResult
refused = do
    verifier <- verifierProgram
    pure $ case verifier of
        Error e -> Just ("the verifier does not compile: " ++ e)
        Ok verifierProgram -> case runProgramIn noWorld{worldInput = ""} verifierProgram of
            Error e -> Just e
            Ok ((output, errors), _)
                | output == "1" && "not the MIR as data" `isInfixOf` errors -> Nothing
                | otherwise -> Just ("got output " ++ show output ++ " and errors " ++ show errors)

noEntryBlock :: Program -> Program
noEntryBlock program = program{progMain = (progMain program){fnBlocks = Map.delete (BlockId 0) (fnBlocks (progMain program))}}

varLocal :: Program -> Program
varLocal program = program{progMain = change (progMain program)}
  where
    change fn = case Map.keys (fnLocals fn) of
        [] -> fn
        local : _ -> fn{fnLocals = Map.adjust (\decl -> decl{localType = TVar 0}) local (fnLocals fn)}

switchOnInt :: Program -> Program
switchOnInt = onEveryFunction change
  where
    change fn = fn{fnBlocks = Map.map block (fnBlocks fn)}
    block basic = basic{blockTerminator = case blockTerminator basic of
        SwitchBool _ yes no -> SwitchBool (Const (CInt 1)) yes no
        other -> other}

unknownCall :: Program -> Program
unknownCall = onEveryFunction change
  where
    change fn = fn{fnBlocks = Map.map block (fnBlocks fn)}
    block basic = basic{blockTerminator = case blockTerminator basic of
        Call _ args dest next -> Call (Const (CFn "noSuchFunction")) args dest next
        other -> other}

constructorSource :: String
constructorSource = "struct ProbeCtor { value: Int }; x = ProbeCtor { value: 1 }; return x.value;"

unknownConstructor :: Program -> Program
unknownConstructor program = program{progMain = main{fnBlocks = Map.map block (fnBlocks main)}}
  where
    main = progMain program
    block basic = basic{blockStatements = map statement (blockStatements basic)}
    statement (Assign dest (MakeData "ProbeCtor" fields)) = Assign dest (MakeData "MissingCtor" fields)
    statement (Peek dest (MakeData "ProbeCtor" fields)) = Peek dest (MakeData "MissingCtor" fields)
    statement other = other

missingTarget :: Program -> Program
missingTarget program = program{progMain = main{fnBlocks = Map.map block (fnBlocks main)}}
  where
    main = progMain program
    block basic = basic{blockTerminator = case blockTerminator basic of
        SwitchBool condition _ no -> SwitchBool condition (BlockId 999999) no
        other -> other}

localNamed :: Function -> String -> Maybe Local
localNamed fn wanted = case [local | (local, decl) <- Map.toList (fnLocals fn), localName decl == Just wanted] of
    local : _ -> Just local
    [] -> Nothing

wrongHolderArg :: Program -> Program
wrongHolderArg program = case localNamed (progMain program) "b" of
    Nothing -> program
    Just b -> program{progMain = change (progMain program)}
      where
        change fn = fn{fnBlocks = Map.map block (fnBlocks fn)}
        block basic = basic{blockTerminator = case blockTerminator basic of
            Call callee@(Const (CFn "take2")) (_ : rest) dest next -> Call callee (Copy b : rest) dest next
            other -> other}

arrayOfLists :: Program -> Program
arrayOfLists program = case localNamed (progMain program) "xs" of
    Nothing -> program
    Just xs -> program{progMain = (progMain program){fnLocals = Map.adjust change xs (fnLocals (progMain program))}}
  where
    change decl = decl{localType = case localType decl of
        TArrayOf _ size -> TArrayOf (TList TInt) size
        other -> other}

onEveryFunction :: (Function -> Function) -> Program -> Program
onEveryFunction change program =
    program
        { progMain = change (progMain program)
        , progFunctions = Map.map change (progFunctions program)
        }

withVerifier :: (FilePath -> IO TestResult) -> IO TestResult
withVerifier = withProgram "examples/mir/mir_verify/mir_verify.tersus" "mir-verify"

-- One case per program, so the sweep runs at the harness's parallelism instead of one program after another
-- inside a single case (withVerifier builds the verifier executable once for the process). The data comes from
-- the harness's shared cache (mirDataOf), and the Haskell verdict is taken on the program read back from it.
nativeCheck :: String -> String -> IO TestResult
nativeCheck name source = withVerifier $ \exe -> do
    failures <- check exe (name, source)
    pure $ case failures of
        [] -> Nothing
        bad -> Just (unlines bad)
  where
    check exe (name, source) = do
        dataOf <- if "examples/mir/" `isPrefixOf` name then mirDataFromFile name else mirDataOf source
        case dataOf of
            Error e -> pure [name ++ ": " ++ e]
            Ok text -> case readProgram text of
                Error e -> pure [name ++ ": the data does not read back: " ++ e]
                Ok program -> do
                    let expected = referenceAccepts program
                    (code, output, errors) <- runExecutableBytes exe [] text
                    let accepted = code == ExitSuccess && sameText output "OK"
                        refusedIt = code /= ExitSuccess && output == "1\n" && not (null errors)
                    pure
                        [ name ++ ": expected " ++ (if expected then "acceptance" else "refusal") ++ ", got exit " ++ show code ++ ", output " ++ show output ++ ", errors " ++ take 200 errors
                        | (expected && not accepted) || (not expected && not refusedIt)
                        ]
