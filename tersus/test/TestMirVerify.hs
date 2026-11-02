module TestMirVerify (testMirVerify, testMirVerifyPrograms) where

import Data.List (isInfixOf)
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
import Types (Type (..))
import TestHarness
import TestMirReader (sameText, withProgram)
import TestNative (nativeExamples, runExecutableBytes, unvalidatedPrograms, validatedPrograms)
import Utils

-- The MIR housekeeping of REPLACING_HASKELL.md target 3, in Tersus (examples/mir_verify.tersus): the check that a program
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
        , TestCase "Uninit function type round trips through MIR data" uninitRoundTrip
        , TestList "function-list identity, interpreted"
            [TestCase name (rawInterpreted expected input) | (name, input, expected) <- functionCases]
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
    source <- readFile "examples/mir_verify.tersus"
    pure $ case lowerSource True source of
        Error e -> Just e
        Ok program ->
            let owned = insertOwnership program
                check (name, owner, field, tableType, elementType) = case Map.lookup name (progFunctions owned) of
                    Nothing -> Just ("the verifier has no " ++ name ++ " function")
                    Just fn ->
                        let copied = [dest | block <- Map.elems (fnBlocks fn), Assign dest (ReadField _ actualOwner actualField) <- blockStatements block, actualOwner == owner, actualField == field, Just decl <- [Map.lookup dest (fnLocals fn)], localType decl == tableType]
                            elementCopies = [dest | Just raw <- [Map.lookup name (progFunctions program)], block <- Map.elems (fnBlocks raw), Assign dest (ListOp Get _) <- blockStatements block, Just decl <- [Map.lookup dest (fnLocals raw)], localType decl == elementType]
                         in if null (copied ++ elementCopies) then Nothing else Just (name ++ " clones its input aggregate into " ++ show (copied ++ elementCopies))
                targets = [("ctorInfo", "Program", "types", TList (TNamed "TypeDecl" []), TNamed "TypeDecl" []), ("findBlock", "Function", "blocks", TList (TNamed "MirBlock" []), TNamed "MirBlock" []), ("findLocal", "Function", "locals", TList (TNamed "LocalDecl" []), TNamed "LocalDecl" [])]
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
verifierProgram = readFile "examples/mir_verify.tersus" >>= compileOnce

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
        failures <- mapM (check exe) (("raw lists and Boxes library", library, True) : blockCases)
        functionFailures <- mapM (\(name, input, expected) -> case input of
            Error e -> pure (Just (name ++ ": " ++ e))
            Ok text -> check exe (name, text, expected)) functionCases
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
        ++ [("function list malformed " ++ label ++ " closer", Ok (fixtureWithLocal (badName, goodType) goodType False ("named \"StdList<" ++ badName ++ ">\" 0")), False) | (label, badName, goodType) <- malformed]
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
        fixtureWithLocal element resultType borrowed ("named \"StdList\" 1 type " ++ elementType)
    fixtureWithLocal (elementName, elementType) resultType borrowed listType = unlines
        [ "tersus-mir 1"
        , "struct \"Integer\" 1 \"n\" int"
        , "struct \"StdList<" ++ elementName ++ ">\" 3 \"addr\" addr " ++ elementType ++ " \"len\" int \"cap\" int"
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
withVerifier = withProgram "examples/mir_verify.tersus" "mir-verify"

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
        dataOf <- mirDataOf source
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
