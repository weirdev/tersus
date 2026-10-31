module TestMirData (testMirData) where

import Data.Char (isAscii)
import Data.List (isInfixOf)
import qualified Data.Map.Strict as Map

import Cli (Command (..), runSource)
import Mir
import MirData
import Pipeline (ownedSource)
import Types (Arg (..), Type (..))
import TestHarness
import TestNative (nativeExamples, validatedPrograms)
import Utils

-- The MIR as data (`tersus mir --data`, MirData): what is written is read back as the same program, for every example and every program that
-- native code is tested with, and a name of any bytes is written as ASCII.
testMirData :: Test
testMirData =
    TestList
        "testMirData"
        [ TestList "examples" [TestCase path (roundTripsAndIr <$> readFile path) | path <- nativeExamples]
        , TestList "programs" [TestCase name (pure (roundTripsAndIr source)) | (name, source) <- validatedPrograms]
        , TestList
            "format"
            [ testCase "the command prints it" $
                case runSource MirText "return 1 + 2;" of
                    Ok text | take 1 (lines text) == ["tersus-mir 1"], "main " `elem` map (take 5) (lines text) -> Nothing
                    other -> Just ("not the data of a program: " ++ show other)
            , testCase "a function is its lines" $
                case runSource MirText "fn double(n: Int) -> Int [{ }] [{ }] { return n + n; }; return double(4);" of
                    Ok text ->
                        let ls = lines text
                         in if "function \"double\" params 1 1 returns some int sizeparams 0 typeparams 0 borrowed 0" `elem` ls
                                && "assign 0 binary add copy 1 copy 1" `elem` ls
                                then Nothing
                                else Just text
                    Error e -> Just e
            , testCase "a named type writes its arguments" $
                case runSource MirText "struct Pair<T> { a: T, b: T }; p = Pair<Int> { a: 1, b: 2 }; return p.a;" of
                    Ok text | any ("named \"Pair\" 1 type int" `isInfixOf`) (lines text) -> Nothing
                    other -> Just ("not the data of a generic instance: " ++ show other)
            , testCase "a name of any bytes is ASCII and comes back" (names roundTripsNames)
            , testCase "the validator's part is not data" $
                case ownedSource "fn f(n: Int) -> Int [{ affirm n > 0; }] [{ affirm return > 0; }] { return n; }; return f(2);" of
                    Ok program -> if readProgram (writeProgram program) == Ok (forNative program) && not (any isGhost (statements (forNative program))) then Nothing else Just "ghost statements were kept"
                    Error e -> Just e
            ]
        , TestList
            "instances"
            [ testCase "an instance introduced by another instance is declared" nestedInstanceIsDeclared
            ]
        , TestList
            "reading"
            [ testCase "a text that is not the MIR" (refused "return 1;" "tersus-mir 1")
            , testCase "a program without main" (refused "tersus-mir 1\nstruct \"P\" 0\n" "no main")
            , testCase "a record that is not known" (refused "tersus-mir 1\nbogus 1\n" "not a record")
            , testCase "a function that is not ended" (refused "tersus-mir 1\nmain \"main\" params 0 returns none sizeparams 0 typeparams 0 borrowed 0\nblock 0\nreturn\n" "end")
            , testCase "a name that is not closed" (refused "tersus-mir 1\nstruct \"P 0\n" "not closed")
            , testCase "a type that is not one" (refused "tersus-mir 1\nstruct \"P\" 1 \"x\" text\n" "not a type")
            ]
        ]
  where
    refused text expected = testAssertErrorContains expected (readProgram text)
    statements program = concat [stmts | f <- progMain program : Map.elems (progFunctions program), BasicBlock stmts _ <- Map.elems (fnBlocks f)]
    isGhost s = case s of
        Ghost _ _ -> True
        _ -> False

-- The data of a program reads back as the same program, and is written the same way again. That the data the emitter is
-- given and the data of the program read back from it make the same IR is checked with the emitter itself in TestMirEmit.
roundTripsAndIr :: String -> TestResult
roundTripsAndIr source = case ownedSource source of
    Error e -> Just ("does not compile: " ++ e)
    Ok program ->
        let text = writeProgram program
            native = forNative program
         in case readProgram text of
                Error e -> Just ("cannot be read back: " ++ e)
                Ok back
                    | not (all isAscii text) -> Just "the data is not ASCII"
                    | back /= native -> Just "reads back as another program"
                    | writeProgram back /= text -> Just "is written differently after it was read"
                    | otherwise -> Nothing

-- Names with a space, quotes, a backslash, a newline and letters of every width
names :: Program -> TestResult
names program =
    let text = writeProgram program
     in case readProgram text of
            Ok back | back == program && all isAscii text && length (lines text) == length (lines (writeProgram back)) -> Nothing
            Ok _ -> Just "another program"
            Error e -> Just e

nestedInstanceIsDeclared :: TestResult
nestedInstanceIsDeclared =
    let program =
            Program
                { progTypes = Map.empty
                , progFunctions = Map.empty
                , progMain =
                    Function
                        { fnName = "main"
                        , fnParams = []
                        , fnReturns = Nothing
                        , fnLocals = Map.fromList [(Local 0, LocalDecl (TNamed "Outer" [ArgType TInt]) Nothing)]
                        , fnBlocks = Map.fromList [(BlockId 0, BasicBlock [] Return)]
                        , fnSizeParams = []
                        , fnTypeParams = []
                        , fnBorrowed = []
                        , fnSpec = emptySpec
                        }
                , progGenerics =
                    Map.fromList
                        [ ("Outer", (["T"], [("inner", TNamed "Inner" [ArgType (TParam "T")]), ("tag", TInt)]))
                        , ("Inner", (["T"], [("value", TParam "T")]))
                        ]
                , progInvariants = Map.empty
                }
        completed = completeInstances program
     in if Map.lookup "Outer<Int>" (progTypes completed) == Just (StructDecl [("inner", TNamed "Inner" [ArgType TInt]), ("tag", TInt)])
            && Map.lookup "Inner<Int>" (progTypes completed) == Just (StructDecl [("value", TInt)])
            then Nothing
            else Just ("the nested instance was not declared: " ++ show (Map.toList (progTypes completed)))

roundTripsNames :: Program
roundTripsNames =
    Program
        { progTypes = Map.fromList [(oddName, StructDecl [(oddName, TNamed oddName [])])]
        , progFunctions = Map.fromList [(oddName, fn oddName)]
        , progMain = fn "main"
        , progGenerics = Map.empty
        , progInvariants = Map.empty
        }
  where
    oddName = "a \"quoted\" \\ name\nwith caf\233, \955 and \128512"
    fn n =
        Function
            { fnName = n
            , fnParams = []
            , fnReturns = Nothing
            , fnLocals = Map.fromList [(Local 0, LocalDecl TInt (Just oddName))]
            , fnBlocks = Map.fromList [(BlockId 0, BasicBlock [Assign (Local 0) (Use (Const (CData oddName [(oddName, CFn oddName)])))] Return)]
            , fnSizeParams = []
            , fnTypeParams = []
            , fnBorrowed = []
            , fnSpec = emptySpec
            }
