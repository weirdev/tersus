{-# LANGUAGE PatternSynonyms #-}

module TestMirData (testMirData, testMirLowered) where

import Data.Char (isAscii)
import Data.List (isInfixOf, isPrefixOf, sort)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Cli (Command (..), runSource)
import Compile (elaborateStatements, sourceRequest)
import Differential (Unit (..), suiteUnits, toolPackages)
import ElaborateRequest (LibraryAnswer (..), LoadKind (..), LoadRequest (..), LoadResponse (..), Response (..))
import ElaboratorTool (bootstrapLoader, sourceLoader)
import LibPackage (libCatalog, libPackage)
import Lowering (lowerAccepted)
import Mir
import MirHousekeeping (validationEntry)
import MirMoves (finishLowered)
import Modules (LoadResult (..))
import qualified Modules as Mod
import MirData
import qualified PackageCompile as Package
import PreludeSource (elaboratePackageFiles, libModules, toolPackageFiles, validationPackageFiles)
import qualified Syntax as S
import Pipeline (ownedSource, loadFromFilesystem)
import Types (Arg (..), Size (..), Type (..), pattern TList, pattern TBox)
import TestHarness
import TestNative (nativeExamples, validatedPrograms)
import TestVariadic (variadicPrograms)
import Utils

-- The MIR as data (`tersus mir --data`, MirData): what is written is read back as the same program, for every example and every program that
-- native code is tested with, and a name of any bytes is written as ASCII.
testMirData :: Test
testMirData =
    TestList
        "testMirData"
        [ TestParallel "examples" [TestCase path (roundTripsAndIrForPath path) | path <- nativeExamples]
        , TestParallel "programs" [TestCase name (roundTripsAndIr source) | (name, source) <- validatedPrograms]
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
            , testCase "erasure scrubs existing declarations as well as new instances" existingPermissionsAreErased
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
-- The data comes from the harness's shared cache (mirDataOf): the groups between them compile these programs once.
roundTripsAndIrForPath :: FilePath -> IO TestResult
roundTripsAndIrForPath path = do
    loaded <- loadFromFilesystem path
    case loaded of
        Right (PackageResult _) -> do
            dataOf <- mirDataFromFile path
            pure (roundTripResult dataOf)
        _ -> readFile path >>= roundTripsAndIr

roundTripsAndIr :: String -> IO TestResult
roundTripsAndIr source = do
    dataOf <- mirDataOf source
    pure (roundTripResult dataOf)

roundTripResult :: Result String String -> TestResult
roundTripResult dataOf =
    case dataOf of
        Error e -> Just ("does not compile: " ++ e)
        Ok text -> case readProgram text of
            Error e -> Just ("cannot be read back: " ++ e)
            Ok back
                | not (all isAscii text) -> Just "the data is not ASCII"
                | back /= forNative back -> Just "reads back as another program"
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
                , progBounded = Map.empty
                , progInstances = Map.empty
                }
        completed = completeInstances program
     in if Map.lookup "Outer<Int>" (progTypes completed) == Just (StructDecl [("inner", TNamed "Inner" [ArgType TInt]), ("tag", TInt)])
            && Map.lookup "Inner<Int>" (progTypes completed) == Just (StructDecl [("value", TInt)])
            then Nothing
            else Just ("the nested instance was not declared: " ++ show (Map.toList (progTypes completed)))

existingPermissionsAreErased :: TestResult
existingPermissionsAreErased =
    let fields = [("addr", TAddr TInt), ("blk", TBlock TInt)]
        declarations = Map.fromList [("Box<Int>", StructDecl fields), ("E", EnumDecl [("E::Held", fields)])]
        program = roundTripsNames
            { progTypes = declarations
            , progFunctions = Map.empty
            , progMain = (progMain roundTripsNames)
                { fnLocals = Map.singleton (Local 0) (LocalDecl (TNamed "Wrapped" [ArgType TInt]) Nothing)
                , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] Return)
                }
            , progGenerics = Map.singleton "Wrapped" (["T"], [("value", TParam "T"), ("blk", TBlock (TParam "T"))])
            }
        completed = completeErasedInstances program
        expected = Map.fromList
            [ ("Box<Int>", StructDecl [("addr", TAddr TInt)])
            , ("E", EnumDecl [("E::Held", [("addr", TAddr TInt)])])
            , ("Wrapped<Int>", StructDecl [("value", TInt)])
            ]
     in if progTypes completed == expected && all (\(name, declaration) -> Map.lookup name (progTypes (completeInstances program)) == Just declaration) (Map.toList declarations)
            then Nothing
            else Just ("erased declarations: " ++ show (progTypes completed))

roundTripsNames :: Program
roundTripsNames =
    Program
        { progTypes = Map.fromList [(oddName, StructDecl [(oddName, TNamed oddName [])])]
        , progFunctions = Map.fromList [(oddName, fn oddName)]
        , progMain = fn "main"
        , progGenerics = Map.empty
        , progInvariants = Map.empty
        , progBounded = Map.empty
        , progInstances = Map.empty
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
            , fnMutBorrowed = []
            , fnFrom = []
            , fnSpec = emptySpec
            }

-- A lowered unit as data (`tersus-mir 3`, MirData.writeLowered): every unit the compiler lowers from the corpus reads
-- back as the same unit, and the names it carries are those the module declares.
-- Finishing a raw unit gives fixed MIR and errors, a unit with every kind of record round trips, broken copies of it
-- are refused, and what the data cannot hold is refused by the writer.
testMirLowered :: Test
testMirLowered =
    TestList
        "testMirLowered"
        [ TestParallel
            "corpus"
            ( TestCase "examples" examplesLower
                : TestCase "variadic functions" (unitsLower [SourceText ("variadic: " ++ name) source | (name, source) <- variadicPrograms ++ variadicLowering, name /= refusedVariadic])
                : testCase "a define of a variadic function's pack is refused by the lowering" (case lookup refusedVariadic variadicLowering of
                    Just source -> case fileLowering refusedVariadic source of
                        Ok [(_, lowered)] -> testAssertErrorContains "Undefined variable: n" lowered
                        other -> Just ("not one lowering: " ++ take 300 (show other))
                    Nothing -> Just "no such program")
                : TestCase "examples/modules" (unitsLower [FilePackage "examples/modules/app/main.tersus"])
                : TestCase "compiler libraries" librariesLower
                : [TestCase entry (unitsLower [EmbeddedPackage entry]) | entry <- loweredToolEntries]
            )
        , TestList
            "declared names"
            [ TestCase "a package module's are those at its top" (pure nestedInPackage)
            , testCase "a single file's are those nested too" nestedInFile
            ]
        , TestList
            "finishing"
            [ testCase "instances are completed and places taken out" finishedInstances
            , testCase "a move error says where" finishedMoveError
            , TestCase "the stubs of imported functions are dropped" (pure finishedStubs)
            ]
        , testCase "a unit with every kind of record" (loweredRoundTrip everyRecord)
        , TestList "malformed" [testCase label (refusedLowered expected broken) | (label, expected, broken) <- malformedLowered]
        , TestList
            "what the data cannot hold"
            [ testCase "an integer constant of any size is held" (loweredRoundTrip (withLocal (Local 2) TInt (Use (Const (CInt (2 ^ (70 :: Int))))) everyRecord))
            , testCase "a statement list with an integer of any size is held" bigIntegerStatements
            , testCase "a fixed-width type without a word is refused" (testAssertErrorContains "a type the data has no word for" (writeLowered (withLocal (Local 2) (TWord True 64) (Use (Const (CInt 1))) everyRecord)))
            , testCase "a narrowing without a word is refused" (testAssertErrorContains "an operation the data has no word for" (writeLowered (withLocal (Local 2) TInt (ListOp (Narrow True 64) [Copy (Local 1)]) everyRecord)))
            ]
        ]

loweredToolEntries :: [FilePath]
loweredToolEntries = toolPackages ++ ["lib/mir/mir_reader/mir_reader.tersus", "lib/elaborate/elaborate.tersus"]

expectedRefusals :: [(FilePath, String)]
expectedRefusals =
    [ ("examples/rejected/array_push.tersus", "argument 1 of push: expected List<?>, got Array<Int, 2>")
    , ("examples/rejected/array_runtime_size.tersus", "the size of an array must be a constant")
    , ("examples/rejected/array_size_mismatch.tersus", "argument 2 of dot: expected Array<Int, 5>, got Array<Int, 4>")
    , ("examples/rejected/array_size_param_mismatch.tersus", "argument 2 of dot: expected Array<Int, 2>, got Array<Int, 3>")
    , ("examples/rejected/array_unsized.tersus", "an array with no size")
    , ("examples/rejected/box_array_size.tersus", "argument 1 of corner: expected Box<Array<Int, 3>>, got Box<Array<Int, ?>>")
    , ("examples/rejected/box_infinite_size.tersus", "Chain holds itself, so it would have no size")
    , ("examples/rejected/call_undefined.tersus", "Undefined variable: nowhere")
    , ("examples/rejected/for_assigns_counter.tersus", "The body of a for loop cannot assign its loop variable i")
    , ("examples/rejected/list_element_mismatch.tersus", "argument 2 of push: expected Bool, got Int")
    , ("examples/rejected/sized_struct_mismatch.tersus", "argument 1 of first: expected Packet<3>, got Packet<2>")
    , ("examples/rejected/struct_field_type.tersus", "field value of Node: expected Int, got Bool")
    , ("examples/rejected/trait_ambiguous_call.tersus", "Counter::label is ambiguous")
    , ("examples/rejected/trait_missing_function.tersus", "impl Step for Counter lacks the function total")
    , ("examples/rejected/type_argument_mismatch.tersus", "argument 1 of size: expected List<?>, got Int")
    , ("examples/rejected/type_return_mismatch.tersus", "returned value: expected Int, got List<Int>")
    ]

examplesLower :: IO TestResult
examplesLower = do
    units <- suiteUnits
    let paths = [path | SourceFile path <- units]
    result <- unitsLower [SourceFile path | path <- paths]
    pure $
        firstLowering
            [ case [path | (path, _) <- expectedRefusals, path `notElem` paths] of
                [] -> Nothing
                gone -> Just ("expected refusals of examples that are not there: " ++ unwords gone)
            , testAssertTrue (length paths > length expectedRefusals)
            , result
            ]

-- One lowering the compiler takes from the elaborator, through Lowering.lowerAccepted: its module and what it gave
type UnitLowering = (String, Result Lowered String)

unitsLower :: [Unit] -> IO TestResult
unitsLower units = do
    found <- mapM unitLowerings units
    pure $ firstLowering [either (\e -> Just (show unit ++ ": " ++ e)) (firstLowering . map checkLowering) (resultEither r) | (unit, r) <- zip units found]
  where
    resultEither r = case r of
        Ok a -> Right a
        Error e -> Left e

-- (the libraries have functions with bounds and name copies of them, so their round trips cover those records)
librariesLower :: IO TestResult
librariesLower = do
    result <- unitsLower [Libraries]
    pure $ firstLowering
        [ result
        , case libraryLowerings of
            Ok lowerings ->
                let programs = [lowProgram raw | (_, Ok raw) <- lowerings]
                 in testAssertTrue (any (not . Map.null . progBounded) programs && any (not . Map.null . progInstances) programs)
            Error e -> Just e
        ]

unitLowerings :: Unit -> IO (Result [UnitLowering] String)
unitLowerings unit = case unit of
    SourceFile path -> fileLowering path <$> readFile path
    EmbeddedPackage entry -> pure (packageLowerings (embeddedFiles entry) entry)
    FilePackage entry -> (`packageLowerings` entry) <$> Mod.snapshotFromFilesystem entry
    Libraries -> pure libraryLowerings
    SourceText label source -> pure (fileLowering label source)
  where
    embeddedFiles entry
        | entry == validationEntry = validationPackageFiles
        | "lib/elaborate/" `isPrefixOf` entry = elaboratePackageFiles
        | otherwise = toolPackageFiles

-- A single file as Compile.lowerSourceUsing asks for it; a refusal only where one is expected
fileLowering :: String -> String -> Result [UnitLowering] String
fileLowering label source = libPackage `bindResult` \pkg -> case (sourceLoader (sourceRequest LoadProgram False True (libCatalog pkg) source), lookup label expectedRefusals) of
    (LoadedProgram response@Accepted{}, Nothing) -> Ok [(label, lowerAccepted response)]
    (LoadedProgram Accepted{}, Just _) -> Error "accepted, but a refusal was expected"
    (answer, expected) -> case (refusal answer, expected) of
        (Just message, Just wanted)
            | wanted `isInfixOf` message -> Ok []
            | otherwise -> Error ("refused, but not as expected: " ++ message)
        (Just message, Nothing) -> Error ("refused: " ++ message)
        (Nothing, _) -> Error "the loader did not answer with the program's elaboration"
  where
    refusal answer = case answer of
        LoadedProgram (Refused m) -> Just m
        LoadedProgram (RefusedInterface m) -> Just m
        LoadedProgram (Unresolved m) -> Just m
        LoadedProgram (NotModelled m) -> Just m
        NotLoaded m -> Just m
        Unparsed m -> Just m
        _ -> Nothing

packageLowerings :: [(FilePath, String)] -> FilePath -> Result [UnitLowering] String
packageLowerings files entry =
    Package.compileModulesUsing sourceLoader libPackage (Mod.Snapshot (Mod.resolverFromFiles files) entry False) `bindResult` \compiled ->
        case Package.compiledModules compiled of
            [] -> Error "a package without modules"
            modules -> Ok [(Mod.renderModuleId (Package.compiledModuleId m), Package.compiledLowered m) | m <- modules]

-- As LibPackage takes each library's unit; every library answers
libraryLowerings :: Result [UnitLowering] String
libraryLowerings = case bootstrapLoader (LoadRequest LoadLibraries False (Mod.resolverFromFiles []) Nothing Mod.librarySources []) of
    LoadedLibraries answers Nothing
        | sort [label | LibraryAnswer label _ _ _ <- answers] == sort [label | (label, _, _) <- libModules] -> libraries answers
        | otherwise -> Error "the libraries that answered are not PreludeSource.libModules"
    LoadedLibraries _ (Just e) -> Error e
    _ -> Error "the loader did not answer with the compiler libraries"
  where
    libraries [] = Ok []
    libraries (LibraryAnswer label _ _ response : rest) = case response of
        Accepted (Just _) _ _ -> mapResult (("tersuslib::" ++ label, lowerAccepted response) :) (libraries rest)
        _ -> Error ("library " ++ label ++ " was not accepted with an interface")

-- The lowering succeeded and round trips
checkLowering :: UnitLowering -> TestResult
checkLowering (label, lowered) = fmap ((label ++ ": ") ++) $ case lowered of
    Error e -> Just ("lowering failed: " ++ e)
    Ok raw -> loweredRoundTrip raw

nestedProgram :: String
nestedProgram = "fn outer(x: Int) -> Int { struct Hidden { n: Int }; return x; };\nreturn outer(0);"

nestedInPackage :: TestResult
nestedInPackage = case packageLowerings [("app/package.tersus", ""), ("app/main.tersus", nestedProgram)] "app/main.tersus" of
    Error e -> Just e
    Ok [lowering@(_, Ok raw)] -> firstLowering [checkLowering lowering, testAssertEq (lowDeclared raw, lowNested raw) (Set.fromList ["outer"], Set.fromList ["Hidden"])]
    Ok other -> Just ("not one lowered module: " ++ show [label | (label, _) <- other])

nestedInFile :: TestResult
nestedInFile = case fileLowering "nested" nestedProgram of
    Error e -> Just e
    Ok [lowering@(_, Ok raw)] -> firstLowering [checkLowering lowering, testAssertEq (lowDeclared raw, lowNested raw) (Set.fromList ["outer"], Set.fromList ["Hidden"])]
    Ok _ -> Just "not one lowered program"

finishedInstances :: TestResult
finishedInstances = case fileLowering "instances" "struct Pair<T> { a: T, b: T };\np = Pair<Int> { a: 1, b: 2 };\nreturn p.a;" of
    Ok [(_, Ok raw)] ->
        firstLowering
            [ testAssertEq (Map.keys (progTypes (lowProgram raw))) []
            , testAssertTrue (any isPosition (concatMap blockStatements (allBlocks (lowProgram raw))))
            , testAssertEq (mapResult renderProgram (finishLowered raw)) (Ok (unlines
                [ "struct Pair<Int> { a: Int, b: Int }"
                , ""
                , "fn main() -> Int {"
                , "    let _0: Int;"
                , "    let _1: Pair<Int>; // p"
                , "    bb0: {"
                , "        _1 = Pair<Int> { a: const 1, b: const 2 };"
                , "        _0 = (_1 as Pair<Int>).a;"
                , "        return;"
                , "    }"
                , "}"
                ]))
            ]
    other -> Just ("not one lowered program: " ++ take 300 (show [(label, r) | Ok ls <- [other], (label, r) <- ls]))
  where
    allBlocks program = concatMap (Map.elems . fnBlocks) (progMain program : Map.elems (progFunctions program))
    isPosition stmt = case stmt of
        Ghost _ GhostPosition{} -> True
        _ -> False

finishedMoveError :: TestResult
finishedMoveError = case fileLowering "moves" "x = [1];\ny = x;\nz = x;\nreturn size(z);" of
    Ok [(_, Ok raw)] -> testAssertEq (mapResult renderProgram (finishLowered raw)) (Error "Move error: in main, line 3:1: x was moved at line 2:1 and cannot be used again: write clone(x) where it is moved to keep it")
    _ -> Just "not one lowered program"

finishedStubs :: TestResult
finishedStubs = case packageLowerings files "app/main.tersus" of
    Ok [(_, Ok _), (_, Ok raw)] ->
        firstLowering
            [ testAssertEq (Set.toList (lowStubs raw), Map.keys (progFunctions (lowProgram raw))) (["app$util$util$twice"], ["app$util$util$twice"])
            , testAssertEq (mapResult renderProgram (finishLowered raw)) (Ok (unlines
                [ "fn main() -> Int {"
                , "    let _0: Int;"
                , "    bb0: {"
                , "        _0 = call app$util$util$twice(const 2) -> bb1;"
                , "    }"
                , "    bb1: {"
                , "        return;"
                , "    }"
                , "}"
                ]))
            ]
    other -> Just ("not two lowered modules: " ++ either' other)
  where
    files = [("app/package.tersus", ""), ("app/main.tersus", "import app::util::twice;\nreturn twice(2);"), ("app/util/util.tersus", "fn twice(x: Int) -> Int [{ }] [{ }] { return x + x; };")]
    either' r = case r of
        Ok ls -> show [label | (label, _) <- ls]
        Error e -> e

bigIntegerStatements :: TestResult
bigIntegerStatements = case elaborateStatements [S.Return (S.Val (S.VInt (2 ^ (63 :: Int))))] of
    Ok raw -> loweredRoundTrip raw
    Error e -> Just e

withLocal :: Local -> Type -> Rvalue -> Lowered -> Lowered
withLocal l t rv lowered =
    lowered{lowProgram = program{progFunctions = Map.adjust addLocal "f" (progFunctions program)}}
  where
    program = lowProgram lowered
    addLocal f =
        f
            { fnLocals = Map.insert l (LocalDecl t Nothing) (fnLocals f)
            , fnBlocks = Map.adjust (\(BasicBlock stmts term) -> BasicBlock (stmts ++ [Assign l rv]) term) (BlockId 1) (fnBlocks f)
            }

loweredRoundTrip :: Lowered -> TestResult
loweredRoundTrip raw = case writeLowered raw of
    Error e -> Just ("not written: " ++ e)
    Ok text -> case readLowered text of
        Error e -> Just ("not read back: " ++ e)
        Ok back
            | back /= raw -> Just ("read back differently: " ++ unwords (loweredDifferences raw back))
            -- (Eq on a builtin's value ignores its metadata, which show keeps)
            | show back /= show raw -> Just "read back with different builtin metadata"
            | writeLowered back /= Ok text -> Just "written differently the second time"
            | otherwise -> Nothing

loweredDifferences :: Lowered -> Lowered -> [String]
loweredDifferences a b =
    [ part
    | (part, same) <-
        [ ("types", progTypes pa == progTypes pb)
        , ("generics", progGenerics pa == progGenerics pb)
        , ("invariants", progInvariants pa == progInvariants pb)
        , ("bounded", progBounded pa == progBounded pb)
        , ("instances", progInstances pa == progInstances pb)
        , ("main", progMain pa == progMain pb)
        , ("copies", lowCopies a == lowCopies b)
        , ("linear", lowLinear a == lowLinear b)
        , ("drops", lowDrops a == lowDrops b)
        , ("stubs", lowStubs a == lowStubs b)
        , ("declared", lowDeclared a == lowDeclared b)
        , ("nested", lowNested a == lowNested b)
        , ("assumes", lowAssumes a == lowAssumes b)
        ]
    , not same
    ]
        ++ [fnName f | f <- Map.elems (progFunctions pa), Map.lookup (fnName f) (progFunctions pb) /= Just f]
        ++ [fnName f | f <- Map.elems (progFunctions pb), Map.notMember (fnName f) (progFunctions pa)]
  where
    pa = lowProgram a
    pb = lowProgram b

firstLowering :: [TestResult] -> TestResult
firstLowering results = case [e | Just e <- results] of
    e : _ -> Just e
    [] -> Nothing

everyRecord :: Lowered
everyRecord =
    Lowered
        { lowProgram =
            Program
                { progTypes = Map.fromList [("P", StructDecl [("x", TInt)]), ("E", EnumDecl [("E::A", []), ("E::B", [("y", TBool)])])]
                , progFunctions = Map.singleton "f" f
                , progMain = mainFn
                , progGenerics = Map.singleton "G" (["n"], [("a", TArrayOf TInt (SizeParam "n"))])
                , progInvariants = Map.singleton "P" [holds]
                , progBounded = Map.singleton "f" (BoundedFn ["n"] ["T"] ["f::g"] [PackLoop (BlockId 1) (BlockId 2) (BlockId 3) [BlockId 2, BlockId 4] [Local 7, Local 8] (Local 4) (Local 6) "..T@0" (Local 2) (Local 3) Nothing, PackLoop (BlockId 5) (BlockId 6) (BlockId 7) [BlockId 6] [] (Local 9) (Local 10) "..T@1" (Local 11) (Local 12) (Just (Local 13))])
                , progInstances = Map.fromList [("f[Int, 3]", ("f", [ArgType TInt, ArgSize (SizeConst 3)])), ("g[T]", ("f", [ArgType (TParam "T")])), ("<$param T as Hash>::hash", ("", []))]
                }
        , lowCopies = Set.singleton "P"
        , lowLinear = Set.singleton "E"
        , lowDrops = Set.empty
        , lowStubs = Set.singleton "g"
        , lowDeclared = Set.fromList ["P", "f"]
        , lowNested = Set.singleton "Q"
        , lowAssumes = [S.CTerm (S.VBool False)]
        }
  where
    holds = S.ProofAssert (S.CTerm (S.VBool True))
    env = Map.fromList [("n", Copy (Local 1)), ("f", Const (CFn "f"))]
    f =
        Function
            { fnName = "f"
            , fnParams = [Local 1]
            , fnReturns = Just TInt
            , fnLocals = Map.fromList [(Local 0, LocalDecl TInt Nothing), (Local 1, LocalDecl TInt (Just "n"))]
            , fnBlocks =
                Map.fromList
                    [ ( BlockId 0
                      , BasicBlock
                            [ Ghost env (GhostPosition 3 4)
                            , Ghost env (GhostValidation holds)
                            , Ghost env (GhostAxiom "ax" ["a"] [holds] [])
                            , Ghost env (GhostProof "pr" [] [] [holds] [holds])
                            , Ghost Map.empty (GhostFunction "f::g" "g" False)
                            , Ghost env (GhostDissolve (Local 1))
                            ]
                            (Goto (BlockId 1))
                      )
                    , (BlockId 1, BasicBlock [Assign (Local 0) (Use (Copy (Local 1)))] Return)
                    ]
            , fnSizeParams = []
            , fnTypeParams = []
            , fnBorrowed = []
            , fnMutBorrowed = []
            , fnFrom = []
            , fnSpec = FunctionSpec [holds] [] (Just (S.Shrinks (S.Var "n"))) (Map.singleton (BlockId 1) (LoopSpec [holds] (Just S.MayDiverge) env (BlockId 1))) env ["n"] [] []
            }
    mainFn =
        Function
            { fnName = "main"
            , fnParams = []
            , fnReturns = Nothing
            , fnLocals = Map.empty
            , fnBlocks = Map.singleton (BlockId 0) (BasicBlock [] Return)
            , fnSizeParams = []
            , fnTypeParams = []
            , fnBorrowed = []
            , fnMutBorrowed = []
            , fnFrom = []
            , fnSpec = emptySpec
            }

refusedLowered :: String -> ([String] -> [String]) -> TestResult
refusedLowered expected broken = case writeLowered everyRecord of
    Error e -> Just e
    Ok text -> case readLowered text of
        Error e -> Just ("the unbroken unit is refused: " ++ e)
        Ok _ -> testAssertErrorContains expected (readLowered (unlines (broken (lines text))))

-- Broken copies of everyRecord's text, each with what its refusal says
malformedLowered :: [(String, String, [String] -> [String])]
malformedLowered =
    [ ("another version", "tersus-mir 3", \ls -> "tersus-mir 2" : drop 1 ls)
    , ("an unknown statement", "not a statement or a terminator", onFirst (== "return") (const "retrun"))
    , ("an unknown ghost statement", "not a ghost statement", onFirst ("ghost position" `isPrefixOf`) (\l -> "ghost place" ++ drop 14 l))
    , ("an unknown record of the unit", "does not end with", \ls -> let (before, after) = break ("copies " `isPrefixOf`) ls in before ++ ["bogus 1"] ++ after)
    , ("a payload that does not exist", "no payload 99", onFirst isSpec (setWord 2 "99"))
    , ("a payload of the wrong kind", "is not a list of validation statements", \ls ->
        let requires = wordOf 2 (firstLine isSpec ls)
            validation = last (words (firstLine ("ghost validation" `isPrefixOf`) ls))
         in onFirst ("ghost validation" `isPrefixOf`) (\l -> unwords (init (words l) ++ [requires])) (onFirst isSpec (setWord 2 validation) ls))
    , ("a payload referred to twice", "referred to twice", \ls -> onFirst isSpec (setWord 4 (wordOf 2 (firstLine isSpec ls))) ls)
    , ("a payload referred to by nothing", "not referred to", onFirst isSpec (setWord 6 "none"))
    , ("a local twice", "duplicate local", duplicateFirst ("local 1 " `isPrefixOf`))
    , ("a block twice", "duplicate block", onFirst (== "block 1") (const "block 0"))
    , ("a loop twice", "duplicate loop", duplicateFirst ("loop " `isPrefixOf`))
    , ("a name twice in an environment", "a name twice in an environment", onFirst (== "env 0 1 \"n\" copy 1") (const "env 0 2 \"n\" copy 1 \"n\" copy 0"))
    , ("a shared environment that does not exist", "no shared environment 7", onFirst (== "env 0 1 \"n\" copy 1") (const "env 7 1 \"n\" copy 1"))
    , ("a name twice in a set", "a name twice in copies", onFirst ("copies " `isPrefixOf`) (const "copies 2 \"P\" \"P\""))
    , ("no payload block", "without its payload block", takeWhile (not . ("data " `isPrefixOf`)))
    , ("a payload block cut short", "not as long", init)
    , ("a function without its spec", "spec and env", filter (not . isSpec))
    , ("the sets out of order", "expected the linear record", \ls ->
        let (before, rest) = break ("linear " `isPrefixOf`) ls
         in case rest of
                l : d : after -> before ++ [d, l] ++ after
                _ -> ls)
    , ("a payload record that is not one", "unknown tag", onFirst ("StatementsEnd" `isPrefixOf`) (const "StatementsEnding"))
    , ("a negative count of names", "not a count of what follows", onFirst ("copies " `isPrefixOf`) (const "copies -1"))
    , ("a negative count of assumes", "not a count of what follows", onFirst ("assumes " `isPrefixOf`) (const "assumes -1"))
    , ("a negative count in an environment", "not a count of what follows", onFirst (== "env 0 1 \"n\" copy 1") (const "env 0 -1"))
    , ("a negative count of parameters", "not a count of what follows", onFirst (header `isPrefixOf`) (\l -> "function \"f\" params -1 " ++ drop (length header) l))
    , ("a negative count in a constant", "not a count of what follows", onFirst (== "assign 0 use copy 1") (const "assign 0 use const list -1"))
    , ("a negative count in a type", "not a count of what follows", onFirst (== "local 0 none int") (const "local 0 none fn -1 int"))
    , ("a count larger than what follows", "not a count of what follows", onFirst ("copies " `isPrefixOf`) (const "copies 5 \"P\""))
    , ("a payload count that wraps", "not as long", onFirst ("data " `isPrefixOf`) (\l -> "data " ++ show (2 ^ (64 :: Int) + read (drop 5 l) :: Integer)))
    , ("a shared environment that wraps", "no shared environment", onFirst (== "env 0 1 \"n\" copy 1") (const "env 18446744073709551616 1 \"n\" copy 1"))
    , ("a function with bounds twice", "duplicate bounded", duplicateFirst ("bounded " `isPrefixOf`))
    , ("an instance argument that is not one", "not an argument", onFirst ("instance \"f[Int, 3]\"" `isPrefixOf`) (const "instance \"f[Int, 3]\" \"f\" 1 kind int"))
    , ("a local out of range", "a number out of range", onFirst ("local 1 " `isPrefixOf`) (\l -> "local 18446744073709551617 " ++ drop 8 l))
    ]
  where
    isSpec = ("spec " `isPrefixOf`)
    header = "function \"f\" params 1 1 "
    firstLine p ls = head ([l | l <- ls, p l] ++ [""])
    wordOf n l = words l !! n
    setWord n w l = unwords [if i == n then w else x | (i, x) <- zip [0 :: Int ..] (words l)]
    onFirst p change ls = case break p ls of
        (before, l : after) -> before ++ change l : after
        _ -> ls
    duplicateFirst p ls = case break p ls of
        (before, l : after) -> before ++ l : l : after
        _ -> ls

-- Variadic functions whose lowering the programs of TestVariadic do not reach: a borrow of an element at a number, a range
-- loop past the pack, validation statements that read the pack, a pack loop after a return, and slices forwarded
refusedVariadic :: String
refusedVariadic = "validation statements that read the pack"

variadicLowering :: [(String, String)]
variadicLowering =
    [ ("a borrow of an element at a number", "fn sz<T>(r: &T) -> Int { return 1; }; fn f<..T>(args: &..T) -> Int [{ affirm size(args) >= 1; }] [{ }] {\n    r = &get(args, 0);\n    return sz(r);\n};\nreturn f(1, true);")
    , ("a range loop past the pack", "fn f<..T>(args: &..T) -> Int {\n    t = 0;\n    for i in 0..size(args) + 1 { t = t + i; };\n    return t;\n};\nreturn f(1, true);")
    , ("validation statements that read the pack", "fn f<..T>(args: &..T) -> Int {\n    affirm size(args) >= 0;\n    define n = size(args);\n    return n;\n};\nreturn f(1, true);")
    , ("a loop over the pack after a return", "fn f<..T>(args: &..T) -> Int {\n    return 0;\n    for a in args { };\n};\nreturn f(1);")
    , ("a slice forwarded after a fixed argument", "fn g<..U>(k: Int, rest: &..U) -> Int { return k + size(rest); };\nfn f<..T>(args: &..T) -> Int [{ affirm size(args) >= 2; }] [{ }] {\n    return g(10, slice(args, 1, 2));\n};\nreturn f(1, true);")
    , ("the head and the rest forwarded by value in one call", "fn eat<T>(x: T) -> Int { return 1; };\nfn g<A, ..U>(x: A, rest: ..U) -> Int { n = eat(x); for a in rest { n = n + eat(a); }; return n; };\nfn f<..T>(args: ..T) -> Int [{ affirm size(args) >= 1; }] [{ }] {\n    return g(get(args, 0), slice(args, 1, size(args)));\n};\nreturn f(push([], 1), push([], 2));")
    , ("a forward in a loop over the pack", "fn g<..U>(rest: &..U) -> Int { return size(rest); };\nfn f<..T>(args: &..T) -> Int {\n    t = 0;\n    for i in 0..size(args) { t = t + g(slice(args, i, size(args))); };\n    return t;\n};\nreturn f(1, 2, 3);")
    ]
