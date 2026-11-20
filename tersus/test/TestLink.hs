{-# LANGUAGE PatternSynonyms #-}
module TestLink (testLink, testLinkNative, linkProbeProgram, probeSource) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Exception (evaluate)
import Data.IORef (newIORef, readIORef, writeIORef)
import System.IO.Unsafe (unsafePerformIO)
import qualified Native
import qualified MirHousekeeping as Housekeeping
import Seed (cachedSeed, seedHash)
import ValidatorNative (validateCompiled)
import Pipeline (oneMarkerEach)
import System.Exit (ExitCode(..))

import Data.List (isInfixOf, isPrefixOf, nubBy)
import qualified Data.ByteString.Char8 as B
import AstData (readMirPayloadBytes, writeMirPayloadLines)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import DataCodec (quote)
import qualified Mir as M
import MirCopies (makeCopies, makeCopiesWith, genericKey, coveredKey)
import qualified Link as ProductionLink
import qualified Compile
import qualified MirLists
import MirMoves (finishLowered)
import MirData (readLowered, writeLowered)
import qualified MirData
import MirEval (RunEnv (..), Outcome (..), MirValue (..), runProgramEnv)
import MirPass (programData)
import ElaboratorTool (bootstrapLoader)
import LibPackage (libPackage)
import PackageCompile (CompiledModule (..), CompiledPackage (..), compileModulesUsing, lowerCompiledPackage)
import PackageData (ModuleId (..), Snapshot (..), resolverFromFiles)
import PreludeSource (toolPackageFiles)
import Hash (fingerprint)
import TestMirData (everyRecord, malformedLowered)
import qualified Syntax as S
import Types (Type (..), Arg (..), Size (..), BuiltinFunct (..), pattern TList, pattern TBox)
import TestHarness
import Utils

probeSource :: String
probeSource = unlines
    [ "import data::reader::reader { readRecords, tokenizeMir };"
    , "import mir::full::full { fullAt, printFull };"
    , "import mir::link::link { isLinkRequest, runLink };"
    , "r = readRecords(0 - 1); if !r.ok { return 1; };"
    , "rows = []; for line in &r.value { ts = tokenizeMir(line); if !ts.ok { return 1; }; rows = push(rows, ts.value); };"
    , "if isLinkRequest(&rows) { if !runLink(&rows) { return 1; }; } else { p = fullAt(&rows); if !p.ok { return 1; }; printFull(&p.value); };"
    ]

linkProbeProgram :: Result M.Program String
linkProbeProgram = compileModulesUsing bootstrapLoader libPackage (Snapshot (resolverFromFiles files) "lib/probe/driver.tersus" False) `bindResult` lowerCompiledPackage
  where
    files = toolPackageFiles ++ [("lib/probe/package.tersus", ""), ("lib/probe/driver.tersus", probeSource)]

asUnit :: M.Program -> M.Lowered
asUnit p = M.Lowered p Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty []

{-# NOINLINE nativeToolBox #-}
nativeToolBox :: MVar (Maybe (Result FilePath String))
nativeToolBox = unsafePerformIO (newMVar Nothing)

nativeLinkTool :: IO (Result FilePath String)
nativeLinkTool = modifyMVar nativeToolBox $ \cached -> case cached of
    Just tool -> pure (cached, tool)
    Nothing -> do
        seed <- cachedSeed
        result <- case (seed, linkProbeProgram) of
            (Error e, _) -> pure (Error e)
            (_, Error e) -> pure (Error e)
            (Ok emitter, Ok source) -> do
                owned <- Housekeeping.ownedWith emitter source
                case owned of
                    Error e -> pure (Error e)
                    Ok program -> do
                        let input = MirData.writeProgram program
                            key = Housekeeping.ownedContentKey seedHash input []
                        Native.cachedProgram "link-test" key "the Link test tool" $ \output -> do
                            ir <- Native.runWithInput emitter input
                            case ir of Error e -> pure (Error e); Ok llvm -> Native.buildExecutable output llvm
        pure (Just result, result)

{-# NOINLINE actualEmitterBox #-}
actualEmitterBox :: MVar (Maybe (Result FilePath String))
actualEmitterBox = unsafePerformIO (newMVar Nothing)

actualEmitterTool :: IO (Result FilePath String)
actualEmitterTool = modifyMVar actualEmitterBox $ \cached -> case cached of
    Just tool -> pure (cached, tool)
    Nothing -> do
        seed <- cachedSeed
        result <- case seed of
            Error e -> pure (Error e)
            Ok emitter -> do
                owned <- Housekeeping.ownedToolWith emitter Housekeeping.emitterEntry
                case owned of
                    Error e -> pure (Error e)
                    Ok program -> do
                        let input = MirData.writeProgram program
                            key = Housekeeping.ownedContentKey seedHash input []
                        Native.cachedProgram "emitter" key "the actual Full pass entry" $ \output -> do
                            ir <- Native.runWithInput emitter input
                            case ir of Error e -> pure (Error e); Ok text -> Native.buildExecutable output text
        pure (Just result, result)

actualEntryRefusal :: String -> TestResult -> IO TestResult
actualEntryRefusal input control = do
    tool <- actualEmitterTool
    case tool of
        Error e -> pure (Just e)
        Ok executable -> do
            (_, out, errors) <- Native.runWithInputFull executable input
            pure $ firstFailure [control, testAssertEq out "1\n", testAssertTrue (not (null errors))]

nativeFull :: String -> IO (Result M.Lowered String)
nativeFull input = do
    tool <- nativeLinkTool
    case tool of
        Error e -> pure (Error e)
        Ok executable -> do
            (code, out, errors) <- Native.runWithInputFull executable input
            pure $ case code of
                ExitSuccess | out /= "1\n" && null errors -> readLowered out
                _ | not (null errors) -> Error (reverse (dropWhile (== '\n') (reverse (decodeUtf8 errors))))
                _ -> Error ("native Link tool did not write a unit: " ++ take 80 out)

nativeMerge :: [(ModuleId, M.Program)] -> IO (Result M.Program String)
nativeMerge units = case mergeInput units of
    Error e -> pure (Error e)
    Ok input -> do
        result <- nativeFull input
        pure $ case result of
            Error message -> Error message
            Ok raw -> copiesForUnits units (M.lowProgram raw)

nativeMergeBeforeCopies :: [(ModuleId, M.Program)] -> IO (Result M.Program String)
nativeMergeBeforeCopies units = case mergeInput units of
    Error e -> pure (Error e)
    Ok input -> fmap (mapResult M.lowProgram) (nativeFull input)

positiveMerge :: [(ModuleId, M.Program)] -> (M.Program -> TestResult) -> IO TestResult
positiveMerge units check = do
    actual <- nativeMergeBeforeCopies units
    pure (inspect actual check)

retainedGenericUnits :: Result [(ModuleId, M.Program)] String
retainedGenericUnits = compileModulesUsing bootstrapLoader libPackage snapshot `bindResult` \compiled ->
    let lowerOne modu = mapResult ((,) (compiledModuleId modu)) (compiledLowered modu `bindResult` finishLowered)
        libraries = nubBy (\(a, _) (b, _) -> a == b) (concatMap compiledLibUnits (compiledModules compiled))
    in mapResult (libraries ++) (flatResultMap lowerOne (compiledModules compiled))
  where
    snapshot = Snapshot (resolverFromFiles [("app/package.tersus", ""), ("app/main.tersus", source)]) "app/main.tersus" False
    source = "struct Holder<T> { value: T }; fn bounded<T: Copy>(x: T) -> T [{ }] [{ affirm true; }] { affirm true; return x; }; fn generic<T>(xs: &List<T>) -> Int { return size(xs); }; xs = [1, 2]; h = Holder { value: xs }; return bounded(generic(&h.value));"

retainedGenericMetadata :: M.Program -> TestResult
retainedGenericMetadata p = firstFailure
    [ testAssertTrue (Map.member "Holder" (M.progGenerics p))
    , testAssertTrue (Map.member "bounded" (M.progBounded p) && Map.member "bounded[Int]" (M.progInstances p))
    , testAssertTrue ("generic" `elem` calls && "bounded[Int]" `elem` calls)
    , case (Map.lookup "generic" (M.progFunctions p), Map.lookup "bounded" (M.progFunctions p)) of
        (Just generic, Just bounded) -> firstFailure
            [ testAssertEq (M.fnTypeParams generic) ["T"]
            , testAssertEq (M.fnTypeParams bounded) ["T"]
            , testAssertTrue (not (null (M.specEnsures (M.fnSpec bounded))))
            ]
        _ -> Just "the retained source templates disappeared before copies"
    , testAssertTrue (not (null [() | f <- M.progMain p : Map.elems (M.progFunctions p), b <- Map.elems (M.fnBlocks f), M.Ghost _ _ <- M.blockStatements b]))
    ]
  where
    calls = [name | block <- Map.elems (M.fnBlocks (M.progMain p)), M.Call (M.Const (M.CFn name)) _ _ _ <- [M.blockTerminator block]]

realInputChecks :: IO TestResult
realInputChecks = do
    helpers <- Housekeeping.listLibrary
    case (helpers, Housekeeping.toolProgram Housekeeping.mirVerifyEntry) of
        (Error e, _) -> pure (Just e)
        (_, Error e) -> pure (Just e)
        (Ok units, Ok prepared) -> do
            captured <- newIORef Nothing
            let capture inputs = unsafePerformIO (writeIORef captured (Just inputs) >> pure (ProductionLink.linkPrograms inputs))
                aligned = Housekeeping.eraseGhosts prepared `bindResult` Housekeeping.expandRefWrites `bindResult` MirLists.lowerListsWith capture (Ok units)
            helperProgram <- evaluate aligned
            inputs <- readIORef captured
            helperResult <- case (helperProgram, inputs) of
                (Error e, _) -> pure (Just e)
                (_, Nothing) -> pure (Just "the real native lowering never called its helper linker")
                (Ok native, Just actualUnits) -> do
                    compared <- positiveMerge actualUnits (\p -> firstFailure
                        [ testAssertTrue (Map.member "listNew" (M.progFunctions p))
                        , testAssertTrue (not (null [() | f <- M.progMain p : Map.elems (M.progFunctions p), b <- Map.elems (M.fnBlocks f), M.Call (M.Const (M.CFn name)) _ _ _ <- [M.blockTerminator b], name `elem` ["listNew", "listPush"]]))
                        ])
                    pure (firstFailure
                        [ testAssertTrue (any (\(m, _) -> m == ModuleId "tersuslib" (Just "lists")) actualUnits)
                        , testAssertTrue (Map.member "listNew" (M.progFunctions native))
                        , compared
                        ])
            genericResult <- case retainedGenericUnits of
                Error e -> pure (Just e)
                Ok inputs' -> positiveMerge inputs' retainedGenericMetadata
            pruneResult <- case programData prepared of Error e -> pure (Error e); Ok text -> nativeFull ("pass link\nprune\n" ++ text)
            envResult <- case programData prepared of Error e -> pure (Error e); Ok text -> nativeFull ("pass link\nenvironments\n" ++ text)
            pure $ firstFailure
                [ helperResult
                , genericResult
                , inspect (mapResult M.lowProgram pruneResult) (pruneEffects prepared)
                , inspect (mapResult M.lowProgram envResult) (completionEffects prepared)
                ]

pruneEffects :: M.Program -> M.Program -> TestResult
pruneEffects before after = firstFailure
    [ testAssertTrue (not (Map.null (M.progFunctions after)))
    , testAssertTrue (Map.keysSet (M.progFunctions after) `Set.isSubsetOf` Map.keysSet (M.progFunctions before))
    , testAssertTrue (Map.isSubmapOf (M.progTypes after) (M.progTypes before))
    , testAssertEq (M.progGenerics after) (M.progGenerics before)
    , testAssertEq (Map.map M.blockTerminator (M.fnBlocks (M.progMain after)))
        (Map.map M.blockTerminator (M.fnBlocks (M.progMain before)))
    ]

completionEffects :: M.Program -> M.Program -> TestResult
completionEffects before after = firstFailure
    [ testAssertEq (Map.keys (M.progFunctions after)) (Map.keys (M.progFunctions before))
    , testAssertEq (M.fnSpec (M.progMain after)) (M.fnSpec (M.progMain before))
    , testAssertEq (after{M.progFunctions = M.progFunctions before, M.progMain = M.progMain before}) before
    ]

testLinkNative :: Test
testLinkNative = TestList "testLinkNative"
    ([TestCase label $ checkLinked expected <$> nativeMerge units | (label, units, expected) <- linkCases]
    ++ [ TestCase "production Link validates only used compiler-library bounded templates" libraryBoundedRetention
       , TestCase "actual prepared compiler/helper/generic inputs" realInputChecks
       , TestCase "native pruning preserves the entry and reachable program structure on actual owned MIR" $ do
            seed <- cachedSeed
            case (seed, Housekeeping.toolProgram Housekeeping.mirVerifyEntry) of
                (Error e, _) -> pure (Just e)
                (_, Error e) -> pure (Just e)
                (Ok emitter, Ok prepared) -> do
                    owned <- Housekeeping.ownedWith emitter prepared
                    case owned of
                        Error e -> pure (Just e)
                        Ok p -> case programData p of
                            Error e -> pure (Just e)
                            Ok text -> do
                                actual <- nativeFull ("pass link\nprune\n" ++ text)
                                pure (firstFailure
                                    [ testAssertTrue (any (isPrefixOf "listNew") (Map.keys (M.progFunctions p)))
                                    , inspect (mapResult M.lowProgram actual) (pruneEffects p)
                                    ])
       , TestCase "native prune keeps ghost expression control-flow references" $ do
            actual <- case programData expressionForms of
                Error e -> pure (Error e)
                Ok text -> nativeFull ("pass link\nprune\n" ++ text)
            pure (firstFailure
                [ checkLinked (Right "7f3e3b756a3fbc3c") (mapResult M.lowProgram actual)
                , inspect (mapResult M.lowProgram actual) expressionFormEffects
                ])
       , TestCase "native mixed assume and return payload round trip" $ case writeLowered mixedAssumes of
            Error e -> pure (Just e)
            Ok input -> do
                result <- nativeFull input
                pure $ inspect result $ \back -> firstFailure
                    [ testAssertTrue (mixedAssumes == back && show mixedAssumes == show back)
                    , testAssertEq (writeLowered back) (Ok input)
                    ]
       , TestCase "full payload native round trip" $ case writeLowered everyRecord of
            Error e -> pure (Just e)
            Ok input -> do result <- nativeFull input; pure $ inspect result $ \back -> testAssertTrue (everyRecord == back && show everyRecord == show back)
       , TestCase "large distinct shared maps native round trip" $ case writeLowered (asUnit (largeMaps 0)) of
            Error e -> pure (Just e)
            Ok input -> do
                tool <- nativeLinkTool
                case tool of
                    Error e -> pure (Just e)
                    Ok executable -> do
                        (code, out, errors) <- Native.runWithInputFull executable input
                        pure $ firstFailure [testAssertEq code ExitSuccess, testAssertEq errors "", testAssertEq out input]
       , TestCase "native reachability/environment parity" $ do
            a <- case programData reachable of Error e -> pure (Error e); Ok t -> nativeFull ("pass link\nprune\n" ++ t)
            b <- case programData environments of Error e -> pure (Error e); Ok t -> nativeFull ("pass link\nenvironments\n" ++ t)
            pure $ firstFailure [checkLinked (Right "8e24846684e27bb1") (mapResult M.lowProgram a), checkLinked (Right "95fee80f9e8b2927") (mapResult M.lowProgram b), inspect (mapResult M.lowProgram b) environmentEffects]
       , TestCase "native link keeps unused invalid functions until validation" $ case Compile.lowerSourceUsing bootstrapLoader False False "fn unused() -> Int [{ }] [{ affirm false; }] { return 0; }; return 0;" of
            Error e -> pure (Just e)
            Ok p -> do
                merged <- nativeMerge [(ModuleId "unpruned" Nothing,p)]
                pure $ inspect merged $ \full -> firstFailure
                    [ testAssertTrue (Map.member "unused" (M.progFunctions full))
                    , testAssertErrorContains "Could not prove" (validateCompiled (oneMarkerEach full))
                    ]
       , TestCase "actual emitter Full entry rejects blank-line garbage and malformed quotes" $ case programData empty of
            Error e -> pure (Just e)
            Ok text -> do
                tool <- actualEmitterTool
                case tool of
                    Error e -> pure (Just e)
                    Ok executable -> do
                        let request = "pass link\nenvironments\n" ++ text
                        (status, out, errors) <- Native.runWithInputFull executable request
                        let control = firstFailure [testAssertEq status ExitSuccess, testAssertEq errors "", testAssertEq out text]
                        suffix <- actualEntryRefusal (request ++ "\nbogus 0\n") control
                        quotes <- actualEntryRefusal (replaceText "main \"\"" "main \"\"x" request) control
                        legacy <- mapM (\input -> do
                            (_, answer, diagnostic) <- Native.runWithInputFull executable input
                            pure (firstFailure [testAssertEq answer "1\n", testAssertEq diagnostic "the input is not the MIR as data\n"])) ["", "\n"]
                        pure (firstFailure (suffix : quotes : legacy))
       , TestCase "dependency main ghosts follow numeric block order despite wire permutation" $ do
            let dep = empty{M.progMain = (M.progMain empty){M.fnBlocks = Map.fromList
                    [(M.BlockId 2, M.BasicBlock [M.Ghost Map.empty (M.GhostPosition 2 1)] M.Return)
                    ,(M.BlockId 10, M.BasicBlock [M.Ghost Map.empty (M.GhostValidation (S.ProofAssert (S.CTerm (S.VBool True))))] M.Return)]}}
                expectedGhosts = [ M.Ghost Map.empty (M.GhostPosition 2 1)
                                 , M.Ghost Map.empty (M.GhostValidation (S.ProofAssert (S.CTerm (S.VBool True))))
                                 ]
            case (programData dep, programData empty, programData (withMain empty expectedGhosts M.Return)) of
                (Ok input, Ok root, Ok expected) -> do
                    let altered = unlines (reverseFirstBlocks (lines input))
                        one (ModuleId pkg modu) text = "unit " ++ quote pkg ++ " " ++ maybe "none" (\n -> "some " ++ quote n) modu ++ " " ++ show (length (lines text)) ++ "\n" ++ text
                        request = "pass link\nmerge 2\n" ++ one unitA altered ++ one unitB root
                    tool <- nativeLinkTool
                    case tool of
                        Error e -> pure (Just e)
                        Ok executable -> do
                            (status, out, errors) <- Native.runWithInputFull executable request
                            pure (firstFailure
                                [ inspect (readLowered altered) (\back -> testAssertEq (M.lowProgram back) dep)
                                , testAssertEq status ExitSuccess
                                , testAssertEq errors ""
                                , testAssertEq out expected
                                ])
                (Error e, _, _) -> pure (Just e)
                (_, Error e, _) -> pure (Just e)
                (_, _, Error e) -> pure (Just e)
       , TestCase "native block record order is semantic" $ do
            let f = (function "f" 1){M.fnBlocks = Map.fromList [(M.BlockId 0, M.BasicBlock [] (M.Goto (M.BlockId 1))), (M.BlockId 1, M.BasicBlock [M.Assign (M.Local 0) (M.Use (M.Const (M.CInt 1)))] M.Return)]}
                p = empty{M.progFunctions = Map.singleton "f" f}
            case programData p of
                Error e -> pure (Just e)
                Ok input -> do
                    let altered = unlines (reverseFirstBlocks (lines input))
                        one t = "unit \"app\" some \"a\" " ++ show (length (lines t)) ++ "\n" ++ t
                    result <- nativeFull ("pass link\nmerge 2\n" ++ one input ++ one altered)
                    pure (sameResult (linked [(unitA,p)]) (mapResult M.lowProgram result))
       ])

runReference :: String -> Result Outcome String
runReference input = linkProbeProgram `bindResult` runProgramEnv RunEnv{envArgs = [], envInput = input, envFile = const Nothing}

responseProgram :: String -> Result M.Program String
responseProgram input = runReference input `bindResult` \out ->
    if outValue out == Just (MInt 1)
        then Error (reverse (dropWhile (== '\n') (reverse (decodeUtf8 (outStderr out)))))
        else mapResult M.lowProgram (readLowered (outStdout out))

roundTrip :: M.Lowered -> TestResult
roundTrip raw = inspect (writeLowered raw) $ \input -> inspect (runReference input) $ \out ->
    inspect (readLowered (outStdout out)) $ \back -> firstFailure
        [ if raw == back && show raw == show back then Nothing else Just "the full unit or its builtin metadata changed"
        , testAssertEq (writeLowered back) (Ok input)
        , testAssertEq (outValue out) Nothing
        ]

mergeInput :: [(ModuleId, M.Program)] -> Result String String
mergeInput units = flatResultMap one units `bindResult` \texts -> Ok ("pass link\nmerge " ++ show (length units) ++ "\n" ++ concat texts)
  where
    one (ModuleId pkg modu, program) = programData program `bindResult` \text -> Ok
        ("unit " ++ quote pkg ++ " " ++ maybe "none" (\n -> "some " ++ quote n) modu ++ " " ++ show (length (lines text)) ++ "\n" ++ text)

linked :: [(ModuleId, M.Program)] -> Result M.Program String
linked units = mergeInput units `bindResult` responseProgram `bindResult` copiesForUnits units

copiesForUnits :: [(ModuleId, M.Program)] -> M.Program -> Result M.Program String
copiesForUnits units program =
    case makeCopiesWith library (M.completeInstances program) of
        Error e -> Error ("Validation failed: " ++ e)
        ok -> ok
  where
    library = Set.fromList [name | (ModuleId "tersuslib" _, unit) <- units, name <- Map.keys (M.progBounded unit)]

libraryBoundedRetention :: IO TestResult
libraryBoundedRetention = do
    actual <- evaluate (ProductionLink.linkPrograms units)
    reference <- evaluate (linked units)
    native <- nativeMerge units
    let check p = firstFailure
            [ testAssertTrue (Map.member "libraryUsed" (M.progFunctions p))
            , testAssertTrue (Map.member genericKey (M.specEnv (M.fnSpec (M.progFunctions p Map.! "libraryUsed"))))
            , testAssertTrue (Map.member "libraryUsed[Int]" (M.progFunctions p))
            , testAssertTrue (Map.member coveredKey (M.specEnv (M.fnSpec (M.progFunctions p Map.! "libraryUsed[Int]"))))
            , testAssertTrue (Map.notMember "libraryUnused" (M.progFunctions p))
            , testAssertTrue (Map.null (M.progBounded p))
            ]
    pure (firstFailure ([inspect result check | result <- [reference, native, actual]]
        ++ [sameResult actual result | result <- [reference, native]]))
  where
    templates = ["libraryUsed", "libraryUnused"]
    library = empty
        { M.progFunctions = Map.fromList [(name, (function name 1){M.fnTypeParams = ["T"]}) | name <- templates]
        , M.progBounded = Map.fromList [(name, M.BoundedFn [] [] [] []) | name <- templates]
        }
    root = empty
        { M.progInstances = Map.singleton "libraryUsed[Int]" ("libraryUsed", [ArgType TInt])
        , M.progMain = (M.progMain empty){M.fnLocals = Map.singleton (M.Local 0) (M.LocalDecl TInt Nothing), M.fnBlocks = Map.fromList
            [ (M.BlockId 0, M.BasicBlock [] (M.Call (M.Const (M.CFn "libraryUsed[Int]")) [] (M.Local 0) (M.BlockId 1)))
            , (M.BlockId 1, M.BasicBlock [] M.Return)
            ]}
        }
    units = [(privateId, library), (unitB, root)]

singlePass :: String -> M.Program -> Result M.Program String
singlePass pass program = programData program `bindResult` \text -> responseProgram ("pass link\n" ++ pass ++ "\n" ++ text)

checkLinked :: Either String String -> Result M.Program String -> TestResult
checkLinked expected result = case result of
    Error e -> testAssertEq (Left e) expected
    Ok p -> inspect (programData p) $ \text -> testAssertEq (Right (fingerprint [text])) expected

sameResult :: Result M.Program String -> Result M.Program String -> TestResult
sameResult (Error expected) (Error actual) = testAssertEq actual expected
sameResult (Ok expected) (Ok actual)
    | expected == actual && show expected == show actual = Nothing
    | otherwise = Just ("program changed: functions " ++ show (Map.keys (M.progFunctions actual)) ++ "; expected " ++ show (Map.keys (M.progFunctions expected)))
sameResult a b = Just ("acceptance/refusal changed: " ++ resultKind a ++ " versus " ++ resultKind b)
  where
    resultKind (Error e) = e
    resultKind (Ok _) = "accepted"

inspect :: Result a String -> (a -> TestResult) -> TestResult
inspect (Error e) _ = Just e
inspect (Ok a) f = f a

firstFailure :: [TestResult] -> TestResult
firstFailure [] = Nothing
firstFailure (Just e : _) = Just e
firstFailure (Nothing : rest) = firstFailure rest

empty :: M.Program
empty = M.Program Map.empty Map.empty (function "" 0){M.fnReturns = Nothing, M.fnLocals = Map.empty, M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)} Map.empty Map.empty Map.empty Map.empty

function :: String -> Integer -> M.Function
function n value = M.Function n [] (Just TInt) (Map.singleton (M.Local 0) (M.LocalDecl TInt Nothing))
    (Map.singleton (M.BlockId 0) (M.BasicBlock [M.Assign (M.Local 0) (M.Use (M.Const (M.CInt value)))] M.Return)) [] [] [] [] [] M.emptySpec

program :: [(String, Integer)] -> M.Program
program defs = empty{M.progFunctions = Map.fromList [(n, function n value) | (n, value) <- defs]}

withMain :: M.Program -> [M.Statement] -> M.Terminator -> M.Program
withMain p statements term = p{M.progMain = (M.progMain p){M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock statements term)}}

unitA, unitB, privateId :: ModuleId
unitA = ModuleId "app" (Just "a")
unitB = ModuleId "app" (Just "b")
privateId = ModuleId "tersuslib" (Just "lists")

-- Capture canonical MIR3 fingerprints and exact refusals from the retired Haskell linker.
linkCases :: [(String, [(ModuleId, M.Program)], Either String String)]
linkCases =
    [ ("no units", [], Left "link error: no modules to link")
    , ("one unit", [(unitA, program [("f", 1)])], Right "5e42f1d6367192be")
    , ("identical unit identity", [(unitA, program [("f", 1)]), (unitA, program [("f", 1)])], Right "5e42f1d6367192be")
    , ("unit identity mismatch", [(unitA, program [("f", 1)]), (unitA, program [("g", 1)])], Left "link error: module app::a has inconsistent units")
    , ("identical definition from distinct units", [(unitA, program [("f", 1)]), (unitB, program [("f", 1)])], Right "5e42f1d6367192be")
    , ("function collision", [(unitA, program [("f", 1)]), (unitB, program [("f", 2)])], Left "link error: function f is defined by both module app::a and module app::b with different definitions")
    , ("private helper provenance", [(privateId, program [("listNew", 1)]), (unitB, program [("listNew", 1)])], Left "link error: function listNew is defined by both module tersuslib::lists and module app::b with different definitions")
    , ("extern namespace and signature dedup", [(unitA, program [("extern app$a$puts", 1)]), (unitB, program [("extern app$b$puts", 2)])], Right "2961379df8c693a8")
    , ("extern contract collision", [(unitA, externContract True), (unitB, externContract False)], Left "link error: function extern fn puts is defined by both module app::a and module app::b with different definitions")
    , ("extern intra-unit last definition wins", [(unitA, program [("extern a$puts", 1), ("extern z$puts", 2)]), (unitA, program [("extern puts", 2)])], Right "987f9739027eeee1")
    , ("extern normalization follows nested constants and environments", [(unitA, externReferences)], Right "b598ef9dd40ac0a8")
    , ("types collide before functions", [(unitA, withType TInt (program [("f", 1)])), (unitB, withType TBool (program [("f", 2)]))], Left "link error: type T is defined by both module app::a and module app::b with different definitions")
    , ("identical generic declarations", [(unitA, withGeneric "n"), (unitB, withGeneric "n")], Right "76d20307c0c3a987")
    , ("generic declaration collision", [(unitA, withGeneric "n"), (unitB, withGeneric "m")], Left "link error: generic struct T is defined by both module app::a and module app::b with different definitions")
    , ("invariant collision", [(unitA, withInvariant True), (unitB, withInvariant False)], Left "link error: invariant T is defined by both module app::a and module app::b with different definitions")
    , ("bounded declaration collision", [(unitA, withBounded "n"), (unitB, withBounded "m")], Left "link error: function with bounds f is defined by both module app::a and module app::b with different definitions")
    , ("instance collision", [(unitA, withInstance TInt), (unitB, withInstance TBool)], Left "link error: copy copy is defined by both module app::a and module app::b with different definitions")
    , ("dependency ghosts precede root ghosts", [(unitA, ghostUnit 1), (unitB, ghostUnit 2)], Right "54d549d3234d2758")
    , ("identical ghost expression control flow from distinct units", [(unitA, ghostFunction blockExpression), (unitB, ghostFunction blockExpression)], Right "589a5b596d320815")
    , ("conditional ghost expression branch collision", [(unitA, ghostFunction (S.IfExpr (S.Var "c") (S.Var "a") (S.Var "b"))), (unitB, ghostFunction (S.IfExpr (S.Var "c") (S.Var "a") (S.Var "other")))], Left "link error: function f is defined by both module app::a and module app::b with different definitions")
    , ("block ghost expression statement collision", [(unitA, ghostFunction blockExpression), (unitB, ghostFunction (S.BlockExpr [] (S.Var "blockResultRef")))], Left "link error: function f is defined by both module app::a and module app::b with different definitions")
    , ("ascription type child collision", [(unitA, ghostFunction (S.Ascribed (S.Var "x") TInt)), (unitB, ghostFunction (S.Ascribed (S.Var "x") TBool))], Left "link error: function f is defined by both module app::a and module app::b with different definitions")
    , ("identical ascriptions of a recursive type", [(unitA, ghostFunction (S.Ascribed (S.Var "x") (TBox (TList TInt)))), (unitB, ghostFunction (S.Ascribed (S.Var "x") (TBox (TList TInt))))], Right "c257d40edabc1cbe")
    , ("root spec and loop environments remain untouched", [(unitA, program [("extra", 1)]), (unitB, environments)], Right "659454d16d459ffb")
    , ("the complete full metadata fixture", [(unitA, M.lowProgram everyRecord)], Right "85792b8f6a7902a6")
    ]
  where
    withType ty p = p{M.progTypes = Map.singleton "T" (M.StructDecl [("x", ty)])}
    withGeneric n = empty{M.progGenerics = Map.singleton "T" ([n], [("x", TArrayOf TInt (SizeParam n))])}
    withInvariant b = empty{M.progInvariants = Map.singleton "T" [S.ProofAssert (S.CTerm (S.VBool b))]}
    withBounded n = empty{M.progBounded = Map.singleton "f" (M.BoundedFn [n] [] [] [])}
    withInstance ty = empty{M.progInstances = Map.singleton "copy" ("f", [ArgType ty])}
    externContract b = (program [("extern package$puts", 1)]){M.progFunctions = Map.singleton "extern package$puts" (function "extern package$puts" 1){M.fnSpec = M.emptySpec{M.specRequires = [S.ProofAssert (S.CTerm (S.VBool b))]}}}
    ghostUnit n = withMain empty [M.Ghost Map.empty (M.GhostPosition n 1), M.Ghost Map.empty (M.GhostValidation (S.ProofAssert (S.CTerm (S.VInt (toInteger n)))))] M.Return

externReferences :: M.Program
externReferences = withMain (program [("extern p$x$puts", 1)])
    [ M.Assign (M.Local 0) (M.Use (M.Const (M.CList [M.CData "Holder" [("fn", M.CFn "extern p$x$puts")]])))
    , M.Ghost (Map.singleton "alias" (M.Const (M.CFn "extern p$x$puts"))) (M.GhostFunction "extern p$x$puts" "puts" True)
    ] M.Return

environmentEffects :: M.Program -> TestResult
environmentEffects p = firstFailure
    [ testAssertTrue (p /= environments)
    , testAssertEq (M.fnSpec (M.progMain p)) (M.fnSpec (M.progMain environments))
    , testAssertTrue (all (Map.member "missing") (M.specEnv (M.fnSpec f) : map M.loopEnv (Map.elems (M.specLoops (M.fnSpec f))) ++ ghostEnvs f ++ ghostEnvs (M.progMain p)))
    , testAssertEq (Map.lookup "f" (head (ghostEnvs (M.progMain p)))) (Just (M.Copy (M.Local 0)))
    ]
  where
    f = M.progFunctions p Map.! "f"
    ghostEnvs fun = [env | block <- Map.elems (M.fnBlocks fun), M.Ghost env _ <- M.blockStatements block]

environments :: M.Program
environments = (withMain (program [("f", 1), ("missing", 2)]) [M.Ghost local (M.GhostFunction "f" "f" True)] M.Return)
    { M.progMain = root{M.fnSpec = M.emptySpec{M.specEnv = local, M.specLoops = Map.singleton (M.BlockId 0) (M.LoopSpec [] Nothing local (M.BlockId 0))}}
    , M.progFunctions = Map.fromList
        [ ("f", (function "f" 1){M.fnSpec = M.emptySpec{M.specEnv = Map.empty, M.specLoops = Map.singleton (M.BlockId 0) (M.LoopSpec [] Nothing sparse (M.BlockId 0))}, M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [M.Ghost Map.empty (M.GhostValidation (S.ProofAssert (S.CTerm (S.VBool True)))), M.Assign (M.Local 0) (M.Use (M.Const (M.CInt 1)))] M.Return)})
        , ("missing", function "missing" 2)
        ]
    }
  where
    local = Map.fromList [("f", M.Copy (M.Local 0)), ("alias", M.Const (M.CFn "f"))]
    sparse = Map.singleton "local" (M.Copy (M.Local 0))
    root = M.progMain (withMain empty [M.Ghost local (M.GhostFunction "f" "f" True)] M.Return)

reachable :: M.Program
reachable = withMain base
    [ M.Ghost (Map.singleton "envOnly" (M.Const (M.CFn "dead"))) (M.GhostFunction "dead" "dead" True)
    , M.Ghost Map.empty (M.GhostValidation (S.AssignProofVar "x" (S.Var "ghostRef")))
    , M.Assign (M.Local 0) (M.Use (M.Const (M.CArray [M.CFn "runtimeRef"])))
    ] M.Return
  where
    base = (program [("dead", 0), ("ghostRef", 1), ("runtimeRef", 2), ("contractRef", 3), ("invariantRef", 4), ("<Child as Drop>::drop", 5)])
        { M.progMain = (M.progMain empty){M.fnLocals = Map.singleton (M.Local 0) (M.LocalDecl (TNamed "Parent" []) Nothing), M.fnSpec = M.emptySpec{M.specRequires = [S.ProofAssert (S.ATerm "contractRef")]}}
        , M.progTypes = Map.fromList [("Parent", M.StructDecl [("child", TNamed "Child" [])]), ("Child", M.StructDecl [("x", TInt)]), ("DeadType", M.StructDecl [])]
        , M.progInvariants = Map.fromList [("Child", [S.ProofAssert (S.ATerm "invariantRef")]), ("DeadType", [])]
        , M.progGenerics = Map.singleton "UnusedGeneric" (["n"], [("x", TArrayOf TInt (SizeParam "n"))])
        }

ghostExpressionNames :: [String]
ghostExpressionNames =
    [ "condRef", "thenRef", "elseRef"
    , "blockCallRef", "blockProofRef", "blockIfRef", "blockReturnRef", "blockElseRef", "blockResultRef"
    , "ascribedRef"
    ]

blockExpression :: S.Expression
blockExpression = S.BlockExpr
    [ S.Let "t" (S.F (S.Var "blockCallRef") [S.Val (S.VInt 1)])
    , S.ValidationStatement (S.ProofAssert (S.ATerm "blockProofRef"))
    , S.If (S.Var "blockIfRef") [S.Return (S.Var "blockReturnRef")] [S.Block [S.Assign "t" (S.Var "blockElseRef")]]
    ] (S.Var "blockResultRef")

expressionForms :: M.Program
expressionForms = withMain base
    [ M.Ghost Map.empty (M.GhostValidation (S.AssignProofVar "a" (S.IfExpr (S.Var "condRef") (S.Var "thenRef") (S.Var "elseRef"))))
    , M.Ghost Map.empty (M.GhostValidation (S.AssignProofVar "b" blockExpression))
    , M.Ghost Map.empty (M.GhostValidation (S.AssignProofVar "c" (S.Ascribed (S.Var "ascribedRef") (TNamed "Carrier" []))))
    ] M.Return
  where
    base = (program [(n, 1) | n <- "deadRef" : ghostExpressionNames]){M.progTypes = Map.singleton "Carrier" (M.StructDecl [("x", TInt)])}

expressionFormEffects :: M.Program -> TestResult
expressionFormEffects p = firstFailure
    ([testAssertTrue (not (Map.member "deadRef" (M.progFunctions p)))]
        ++ [maybe (Just ("pruning dropped " ++ n)) (const Nothing) (Map.lookup n (M.progFunctions p)) | n <- ghostExpressionNames])

ghostFunction :: S.Expression -> M.Program
ghostFunction expr = empty{M.progFunctions = Map.singleton "f" (function "f" 1)
    {M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock
        [ M.Ghost Map.empty (M.GhostValidation (S.AssignProofVar "p" expr))
        , M.Assign (M.Local 0) (M.Use (M.Const (M.CInt 1)))
        ] M.Return)}}

mixedAssumes :: M.Lowered
mixedAssumes = (asUnit (program [("f", 1)]))
    {M.lowAssumes =
        [ Left (S.CTerm (S.VBool True))
        , Right (S.Var "f")
        , Left (S.ATerm "f")
        , Right (S.Ascribed (S.F (S.Var "f") [S.Val (S.VInt 1)]) TInt)
        , Right (S.IfExpr (S.Var "f") (S.Val (S.VFnRef "f")) blockExpression)
        ]}

malformed :: (String, String, [String] -> [String]) -> TestResult
malformed (_, _, change) = inspect (writeLowered everyRecord) $ \good -> firstFailure
    [ roundTrip everyRecord
    , case readLowered (unlines (change (lines good))) of
        Ok _ -> Just "the malformed differential control is accepted by Haskell"
        Error _ -> inspect (runReference (unlines (change (lines good)))) $ \out -> testAssertEq (outValue out) (Just (MInt 1))
    ]

canonicalRaw :: String -> TestResult
canonicalRaw input = inspect (readLowered input) $ \expected -> inspect (runReference input) $ \out ->
    inspect (readLowered (outStdout out)) $ \actual -> firstFailure
        [ if expected == actual && show expected == show actual then Nothing else Just "the decoded full unit changed"
        , testAssertEq (mapResult (== outStdout out) (writeLowered expected)) (Ok True)
        ]

refuseRaw :: String -> String -> TestResult
refuseRaw control bad = firstFailure
    [ canonicalRaw control
    , case readLowered bad of
        Ok _ -> Just "the invalid wire mutation is accepted by Haskell"
        Error _ -> inspect (runReference bad) $ \out -> testAssertEq (outValue out) (Just (MInt 1))
    ]

replaceFirst :: (String -> Bool) -> (String -> String) -> [String] -> [String]
replaceFirst _ _ [] = []
replaceFirst match edit (line : rest)
    | match line = edit line : rest
    | otherwise = line : replaceFirst match edit rest

wireMutation :: M.Lowered -> ([String] -> [String]) -> TestResult
wireMutation raw change = inspect (writeLowered raw) $ \control -> refuseRaw control (unlines (change (lines control)))

largeMaps :: Int -> M.Program
largeMaps shift = withMain base mainGhosts M.Return
  where
    names = ["f" ++ show i | i <- [0 .. 47 :: Int]]
    globals = Map.fromList [(n, M.Const (M.CFn n)) | n <- names]
    env i = Map.insert "local" (M.Copy (M.Local 0)) (Map.restrictKeys globals (Set.fromList (take (1 + (i + shift) `mod` length names) names)))
    one i n = (function n 1){M.fnSpec = M.emptySpec{M.specEnv = env i}, M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock
        ([M.Ghost (env i) (M.GhostPosition i column) | column <- [1 .. 5]] ++ [M.Assign (M.Local 0) (M.Use (M.Const (M.CInt 1)))]) M.Return)}
    base = empty{M.progFunctions = Map.fromList [(n, one i n) | (i, n) <- zip [0 ..] names]}
    mainGhosts = [M.Ghost (env i) (M.GhostFunction n n True) | (i, n) <- zip [0 ..] names]

reverseShared :: [String] -> [String]
reverseShared rows = before ++ reverse shared ++ map change after
  where
    (before, middle) = break (isPrefixOf "shared ") rows
    (shared, after) = span (isPrefixOf "shared ") middle
    count = length shared
    change line = let ts = words line; slot = case ts of
                        "env" : _ -> Just 1
                        "loop" : _ -> Just 9
                        "ghost" : _ -> Just 2
                        _ -> Nothing
                   in case slot of
                        Just p | length ts > p && ts !! p /= "none" -> unwords (take p ts ++ show (count - 1 - read (ts !! p)) : drop (p + 1) ts)
                        _ -> line

rawMerge :: String -> String -> Result M.Program String
rawMerge a b = responseProgram ("pass link\nmerge 2\n" ++ one a ++ one b) `bindResult` \p ->
    case makeCopies (M.completeInstances p) of Error e -> Error ("Validation failed: " ++ e); ok -> ok
  where
    one text = "unit \"app\" some \"a\" " ++ show (length (lines text)) ++ "\n" ++ text

sharedAllocationControl :: TestResult
sharedAllocationControl = inspect (writeLowered (asUnit (largeMaps 0))) $ \input ->
    let changed = unlines (reverseShared (lines input))
     in inspect (readLowered changed) $ \raw -> firstFailure
        [ testAssertTrue (input /= changed)
        , sameResult (Ok (largeMaps 0)) (Ok (M.lowProgram raw))
        , sameResult (linked [(unitA, largeMaps 0)]) (rawMerge input changed)
        , canonicalRaw changed
        ]

sentinelMutation :: Bool -> Bool -> TestResult
sentinelMutation invariant body = inspect (writeLowered everyRecord) $ \input ->
    let (records, footer) = break (isPrefixOf "data ") (lines input)
     in inspect (readMirPayloadBytes (map B.pack (drop 1 footer))) $ \payloads ->
        let holds = S.ValidationStatement (S.ProofAssert (S.CTerm (S.VBool True)))
            changed = map (\s -> case s of
                S.While condition [] term [] -> S.While condition (if invariant then [S.ProofAssert (S.CTerm (S.VBool True))] else []) term (if body then [holds] else [])
                _ -> s) payloads
         in inspect (writeMirPayloadLines changed) $ \dataLines ->
            refuseRaw input (unlines (records ++ ["data " ++ show (length dataLines)] ++ dataLines))

bigUnit :: Integer -> M.Lowered
bigUnit n = asUnit (program [("big", n)]){M.progMain = (M.progMain empty){M.fnSpec = M.emptySpec{M.specRequires = [S.ProofAssert (S.CTerm (S.VInt n))]}}}

bigSizeUnit :: M.Lowered
bigSizeUnit = asUnit empty{M.progGenerics = Map.singleton "Packet" (["n"], [("value", TArrayOf TInt (SizeConst (2 ^ (80 :: Int))))]),
    M.progMain = (M.progMain empty){M.fnLocals = Map.singleton (M.Local 0) (M.LocalDecl (TArrayOf TInt (SizeConst (2 ^ (80 :: Int)))) Nothing)}}

reverseFirstBlocks :: [String] -> [String]
reverseFirstBlocks rows = before ++ concat (reverse (chunks body)) ++ after
  where
    (before, fromBlock) = break (isPrefixOf "block ") rows
    (body, after) = break (== "end") fromBlock
    chunks [] = []
    chunks (header : rest) = let (statements, next) = break (isPrefixOf "block ") rest in (header : statements) : chunks next

blockOrderControl :: TestResult
blockOrderControl = rawSemanticControl p reverseFirstBlocks
  where
    f = (function "f" 1){M.fnBlocks = Map.fromList [(M.BlockId 0, M.BasicBlock [] (M.Goto (M.BlockId 1))), (M.BlockId 1, M.BasicBlock [M.Assign (M.Local 0) (M.Use (M.Const (M.CInt 1)))] M.Return)]}
    p = empty{M.progFunctions = Map.singleton "f" f}

replaceText :: String -> String -> String -> String
replaceText old new text
    | null text = []
    | old `isPrefixOf` text = new ++ replaceText old new (drop (length old) text)
    | otherwise = head text : replaceText old new (tail text)

valueProgram :: S.Value -> M.Program
valueProgram value = empty{M.progInvariants = Map.singleton "T" [S.ProofAssert (S.CTerm value)]}

rawSemanticControl :: M.Program -> ([String] -> [String]) -> TestResult
rawSemanticControl p change = inspect (programData p) $ \input ->
    let altered = unlines (change (lines input))
     in inspect (readLowered altered) $ \decoded -> firstFailure
        [ testAssertTrue (input /= altered)
        , testAssertEq (M.lowProgram decoded) p
        , sameResult (linked [(unitA, p)]) (rawMerge input altered)
        ]

builtinMetadataControl :: TestResult
builtinMetadataControl = firstFailure
    [ testAssertTrue (left == right && show left /= show right)
    , roundTrip (asUnit (valueProgram left))
    , roundTrip (asUnit (valueProgram right))
    , sameResult (linked [(unitA, valueProgram left)]) (linked [(unitA, valueProgram left), (unitA, valueProgram right)])
    , checkLinked (Left "link error: module app::a has inconsistent units") (linked [(unitA, valueProgram left), (unitA, valueProgram changed)])
    ]
  where
    left = S.VFunct ["a"] [S.ProofAssert (S.CTerm (S.VBool True))] [] (S.BuiltinFunct Plus) []
    right = S.VFunct ["b"] [] [S.Assume (S.CTerm (S.VBool False))] (S.BuiltinFunct Plus) [S.CTerm (S.VInt (2 ^ (80 :: Int)))]
    changed = S.VFunct [] [] [] (S.BuiltinFunct Minus) []

testLink :: Test
testLink = TestList "testLink"
    [ testCase "full MIR3/link source compiles" $ inspect linkProbeProgram (const Nothing)
    , testCase "empty full unit round trip" (roundTrip (asUnit empty))
    , testCase "every full record and builtin metadata round trip" (roundTrip everyRecord)
    , TestList "frozen link results" [testCase label (checkLinked expected (linked units)) | (label, units, expected) <- linkCases]
    , testCase "exact reachability including ghost/contract/invariant/impl references" (checkLinked (Right "8e24846684e27bb1") (singlePass "prune" reachable))
    , testCase "ghost conditional, block and ascribed expressions keep their nested references" $ firstFailure
        [ checkLinked (Right "7f3e3b756a3fbc3c") (singlePass "prune" expressionForms)
        , inspect (singlePass "prune" expressionForms) expressionFormEffects
        ]
    , testCase "mixed assume and Block::assume return payloads round trip" (roundTrip mixedAssumes)
    , testCase "generic metadata survives pruning" (inspect (singlePass "prune" reachable) $ \p -> testAssertEq (M.progGenerics p) (M.progGenerics reachable))
    , testCase "environment completion is exact and idempotent" $ firstFailure
        [ checkLinked (Right "95fee80f9e8b2927") (singlePass "environments" environments)
        , inspect (singlePass "environments" environments) environmentEffects
        , inspect (singlePass "environments" environments) $ \p -> sameResult (Ok p) (singlePass "environments" p)
        ]
    , testCase "different bodies are a meaningful comparison mutation" $ testAssertTrue (linked [(unitA, program [("f", 1)])] /= linked [(unitA, program [("f", 2)])])
    , testCase "block record order follows map semantics" blockOrderControl
    , testCase "arbitrary positive and negative runtime/proof integers" $ firstFailure [roundTrip (bigUnit n) | n <- [2 ^ (80 :: Int), 0 - 2 ^ (80 :: Int), 9223372036854775808, 0 - 9223372036854775809]]
    , testCase "arbitrary runtime size constants" (roundTrip bigSizeUnit)
    , testCase "many distinct repeated shared maps stay exact" (roundTrip (asUnit (largeMaps 0)))
    , testCase "cross-unit global completion of distinct shared maps" (checkLinked (Right "7924ccdbef893207") (linked [(unitA, largeMaps 0), (unitB, largeMaps 11)]))
    , testCase "different shared ID allocations have the same meaning" sharedAllocationControl
    , testCase "shared nonfunction bindings become canonical own bindings" $ inspect (writeLowered everyRecord) $ \text -> canonicalRaw (unlines (replaceFirst (isPrefixOf "shared ") (const "shared 1 \"f\" copy 0") (lines text)))
    , testCase "termination invariant sentinel mutation refuses" (sentinelMutation True False)
    , testCase "termination body sentinel mutation refuses" (sentinelMutation False True)
    , testCase "numeric local spelling duplicate refuses" (wireMutation everyRecord (replaceFirst (isPrefixOf "local 0 ") (\line -> line ++ "\nlocal 00 none bool")))
    , testCase "numeric loop spelling duplicate refuses" (wireMutation everyRecord (replaceFirst (isPrefixOf "loop 1 ") (\line -> line ++ "\nloop 01 " ++ drop 7 line)))
    , testCase "signed local overflow refuses without wrapping" (wireMutation everyRecord (replaceFirst (isPrefixOf "local 0 ") (const "local 9223372036854775808 none int")))
    , testCase "AST signed numbers do not widen" (wireMutation everyRecord (replaceFirst (== "VBool true") (const "Mark 9223372036854775808 0")))
    , testCase "integer payload spelling has semantic equality" (rawSemanticControl (valueProgram (S.VInt 1)) (replaceFirst (isPrefixOf "NamePart \"1\" ") (replaceText "\"1\"" "\"01\"")))
    , testCase "recursive List/Box aliases have semantic equality" (rawSemanticControl (valueProgram (S.VFunct [] [] [] (S.BuiltinFunct (Ctor "Holder" [ArgType (TBox (TList (TList TInt)))] ["value"])) [])) (map (\line -> if "Type " `isPrefixOf` line then replaceText "named \"List\" 1 type " "list " (replaceText "named \"Box\" 1 type " "box " line) else line)))
    , testCase "builtin metadata is retained while builtin equality ignores it" builtinMetadataControl
    , testCase "unknown binary operation refuses" (wireMutation (asUnit (program [("f", 1)])) (replaceFirst (isPrefixOf "assign 0 ") (const "assign 0 binary bogus const int 1 const int 2")))
    , testCase "truncated conditional expression payload refuses" (wireMutation (asUnit (ghostFunction (S.IfExpr (S.Var "f") (S.Var "f") (S.Var "f")))) (replaceFirst (isPrefixOf "IfExpr ") (const "IfExpr 0 1")))
    , testCase "an ascription whose child is not a type refuses" (wireMutation (asUnit (ghostFunction (S.Ascribed (S.Var "f") TInt))) (replaceFirst (isPrefixOf "Ascribed ") (\line -> unwords (take 2 (words line) ++ [head (drop 1 (words line))]))))
    , testCase "a block expression result that is not an expression refuses" (wireMutation (asUnit (ghostFunction blockExpression)) (replaceFirst (isPrefixOf "BlockExpr ") (\line -> unwords (take 2 (words line) ++ [head (drop 1 (words line))]))))
    , testCase "quoted binary operation refuses" (wireMutation (asUnit (program [("f", 1)])) (replaceFirst (isPrefixOf "assign 0 ") (const "assign 0 binary \"add\" const int 1 const int 2")))
    , testCase "unknown list operation refuses" (wireMutation (asUnit (program [("f", 1)])) (replaceFirst (isPrefixOf "assign 0 ") (const "assign 0 listop bogus 0")))
    , testCase "quoted list operation refuses" (wireMutation (asUnit (program [("f", 1)])) (replaceFirst (isPrefixOf "assign 0 ") (const "assign 0 listop \"length\" 0")))
    , TestList "full codec refusal corpus" [testCase label (malformed item) | item@(label, _, _) <- malformedLowered]
    ]
