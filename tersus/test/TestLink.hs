{-# LANGUAGE PatternSynonyms #-}
module TestLink (testLink, testLinkNative, linkProbeProgram, probeSource) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import System.IO.Unsafe (unsafePerformIO)
import qualified Native
import qualified MirHousekeeping as Housekeeping
import Seed (cachedSeed, seedHash)
import System.Exit (ExitCode(..))

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.ByteString.Char8 as B
import AstData (readMirPayloadBytes, writeMirPayloadLines)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import DataCodec (quote)
import qualified Mir as M
import MirCopies (makeCopies)
import MirData (readLowered, writeLowered)
import qualified MirData
import MirEval (RunEnv (..), Outcome (..), MirValue (..), runProgramEnv)
import MirPass (programData)
import ElaboratorTool (bootstrapLoader)
import LibPackage (libPackage)
import PackageCompile (compileModulesUsing, lowerCompiledPackage)
import PackageData (ModuleId (..), Snapshot (..), resolverFromFiles)
import PreludeSource (toolPackageFiles)
import qualified LinkOracle as Oracle
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
                        Native.cachedProgram "link-test" key "the Link differential tool" $ \output -> do
                            ir <- Native.runWithInput emitter input
                            case ir of Error e -> pure (Error e); Ok llvm -> Native.buildExecutable output llvm
        pure (Just result, result)

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
            Ok raw -> case makeCopies (M.completeInstances (M.lowProgram raw)) of
                Error e -> Error ("Validation failed: " ++ e)
                ok -> ok

testLinkNative :: Test
testLinkNative = TestList "testLinkNative"
    ([TestCase label $ sameResult (Oracle.linkPrograms units) <$> nativeMerge units | (label, units) <- linkCases]
    ++ [ TestCase "full payload native round trip" $ case writeLowered everyRecord of
            Error e -> pure (Just e)
            Ok input -> do result <- nativeFull input; pure $ inspect result $ \back -> testAssertTrue (everyRecord == back && show everyRecord == show back)
       , TestCase "large distinct shared maps native round trip" $ case writeLowered (asUnit (largeMaps 0)) of
            Error e -> pure (Just e)
            Ok input -> do result <- nativeFull input; pure $ inspect result $ \back -> testAssertEq (writeLowered back) (Ok input)
       , TestCase "native reachability/environment parity" $ do
            a <- case programData reachable of Error e -> pure (Error e); Ok t -> nativeFull ("pass link\nprune\n" ++ t)
            b <- case programData environments of Error e -> pure (Error e); Ok t -> nativeFull ("pass link\nenvironments\n" ++ t)
            pure $ firstFailure [sameResult (Ok (Oracle.pruneProgram reachable)) (mapResult M.lowProgram a), sameResult (Ok (Oracle.completeSpecEnvs environments)) (mapResult M.lowProgram b)]
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
linked units = mergeInput units `bindResult` responseProgram `bindResult` \program ->
    case makeCopies (M.completeInstances program) of
        Error e -> Error ("Validation failed: " ++ e)
        ok -> ok

singlePass :: String -> M.Program -> Result M.Program String
singlePass pass program = programData program `bindResult` \text -> responseProgram ("pass link\n" ++ pass ++ "\n" ++ text)

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

linkCases :: [(String, [(ModuleId, M.Program)])]
linkCases =
    [ ("no units", [])
    , ("one unit", [(unitA, program [("f", 1)])])
    , ("identical unit identity", [(unitA, program [("f", 1)]), (unitA, program [("f", 1)])])
    , ("unit identity mismatch", [(unitA, program [("f", 1)]), (unitA, program [("g", 1)])])
    , ("identical definition from distinct units", [(unitA, program [("f", 1)]), (unitB, program [("f", 1)])])
    , ("function collision", [(unitA, program [("f", 1)]), (unitB, program [("f", 2)])])
    , ("private helper provenance", [(privateId, program [("listNew", 1)]), (unitB, program [("listNew", 1)])])
    , ("extern namespace and signature dedup", [(unitA, program [("extern app$a$puts", 1)]), (unitB, program [("extern app$b$puts", 2)])])
    , ("extern contract collision", [(unitA, externContract True), (unitB, externContract False)])
    , ("extern intra-unit last definition wins", [(unitA, program [("extern a$puts", 1), ("extern z$puts", 2)]), (unitA, program [("extern puts", 2)])])
    , ("extern normalization follows nested constants and environments", [(unitA, externReferences)])
    , ("types collide before functions", [(unitA, withType TInt (program [("f", 1)])), (unitB, withType TBool (program [("f", 2)]))])
    , ("identical generic declarations", [(unitA, withGeneric "n"), (unitB, withGeneric "n")])
    , ("generic declaration collision", [(unitA, withGeneric "n"), (unitB, withGeneric "m")])
    , ("invariant collision", [(unitA, withInvariant True), (unitB, withInvariant False)])
    , ("bounded declaration collision", [(unitA, withBounded "n"), (unitB, withBounded "m")])
    , ("instance collision", [(unitA, withInstance TInt), (unitB, withInstance TBool)])
    , ("dependency ghosts precede root ghosts", [(unitA, ghostUnit 1), (unitB, ghostUnit 2)])
    , ("root spec and loop environments remain untouched", [(unitA, program [("extra", 1)]), (unitB, environments)])
    , ("the complete full metadata fixture", [(unitA, M.lowProgram everyRecord)])
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

environments :: M.Program
environments = (withMain (program [("f", 1), ("dead", 2)]) [M.Ghost local (M.GhostFunction "f" "f" True)] M.Return)
    { M.progMain = root{M.fnSpec = M.emptySpec{M.specEnv = local, M.specLoops = Map.singleton (M.BlockId 0) (M.LoopSpec [] Nothing local (M.BlockId 0))}}
    , M.progFunctions = Map.singleton "f" (function "f" 1){M.fnSpec = M.emptySpec{M.specEnv = local}}
    }
  where
    local = Map.fromList [("f", M.Copy (M.Local 0)), ("alias", M.Const (M.CFn "f"))]
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
        , testAssertEq (writeLowered actual) (writeLowered expected)
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
        , sameResult (Oracle.linkPrograms [(unitA, largeMaps 0), (unitA, M.lowProgram raw)]) (rawMerge input changed)
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
        , sameResult (Oracle.linkPrograms [(unitA, p), (unitA, M.lowProgram decoded)]) (rawMerge input altered)
        ]

builtinMetadataControl :: TestResult
builtinMetadataControl = firstFailure
    [ testAssertTrue (left == right && show left /= show right)
    , roundTrip (asUnit (valueProgram left))
    , roundTrip (asUnit (valueProgram right))
    , sameResult (Oracle.linkPrograms [(unitA, valueProgram left), (unitA, valueProgram right)]) (linked [(unitA, valueProgram left), (unitA, valueProgram right)])
    , testAssertTrue (linked [(unitA, valueProgram left), (unitA, valueProgram changed)] /= linked [(unitA, valueProgram left), (unitA, valueProgram right)])
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
    , TestList "exact Haskell link differential" [testCase label (sameResult (Oracle.linkPrograms units) (linked units)) | (label, units) <- linkCases]
    , testCase "exact reachability including ghost/contract/invariant/impl references" (sameResult (Ok (Oracle.pruneProgram reachable)) (singlePass "prune" reachable))
    , testCase "generic metadata survives pruning" (inspect (singlePass "prune" reachable) $ \p -> testAssertEq (M.progGenerics p) (M.progGenerics reachable))
    , testCase "environment completion is exact and idempotent" $ firstFailure
        [ sameResult (Ok (Oracle.completeSpecEnvs environments)) (singlePass "environments" environments)
        , inspect (singlePass "environments" environments) $ \p -> sameResult (Ok p) (singlePass "environments" p)
        ]
    , testCase "different bodies are a meaningful comparison mutation" $ testAssertTrue (linked [(unitA, program [("f", 1)])] /= linked [(unitA, program [("f", 2)])])
    , testCase "arbitrary positive and negative runtime/proof integers" $ firstFailure [roundTrip (bigUnit n) | n <- [2 ^ (80 :: Int), 0 - 2 ^ (80 :: Int), 9223372036854775808, 0 - 9223372036854775809]]
    , testCase "arbitrary runtime size constants" (roundTrip bigSizeUnit)
    , testCase "many distinct repeated shared maps stay exact" (roundTrip (asUnit (largeMaps 0)))
    , testCase "cross-unit global completion of distinct shared maps" (sameResult (Oracle.linkPrograms [(unitA, largeMaps 0), (unitB, largeMaps 11)]) (linked [(unitA, largeMaps 0), (unitB, largeMaps 11)]))
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
    , testCase "quoted binary operation refuses" (wireMutation (asUnit (program [("f", 1)])) (replaceFirst (isPrefixOf "assign 0 ") (const "assign 0 binary \"add\" const int 1 const int 2")))
    , testCase "unknown list operation refuses" (wireMutation (asUnit (program [("f", 1)])) (replaceFirst (isPrefixOf "assign 0 ") (const "assign 0 listop bogus 0")))
    , testCase "quoted list operation refuses" (wireMutation (asUnit (program [("f", 1)])) (replaceFirst (isPrefixOf "assign 0 ") (const "assign 0 listop \"length\" 0")))
    , TestList "full codec refusal corpus" [testCase label (malformed item) | item@(label, _, _) <- malformedLowered]
    ]
