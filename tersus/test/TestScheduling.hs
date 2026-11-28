module TestScheduling
    ( Arguments (..)
    , parseArguments
    , selectGroupNames
    , optInGroups
    , isOptIn
    , useWorkerProcesses
    , childCapabilities
    , assignShards
    , ciShardCount
    , runnerSpan
    , groupWeight
    , estimatedPeakMiB
    , memoryBudgetMiB
    , admitGroup
    , launchOrder
    , splitTestGroups
    , groupName
    , leafPaths
    , testScheduling
    ) where

import Control.Exception (evaluate)
import Data.Char (isDigit)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (foldl', isInfixOf, isPrefixOf, minimumBy, sort, sortBy)
import System.Environment (getEnvironment, getExecutablePath)
import System.Exit (ExitCode (..))
import System.Process (CreateProcess (..), proc)
import Native (availableProcessors, readProcessOutput)
import System.Timeout (timeout)
import Data.Ord (comparing)
import qualified Data.Map.Strict as Map
import TestHarness (Test (..), TestResult, batchItems, testAssertEq, testAssertTrue, testCase)
import TestParserBootstrap (testParserBootstrap, parserBootstrapGroups)
import TestPipeline (selfHostedFamilyManifest)

data Arguments = Arguments
    { argumentJobs :: Maybe Int
    , argumentGroups :: [String]
    , argumentChild :: Bool
    , argumentShard :: Maybe (Int, Int)
    }
    deriving (Eq, Show)

parseArguments :: [String] -> Either String Arguments
parseArguments = go (Arguments Nothing [] False Nothing)
  where
    go arguments []
        | argumentChild arguments && argumentShard arguments /= Nothing = Left "--child cannot be combined with --shard"
        | otherwise = Right arguments
    go arguments ("--child" : rest) = go arguments{argumentChild = True} rest
    go arguments ("-j" : number : rest) = withJobs arguments number rest
    go arguments ("--jobs" : number : rest) = withJobs arguments number rest
    go arguments ("--shard" : shard : rest) = withShard arguments shard rest
    go _ ["-j"] = Left "-j needs a number of jobs"
    go _ ["--jobs"] = Left "--jobs needs a number of jobs"
    go _ ["--shard"] = Left "--shard needs k/n (1 <= k <= n)"
    go arguments (argument : rest)
        | "--jobs=" `isPrefixOf` argument = withJobs arguments (drop (length "--jobs=") argument) rest
        | "--shard=" `isPrefixOf` argument = withShard arguments (drop (length "--shard=") argument) rest
        | "-j" `isPrefixOf` argument && length argument > 2 = withJobs arguments (drop 2 argument) rest
        | "-" `isPrefixOf` argument = Left ("unknown option: " ++ argument)
        | otherwise = go arguments{argumentGroups = argumentGroups arguments ++ [argument]} rest
    withJobs arguments number rest = case positiveInt number of
        Just jobs -> go arguments{argumentJobs = Just jobs} rest
        Nothing -> Left ("-j needs a number of jobs (at least 1), not " ++ show number)
    withShard arguments text rest
        | argumentShard arguments /= Nothing = Left "--shard may only be specified once"
        | otherwise = case break (== '/') text of
            (indexText, '/' : countText) -> case (positiveInt indexText, positiveInt countText) of
                (Just index, Just count) | index <= count -> go arguments{argumentShard = Just (index, count)} rest
                _ -> invalidShard
            _ -> invalidShard
      where
        invalidShard = Left ("--shard needs k/n (1 <= k <= n), not " ++ show text)

positiveInt :: String -> Maybe Int
positiveInt text
    | null text || not (all isDigit text) = Nothing
    | otherwise = case reads text :: [(Integer, String)] of
        [(number, "")] | number >= 1 && number <= toInteger (maxBound :: Int) -> Just (fromInteger number)
        _ -> Nothing

-- Groups that run only when they are named (with the groups registered for them), and never in a shard: too slow
-- for every run of the suite
optInGroups :: [String]
optInGroups = ["testHostValidation", "testElaborateMutant"]

isOptIn :: String -> Bool
isOptIn name = takeWhile (/= ':') name `elem` optInGroups

selectGroupNames :: Arguments -> [String] -> Either String [String]
selectGroupNames arguments names
    | not (null unknown) = Left ("unknown test groups: " ++ unwords unknown)
    | argumentShard arguments /= Nothing && any isOptIn expanded = Left "opt-in groups run only without --shard"
    | otherwise = Right [name | name <- names, requested name, inShard name]
  where
    chosen = argumentGroups arguments
    expansion name = [registered | registered <- names,
        registered == name || (name ++ ":") `isPrefixOf` registered]
    unknown = [name | name <- chosen, null (expansion name)]
    expanded = concatMap expansion chosen
    requested name = if null chosen then not (isOptIn name) else name `elem` expanded
    assignments = case argumentShard arguments of
        Nothing -> []
        Just (_, count) -> assignShards count (filter (not . isOptIn) names)
    inShard name = case argumentShard arguments of
        Nothing -> True
        Just (index, _) -> lookup name assignments == Just index

useWorkerProcesses :: Arguments -> Int -> Int -> Bool
useWorkerProcesses arguments jobs selectedCount =
    not (argumentChild arguments) && jobs > 1 && selectedCount > 0

-- A child's share of the processors the run may use: a runner left with fewer groups than workers (a bootstrap runner
-- with its one group) gives each of them the processors the missing workers would have had.
childCapabilities :: Int -> Int -> Int -> Int
childCapabilities jobs processors groups = max 1 (min jobs processors `div` max 1 (min jobs groups))

-- The runners of the CI matrix (.github/workflows/ci.yml) besides the host runner
ciShardCount :: Int
ciShardCount = 10

assignShards :: Int -> [String] -> [(String, Int)]
assignShards count names
    | count <= 0 = []
    -- Run 41883710449: sibling compiler tests contended with the private cold bootstrap.
    | count == ciShardCount && not (null isolated) =
        [(name, normalShards !! (index - 1))
            | (name, index) <- assignShards (length normalShards) (filter (\name -> name `notElem` map fst isolated) names)]
        ++ isolated
    | otherwise = [(name, index) | (index, assigned) <- zip [1 ..] (foldl' place (replicate (min count (length names)) []) ordered), name <- assigned]
  where
    isolated = [(name, index) | (name, index) <- zip bootstrapGroups [count - 3 ..], name `elem` names]
    normalShards = [index | index <- [1 .. count], index `notElem` map snd isolated]
    -- Longest first, then place where memory admission leaves the earliest finish.
    ordered = launchOrder id names
    place shards name =
        let cost (index, assigned) = (runnerSpan (assigned ++ [name]), sum (map groupWeight assigned), index :: Int)
            target = (\(_, _, index) -> index) (minimum (map cost (zip [1 ..] shards)))
         in [if index == target then assigned ++ [name] else assigned | (index, assigned) <- zip [1 ..] shards]

-- The worker processes of a CI runner (.github/workflows/ci.yml: -j 4)
ciWorkers :: Int
ciWorkers = 4

-- When each group of a runner starts, as the harness runs them (TestTersus.runInParallel): in launch order, as many at
-- once as there are workers and the memory budget admits, each taking its weight; with the groups running and the
-- memory charged once it has started
admissionTrace :: [String] -> [(Int, Int, Int, String)]
admissionTrace = go 0 [] . launchOrder id
  where
    go now running queue = case (if length running < ciWorkers then admitGroup memoryBudgetMiB estimatedPeakMiB (charged running) queue else Nothing) of
        Just (name, rest) ->
            let started = (now + groupWeight name, name) : running
             in (now, length started, charged started, name) : go now started rest
        Nothing -> case sort running of
            (finish, _) : others -> go finish others queue
            [] -> []
    charged running = sum [estimatedPeakMiB name | (_, name) <- running]

-- How long a runner takes for the groups
runnerSpan :: [String] -> Int
runnerSpan names = maximum (0 : [start + groupWeight name | (start, _, _, name) <- admissionTrace names])

-- Rebuilds its validator in each process rather than reading the old, much larger decoded cache entry.
-- Recent CI batches topped out at 2.3 GiB in the worker; charge 4.5 GiB for cold and subprocess headroom.
isSelfHosted :: String -> Bool
isSelfHosted = isPrefixOf "testMirSelfHosted:"

-- Material timing changes use the median of min(CPU, wall) from recent CI logs (dev/ci_weights.py).
-- The rebatched emitter rows estimate one shared link/ownership preparation and per-worker native startup.
groupWeight :: String -> Int
groupWeight name = Map.findWithDefault 1 name weightTable

-- (looked up for every step of every runner's simulation while the shards are assigned)
weightTable :: Map.Map String Int
weightTable = Map.fromList measuredWeights

measuredWeights :: [(String, Int)]
measuredWeights =
    [ ("testArrays", 50)
    , ("testAstData:1/4", 34)
    , ("testAstData:2/4", 175)
    , ("testAstData:3/4", 296)
    , ("testAstData:4/4", 43)
    , ("testAstReader:1/4", 128)
    , ("testAstReader:2/4", 18)
    , ("testAstReader:3/4", 52)
    , ("testAstReader:4/4", 433)
    , ("testBootstrap", 695)
    , ("testBorrow", 142)
    , ("testBox", 25)
    , ("testBuiltinRegistry", 1)
    , ("testBytes", 9)
    , ("testCallsAndReturnJoin", 8)
    , ("testCallsUseContracts", 81)
    , ("testCfgValidation", 32)
    , ("testCli", 17)
    , ("testClosures", 108)
    , ("testConnectives", 13)
    , ("testControlFlow", 18)
    , ("testCopies", 55)
    , ("testCrashRegression", 3)
    , ("testCrlf", 1)
    , ("testDataCodec", 465)
    , ("testDeref", 7)
    , ("testDifferential", 927)
    , ("testEnumCast", 9)
    , ("testEnums", 16)
    , ("testEq", 10)
    , ("testEqualityByParts", 7)
    , ("testErgonomics", 112)
    , ("testExamples", 40)
    , ("testFirstLast", 4)
    , ("testFncReview", 339)
    , ("testForLoops", 16)
    , ("testForallInstantiation", 4)
    , ("testForallLoops", 5)
    , ("testForallProof", 5)
    , ("testForallSyntax", 7)
    , ("testFrontendBootstrap", 1017)
    , ("testFunctionCalls", 4)
    , ("testGenericLists", 9)
    , ("testGenerics", 25)
    , ("testGoalSlices", 13)
    , ("testHashMap", 18)
    , ("testHashSet", 12)
    , ("testHaskellParity", 5)
    , ("testHeldReferences", 99)
    , ("testHostValidation:astReader", 34)
    , ("testHostValidation:elaborator", 643)
    , ("testHostValidation:emitter", 68)
    , ("testHostValidation:mirErase", 25)
    , ("testHostValidation:mirReader", 12)
    , ("testHostValidation:mirVerify", 34)
    , ("testHostValidation:parser", 123)
    , ("testIfJoin", 17)
    , ("testInferredInvariants", 16)
    , ("testIntRange", 3)
    , ("testLibModules", 107)
    , ("testLinearArithmetic", 21)
    , ("testLink", 764)
    , ("testLinkNative", 450)
    , ("testListProofs", 7)
    , ("testLists", 18)
    , ("testMir", 6)
    , ("testMirCopies", 1)
    , ("testMirData", 189)
    , ("testMirEmit:1/4", 540)
    , ("testMirEmit:2/4", 600)
    , ("testMirEmit:3/4", 330)
    , ("testMirEmit:4/4", 330)
    , ("testMirEmitPrograms", 653)
    , ("testMirEmitRecords", 472)
    , ("testMirErase", 175)
    , ("testMirEvalLists", 6)
    , ("testMirLowered:1/4", 36)
    , ("testMirLowered:2/4", 460)
    , ("testMirLowered:3/4", 382)
    , ("testMirLowered:4/4", 69)
    , ("testMirMono", 365)
    , ("testMirMonoOwnership", 71)
    , ("testMirOwnership", 292)
    , ("testMirPacks", 283)
    , ("testMirReader", 270)
    , ("testMirSelfHosted:1/4", 334)
    , ("testMirSelfHosted:2/4", 242)
    , ("testMirSelfHosted:3/4", 347)
    , ("testMirSelfHosted:4/4", 401)
    , ("testMirSupport", 783)
    , ("testMirVerify:1/4", 141)
    , ("testMirVerify:2/4", 105)
    , ("testMirVerify:3/4", 200)
    , ("testMirVerify:4/4", 112)
    , ("testMirVerifyPrograms", 263)
    , ("testModules:1/4", 346)
    , ("testModules:2/4", 100)
    , ("testModules:3/4", 179)
    , ("testModules:4/4", 107)
    , ("testModulo", 12)
    , ("testMulDivNegative", 7)
    , ("testNative:1/4", 247)
    , ("testNative:2/4", 234)
    , ("testNative:3/4", 230)
    , ("testNative:4/4", 183)
    , ("testNativeErgonomics", 88)
    , ("testNativeStorageModules", 663)
    , ("testOwnership", 262)
    , ("testOwnershipCodec", 351)
    , ("testOwnershipInterpreted", 308)
    , ("testOwnershipMetadata", 1)
    , ("testParity:mirReader", 201)
    , ("testParity:validation", 1090)
    , ("testParse", 1)
    , ("testParseEval", 1)
    , ("testParseVal", 3)
    , ("testParseValFail", 1)
    , ("testParser:1/4", 270)
    , ("testParser:2/4", 213)
    , ("testParser:3/4", 219)
    , ("testParser:4/4", 48)
    , ("testParserBootstrap:1/2", 659)
    , ("testParserBootstrap:2/2", 612)
    , ("testParserUnicode", 12)
    , ("testPhase1Cache", 122)
    , ("testPhase1Packages", 21)
    , ("testPhase2Packages", 30)
    , ("testPipeline", 7)
    , ("testPointers", 38)
    , ("testPrecedence", 2)
    , ("testPrettyProofs", 3)
    , ("testRecursion", 6)
    , ("testRefinedArithmetic", 9)
    , ("testScheduling", 16)
    , ("testSequence", 42)
    , ("testSharedCache:1/4", 9)
    , ("testSharedCache:2/4", 6)
    , ("testSharedCache:3/4", 252)
    , ("testSharedCache:4/4", 590)
    , ("testSharedCacheProbe", 1)
    , ("testSolverCache", 4)
    , ("testStdGraph", 16)
    , ("testStrings", 141)
    , ("testStructs", 12)
    , ("testTermination", 14)
    , ("testThreads", 80)
    , ("testTraits", 62)
    , ("testTypeCheck", 3)
    , ("testUserRewriteValidation", 2)
    , ("testValidateWithExpectedMatch", 1)
    , ("testValidateWithExpectedMismatch", 1)
    , ("testValidationCache", 17)
    , ("testValidationFail", 38)
    , ("testVariadic", 188)
    , ("testVerdictLocks", 1)
    ]

-- The budget leaves the OS and runner of the 16 GB CI machine about 3.6 GiB.
-- Use observed process peaks plus headroom (dev/ci_weights.py --peaks). These are admission estimates, not limits.
estimatedPeakMiB :: String -> Int
estimatedPeakMiB name
    | isSelfHosted name = 4608
    | otherwise = Map.findWithDefault 1024 name peakTable

peakTable :: Map.Map String Int
peakTable = Map.fromList measuredPeaksMiB

-- Any of the four shared MIR probes can own the cold build; charge it in each.
measuredPeaksMiB :: [(String, Int)]
measuredPeaksMiB =
    [ ("testAstData:2/4", 1280)
    , ("testAstData:3/4", 2304)
    , ("testAstReader:1/4", 2304)
    , ("testAstReader:2/4", 2816)
    , ("testAstReader:3/4", 4608)
    , ("testAstReader:4/4", 2560)
    , ("testBorrow", 1536)
    , ("testCallsUseContracts", 1792)
    , ("testClosures", 1280)
    , ("testControlFlow", 1280)
    , ("testDataCodec", 2304)
    , ("testDifferential", 11520)
    , ("testErgonomics", 1536)
    , ("testFncReview", 4608)
    , ("testFrontendBootstrap", 6912)
    , ("testHeldReferences", 1280)
    , ("testHostValidation:elaborator", 8704)
    , ("testHostValidation:emitter", 7168)
    , ("testHostValidation:parser", 2048)
    , ("testLibModules", 1280)
    , ("testLink", 5120)
    , ("testLinkNative", 5120)
    , ("testMirCopiesFused", 4608)
    , ("testMirCopiesParity", 4608)
    , ("testMirCopyKeys", 4608)
    , ("testMirData", 1536)
    , ("testMirEmit:1/4", 9216)
    , ("testMirEmit:2/4", 9216)
    , ("testMirEmit:3/4", 9216)
    , ("testMirEmit:4/4", 9216)
    , ("testMirEmitPrograms", 8704)
    , ("testMirEmitRecords", 9216)
    , ("testMirErase", 1536)
    , ("testMirLowered:2/4", 4096)
    , ("testMirLowered:3/4", 1536)
    , ("testMirMono", 9472)
    , ("testMirMonoOwnership", 1280)
    , ("testMirOwnership", 1280)
    , ("testMirPacks", 4608)
    , ("testMirReader", 1536)
    , ("testMirSupport", 8448)
    , ("testMirVerify:1/4", 1536)
    , ("testMirVerify:2/4", 3840)
    , ("testMirVerify:3/4", 1536)
    , ("testMirVerify:4/4", 3840)
    , ("testMirVerifyPrograms", 1536)
    , ("testModules:1/4", 2048)
    , ("testModules:2/4", 2048)
    , ("testModules:3/4", 1280)
    , ("testNative:1/4", 1280)
    , ("testNative:2/4", 1280)
    , ("testNative:3/4", 1280)
    , ("testNative:4/4", 1280)
    , ("testNativeErgonomics", 1280)
    , ("testNativeStorageModules", 8704)
    , ("testOwnership", 2048)
    , ("testOwnershipCodec", 2048)
    , ("testOwnershipInterpreted", 8704)
    , ("testParity:mirReader", 1280)
    , ("testParity:validation", 1792)
    , ("testParser:1/4", 6144)
    , ("testParser:2/4", 8448)
    , ("testParser:3/4", 14336)
    , ("testParser:4/4", 4352)
    , ("testParserBootstrap:2/2", 4352)
    , ("testPhase1Cache", 4608)
    , ("testPrettyProofs", 1280)
    , ("testSharedCache:3/4", 8192)
    , ("testSharedCache:4/4", 2304)
    , ("testThreads", 1280)
    , ("testVariadic", 1280)
    ]

memoryBudgetMiB :: Int
memoryBudgetMiB = 12288

-- The first queued group whose estimate fits beside the running ones; with none running, the first group,
-- however large, so that a group estimated over the budget runs alone instead of never.
admitGroup :: Int -> (a -> Int) -> Int -> [a] -> Maybe (a, [a])
admitGroup budget estimate used queue = case break fits queue of
    (before, item : after) -> Just (item, before ++ after)
    (_, []) -> Nothing
  where
    fits item = used == 0 || used + estimate item <= budget

-- Longest first: a runner is done when its last group is, so the groups that take minutes start before the short ones.
-- Self-hosted batches build independently and no longer need a separate launch priority.
launchOrder :: (a -> String) -> [a] -> [a]
launchOrder name = sortBy (comparing (negate . groupWeight . name))

groupName :: Test -> String
groupName (TestCase name _) = name
groupName (TestList name _) = name
groupName (TestParallel name _) = name

leafTests :: Test -> [Test]
leafTests test@TestCase{} = [test]
-- Groups that share an expensive fixture or overwrite the same native test file must stay in one process.
leafTests test@(TestList name _) | name `elem` ["memory", "linked emitter"] = [test]
leafTests (TestList name tests) = [TestList name [leaf] | test <- tests, leaf <- leafTests test]
leafTests (TestParallel name tests) = [TestParallel name [leaf] | test <- tests, leaf <- leafTests test]

leafActions :: Test -> [([String], IO TestResult)]
leafActions (TestCase name action) = [([name], action)]
leafActions (TestList name tests) = under name tests
leafActions (TestParallel name tests) = under name tests

under :: String -> [Test] -> [([String], IO TestResult)]
under name tests = [(name : path, action) | test <- tests, (path, action) <- leafActions test]

leafPaths :: Test -> [[String]]
leafPaths = map fst . leafActions

splitTestGroups :: Int -> Test -> [Test]
splitTestGroups count original
    | count <= 1 = [original]
    | otherwise =
        [TestList (groupName original ++ ":" ++ show index ++ "/" ++ show batchCount)
            (map snd (sortBy (comparing fst) leaves))
        | (_, index, leaves) <- bins]
  where
    units = zip [0 :: Int ..] (leafTests original)
    batchCount = min count (length units)
    bins = foldl' assign [(0, index, []) | index <- [1 .. batchCount]]
        (sortBy (comparing (negate . unitWeight . snd)) units)
    assign batches unit@(_, test) =
        let (_, target, _) = minimumBy (comparing (\(weight, index, _) -> (weight, index))) batches
         in [if index == target then (weight + unitWeight test, index, unit : leaves) else batch
            | batch@(weight, index, leaves) <- batches]
    unitWeight :: Test -> Int
    unitWeight test = case concat (leafPaths test) of
        path | any (`elem` path) ["whole corpus parity", "whole parsed and elaborated source corpus", "whole corpus native round trip", "the text protocol loses nothing over the corpus"] -> 60
        path | "linked emitter" `elem` path -> 60
        path | "validator package keeps bare helpers and reference calls never run driver main" `elem` path -> 250
        path | "late top-level definitions consume expression types once" `elem` path && last path == "0" -> 110
        path | "native-module-loader" `elem` path && "lib/parser/parser.tersus" `elem` path -> 85
        path | "lib/mir/emit/emit.tersus" `elem` path || "lib/mir/mir_reader/mir_reader.tersus" `elem` path -> 30
        path | "the IR of a loop, interpreted" `elem` path || "raw lists and Boxes library" `elem` path -> 30
        path | "MIR loops" `elem` path -> 32
        path | "corpus" `elem` path && any (`elem` path) ["examples", "lib/elaborate/elaborate.tersus"] -> 60
        path | "diagnostic observation borrows the parser state without copying its arena" `elem` path -> 40
        path | any (`elem` path) ["compileFromValidated reuses the exact validated sentinel", "changed embedded source still fails validation independently", "truncated named List declaration is refused natively"] -> 60
        path | "MIR branches" `elem` path -> 16
        path | any (`elem` path) ["MIR contracts", "MIR sequences", "MIR data", "MIR list updates"] -> 8
        path | "interpreted" `elem` path || "pre-erasure, interpreted" `elem` path
            || "function-list identity, interpreted" `elem` path || "call metadata, interpreted" `elem` path -> 5
        _ -> length (leafPaths test)

-- Observe the real dispatch through the existing no-compiler probe group.
routingProbe :: [String] -> Maybe Int -> Bool -> Bool -> IO TestResult
routingProbe arguments capabilities worker summarized = do
    self <- getExecutablePath
    inherited <- getEnvironment
    let environment = [("TERSUS_TEST_ROUTING_PROBE", "1"), ("TERSUS_TEST_RTS_STATS", "1")]
            ++ [(key, value) | (key, value) <- inherited, key `notElem` ["TERSUS_TEST_ROUTING_PROBE", "TERSUS_TEST_RTS_STATS"]]
    outcome <- timeout 30000000 (readProcessOutput
        (proc self (arguments ++ ["+RTS", "-N2", "-RTS"])){env = Just environment} "")
    pure $ case outcome of
        Nothing -> Just "routing probe did not finish"
        Just (code, output, errors) ->
            let actualCaps = [line | line <- lines output, "[CAPABILITIES]" `isPrefixOf` line]
                expectedCaps = maybe [] (\count -> ["[CAPABILITIES] " ++ show count]) capabilities
                starts = length [() | line <- lines output, "[START] testSharedCacheProbe" `isPrefixOf` line]
                times = length [() | line <- lines output, "[TIME] testSharedCacheProbe" `isPrefixOf` line]
                passes = length [() | line <- lines output, "[PASS] testSharedCacheProbe" `isPrefixOf` line]
                expectedPasses = maybe 0 (const 1) capabilities
             in if code == ExitSuccess && actualCaps == expectedCaps
                    && starts == (if worker then 1 else 0) && times == starts
                    && passes == expectedPasses
                    && ("Summary:" `isInfixOf` output) == summarized
                    && (not worker || maybe False (\count -> ("using -N" ++ show count) `isInfixOf` errors) capabilities)
                    then Nothing
                    else Just ("unexpected worker routing: " ++ show (code, output, errors))

testScheduling :: [String] -> [(Test, [Test])] -> Test
testScheduling names batches = TestList "testScheduling"
    [ testCase "no flags select every group but the opt-in ones" $
        testAssertEq (parseArguments [] >>= (`selectGroupNames` names)) (Right suite)
    , testCase "job forms and group filters are preserved" $
        testAssertTrue (all (== Right (Arguments (Just 2) ["testCli"] False Nothing))
            [parseArguments ["testCli", "-j", "2"], parseArguments ["--jobs", "2", "testCli"],
             parseArguments ["-j2", "testCli"], parseArguments ["--jobs=2", "testCli"]])
    , testCase "both shard forms parse alongside jobs and filters" $
        testAssertTrue (all (== Right (Arguments (Just 4) ["testCli"] False (Just (2, 3))))
            [parseArguments ["--shard", "2/3", "-j", "4", "testCli"],
             parseArguments ["testCli", "--jobs=4", "--shard=2/3"]])
    , testCase "malformed, duplicate and child shard flags are rejected" $
        testAssertTrue (all isLeft
            ([parseArguments ["--shard", text] | text <- invalidShards]
                ++ map parseArguments [["--shard"], ["--shard="], ["--shard", "1/3", "--shard=2/3"],
                    ["--child", "--shard", "1/3"], ["--shard=1/3", "--child"]]))
    , testCase "invalid jobs and unknown options are rejected before tests" $
        testAssertTrue (all (isLeft . parseArguments)
            [["-j"], ["--jobs"], ["-j0"], ["--jobs=-1"], ["-j", "wat"], ["--shrad=1/3"]])
    , testCase "child arguments select the original single group without a shard" $
        testAssertEq (parseArguments ["testCli", "--child"] >>= (`selectGroupNames` names)) (Right ["testCli"])
    , testCase "worker dispatch preserves child, serial and empty routing" $
        let arguments child = Arguments (Just 4) [] child Nothing
         in testAssertTrue (useWorkerProcesses (arguments False) 4 1
            && useWorkerProcesses (arguments False) 4 2
            && not (useWorkerProcesses (arguments True) 4 1)
            && not (useWorkerProcesses (arguments False) 1 1)
            && not (useWorkerProcesses (Arguments Nothing [] False Nothing) 1 1)
            && not (useWorkerProcesses (arguments False) 4 0))
    , TestCase "explicit parallel single group uses one worker with the run's processors and RTS statistics" $ do
        processors <- availableProcessors
        routingProbe ["-j", "4", "testSharedCacheProbe"] (Just (min 4 processors)) True True
    , testCase "children share the run's processors among the groups that run at once" $
        testAssertEq [childCapabilities 4 4 40, childCapabilities 4 4 1, childCapabilities 4 4 2, childCapabilities 4 96 1, childCapabilities 4 2 1, childCapabilities 1 4 1, childCapabilities 4 4 0]
            [1, 4, 2, 4, 2, 1, 4]
    , TestCase "default single group retains the parent RTS" $
        routingProbe ["testSharedCacheProbe"] (Just 2) False True
    , TestCase "serial single group retains the parent RTS" $
        routingProbe ["-j", "1", "testSharedCacheProbe"] (Just 2) False True
    , TestCase "explicit parallel child stays in process and cannot recurse" $
        routingProbe ["-j", "4", "testSharedCacheProbe", "--child"] (Just 2) False False
    , TestCase "empty explicit parallel selection launches no child" $
        routingProbe ["-j", "4", "--shard", "999/999", "testSharedCacheProbe"] Nothing False True
    , testCase "all registered group names are unique" $
        testAssertEq (length names) (length (unique names))
    , testCase "every group belongs to exactly one shard for every tested count" $
        testAssertTrue (all complete [1 .. length names + 1])
    , testCase "the CI shards reserve the last four for the bootstrap groups, one each" $
        let assigned = assignShards ciShardCount names
         in testAssertTrue (and [[name | (name, shard) <- assigned, shard == index] == [group]
                | (group, index) <- zip bootstrapGroups [ciShardCount - 3 ..]]
            && [(name, shard) | (name, shard) <- assigned, name `notElem` bootstrapGroups]
                == assignShards (ciShardCount - 4) (filter (`notElem` bootstrapGroups) names))
    , testCase "CI shard isolation retains aliases and filtered bootstrap selection" $
        testAssertTrue (all (\index ->
            selectGroupNames (Arguments Nothing ["testBootstrap"] False (Just (index, ciShardCount))) names
                == Right ["testBootstrap" | index == ciShardCount - 1]
            && selectGroupNames (Arguments Nothing ["testParserBootstrap"] False (Just (index, ciShardCount))) names
                == Right (["testParserBootstrap:1/2" | index == ciShardCount - 3] ++ ["testParserBootstrap:2/2" | index == ciShardCount - 2])
            && selectGroupNames (Arguments Nothing ["testFrontendBootstrap"] False (Just (index, ciShardCount))) names
                == Right ["testFrontendBootstrap" | index == ciShardCount]
            && selectGroupNames (Arguments Nothing ["testNative"] False (Just (index, ciShardCount))) names
                == Right [name | name <- names, "testNative:" `isPrefixOf` name,
                    lookup name (assignShards ciShardCount suite) == Just index]) [1 .. ciShardCount])
    , testCase "bootstrap isolation is limited to the CI shard count and handles sparse inputs" $
        let c = ciShardCount
         in testAssertTrue
            ( assignShards c ["testBootstrap"] == [("testBootstrap", c - 1)]
              && assignShards c ["testParserBootstrap:2/2"] == [("testParserBootstrap:2/2", c - 2)]
              && assignShards c ["testParserBootstrap:1/2"] == [("testParserBootstrap:1/2", c - 3)]
              && assignShards c ["testFrontendBootstrap"] == [("testFrontendBootstrap", c)]
              && assignShards c ["testParserBootstrap:2/2", "newA", "newB", "newC", "newD", "newE", "newF", "newG"]
                  == [("newA", 1), ("newB", 2), ("newC", 3), ("newD", 4), ("newE", 5), ("newF", 6), ("newG", c - 3), ("testParserBootstrap:2/2", c - 2)]
              && assignShards c ["testBootstrap", "testParserBootstrap:1/2", "testParserBootstrap:2/2"]
                  == [("testParserBootstrap:1/2", c - 3), ("testParserBootstrap:2/2", c - 2), ("testBootstrap", c - 1)]
              && assignShards c ["newA", "newB"] == [("newA", 1), ("newB", 2)]
              && assignShards 1 ["testBootstrap", "newA"] == [("testBootstrap", 1), ("newA", 1)]
              && sort (map snd (assignShards 2 ["testBootstrap", "newA"])) == [1, 2]
              && map snd (assignShards 7 ["testFrontendBootstrap"]) == [1]
              && null (assignShards 0 ["testBootstrap"])
              && null (assignShards c []))
    , testCase "examples and strings remain unbatched to avoid duplicate cold startup" $
        testAssertTrue (all (`elem` names) ["testExamples", "testStrings"]
            && not (any (\name -> "testExamples:" `isPrefixOf` name || "testStrings:" `isPrefixOf` name) names))
    , testCase "empty groups and invalid partition counts are safe" $
        testAssertTrue (null (assignShards 3 []) && null (assignShards 0 names) && null (assignShards (-1) names))
    , testCase "unprofiled groups are retained and ties are deterministic" $
        testAssertEq (assignShards 2 ["newA", "newB", "newC"]) [("newA", 1), ("newC", 1), ("newB", 2)]
    , testCase "largest measured registered groups are spread before small groups" $
        let groups = ["testNative:1/4", "testMirVerify:1/4", "testMirEmit:1/4", "testBootstrap"]
            assigned = assignShards 3 groups
            heaviest = take 3 (sortBy (comparing (negate . groupWeight)) groups)
         in testAssertEq (sort [shard | (name, shard) <- assigned, name `elem` heaviest]) [1, 2, 3]
    , testCase "the normal CI runners' simulated spans differ by at most two minutes" $
        if maximum loads - minimum loads <= 120 then Nothing else Just ("simulated spans: " ++ show loads)
    , testCase "CLI and cold bootstrap are covered exactly once" $
        testAssertTrue (all (\name -> length (filter ((== name) . fst) assignments) == 1)
            ("testCli" : bootstrapGroups))
    , testCase "explicit filters intersect the full-suite shard assignment" $
        testAssertTrue (all filtered [1 .. 3])
    , testCase "unknown explicit groups fail even on an empty shard" $
        testAssertTrue (isLeft (selectGroupNames (Arguments Nothing ["noSuchGroup"] False (Just (99, 99))) names))
    , testCase "huge valid shard counts do not allocate one bin per empty shard" $
        testAssertEq (selectGroupNames (Arguments Nothing [] False (Just (maxBound, maxBound))) names) (Right [])
    , testCase "corpus batches retain every indexed occurrence, duplicates and source order" $
        let values = zip [0 :: Int ..] ["same", "other", "same", "last", "same", "tail"]
            parts = [batchItems 4 batch values | batch <- [1 .. 4]]
         in testAssertTrue (sort (concat parts) == values && all (\part -> sort part == part) parts
            && null (batchItems 0 1 values) && null (batchItems 4 0 values) && null (batchItems 4 5 values))
    , testCase "AST and parser batches each retain one complete corpus chunk" $
        testAssertTrue (all (\(original, split) ->
            if groupName original `elem` ["testAstData", "testParser", "testAstReader"] then
                let label = case groupName original of
                        "testAstData" -> "whole parsed and lowered source corpus"
                        "testAstReader" -> "whole corpus native round trip"
                        _ -> "whole corpus parity"
                    chunks batch = [last path | path <- leafPaths batch, label `elem` path]
                 in all ((== 1) . length . chunks) split
                    && sort (concatMap chunks split) == ["1/4", "2/4", "3/4", "4/4"]
            else True) batches)
    , testCase "parser bootstrap partitions retain the original twelve cold and two primed cases" $
        testAssertTrue (map (length . leafPaths) parserBootstrapGroups == [12,2]
            && sort (concatMap (map (drop 1) . leafPaths) parserBootstrapGroups) == sort (leafPaths testParserBootstrap)
            && map last (leafPaths (last parserBootstrapGroups))
                == ["same-process transient failures repair without stale library or executable caches", "P0 P1 current-source fixpoint regenerates identical IR and P2 behavior"])
    , testCase "parser bootstrap aliases and child names select the two registered partitions" $
        testAssertTrue (aliasComplete (testParserBootstrap, parserBootstrapGroups)
            && all (\batch -> selectGroupNames (Arguments Nothing [groupName batch] True Nothing) names
                == Right [groupName batch]) parserBootstrapGroups)
    , testCase "all old leaf paths occur exactly once in the registered batches" $
        testAssertTrue (all (\(original, split) ->
            sort (leafPaths original) == sort (concatMap (map (drop 1) . leafPaths) split)) batches)
    , testCase "each expensive group has four nonempty registered batches (fewer if it has fewer cases) and no original duplicate" $
        testAssertTrue (all (\(original, split) -> length split == min 4 (length (leafTests original))
            && groupName original `notElem` names
            && all (\batch -> groupName batch `elem` names && not (null (leafPaths batch))) split) batches)
    -- The unprofiled fallback is weight 1, so weight > 1 for every batched and
    -- measured tail group catches a fallback to weight 1 without snapshotting
    -- the measured values themselves.
    , testCase "batched and measured tail groups retain weights above the unprofiled fallback" $
        testAssertTrue (all (> 1) ([groupWeight (groupName batch) | (_, split) <- batches, batch <- split]
                ++ map groupWeight ["testParity:validation", "testParity:mirReader", "testMirData", "testOwnership", "testMirEmitPrograms"]
                ++ map (groupWeight . groupName) parserBootstrapGroups)
            && all (> 0) (map groupWeight names)
            && maximum loads - minimum loads <= 120)
    , testCase "old aliases expand to all batches without duplicates" $
        testAssertTrue (all aliasComplete batches)
    , testCase "alias filters intersect the full-suite shard assignment" $
        testAssertTrue (all (\batch -> all (aliasFiltered batch) [1 .. 4]) batches)
    , testCase "child batch names with punctuation select only that batch" $
        testAssertTrue (all (\(_, split) -> all (\batch ->
            (parseArguments [groupName batch, "--child"] >>= (`selectGroupNames` names))
                == Right [groupName batch]) split) batches)
    , TestCase "mixed fixed and parallel leaves execute once with every prefix retained" $ do
        seen <- newIORef ([] :: [Int])
        let action index = modifyIORef' seen (++ [index]) >> pure (Just ("result " ++ show index))
            leaf index = TestCase "duplicate label" (action index)
            fixture = TestList "root"
                [ TestParallel "parallel" [leaf 1, leaf 2]
                , TestList "fixed" [leaf 3, leaf 4]
                , TestList "memory" [leaf 5, leaf 6]
                ]
            split = splitTestGroups 4 fixture
            paths = concatMap (map (drop 1) . leafPaths) split
            actions = [map snd (leafActions batch) | batch <- split]
            traces = [[5,6], [1,4], [2], [3]]
            expected = [(trace, [Just ("result " ++ show index) | index <- trace]) | trace <- traces]
            observe = mapM (\batch -> do
                writeIORef seen []
                results <- sequence batch
                trace <- readIORef seen
                pure (trace, results))
            replace batch = case batch of
                [] -> []
                _ : rest -> action 99 : rest
            wrap original = modifyIORef' seen (++ [0]) >> original
        _ <- evaluate (sum (map length paths))
        beforeExecution <- readIORef seen
        actual <- observe actions
        equivalent <- observe (map (map (>>= pure)) actions)
        changed <- mapM observe
            [ map (drop 1) actions
            , map (\batch -> batch ++ take 1 batch) actions
            , map replace actions
            , map (map wrap) actions
            , map reverse actions
            ]
        pure (testAssertEq beforeExecution []
            <> testAssertEq actual expected
            <> testAssertEq equivalent expected
            <> testAssertTrue (all (/= expected) changed)
            <> testAssertEq (sort paths) (sort (leafPaths fixture)))
    , -- (the queries that compared the Haskell engine with the Tersus one went with the engine)
      testCase "every self-hosted query assertion remains in its family" $
        testAssertEq selfHostedFamilyManifest
            [("products", 225), ("relations", 27), ("entailment cache", 2), ("execution", 61), ("driver", 54),
             ("MIR contracts", 60), ("MIR arithmetic", 22), ("MIR sequences", 32), ("MIR data", 21),
             ("MIR list updates", 19), ("MIR branches", 14), ("MIR loops", 22), ("bridges", 19),
             ("join hull", 35), ("loop candidate provenance", 7), ("goal slices", 17)]
    , testCase "self-hosted batches can use separate CI runners" $
        let assigned = assignShards ciShardCount suite
         in testAssertTrue (length (unique [index | (name, index) <- assigned, isSelfHosted name]) > 1)
    , testCase "other original groups remain individually shardable" $
        testAssertEq (map snd (assignShards 4 ["testNative:1/4", "testNative:2/4", "testNative:3/4", "testNative:4/4"]))
            [1,2,3,4]
    , testCase "independent self-hosted batches can overlap within the memory budget" $
        let selfHosted = filter isSelfHosted names
         in testAssertTrue (runnerSpan selfHosted < sum (map groupWeight selfHosted))
    , testCase "fixed native memory_limit users stay ordered in one batch" $
        testAssertTrue (all (sameBatch "memory") batches)
    , testCase "linked emitter checks share one worker and stay in order" $
        testAssertTrue (all (sameBatch "linked emitter") batches
            && length [path | (original, _) <- batches, path <- leafPaths original, "linked emitter" `elem` path] == 3)
    , testCase "small and empty trees never create empty batches" $
        testAssertTrue (null (splitTestGroups 4 (TestList "empty" []))
            && map groupName (splitTestGroups 4 (testCase "single" Nothing)) == ["single:1/1"])
    , testCase "every MIR probe group can be charged as the cold build owner" $
        testAssertTrue (all ((>= 4608) . estimatedPeakMiB) ["testMirPacks", "testMirCopyKeys", "testMirCopiesParity", "testMirCopiesFused"])
    , testCase "every CI shard's groups launch once, with estimated memory within the budget whenever two run" $
        testAssertTrue (all (\index -> case selectGroupNames (Arguments Nothing [] False (Just (index, ciShardCount))) names of
            Right shard -> let trace = admissionTrace shard
                 in sort [name | (_, _, _, name) <- trace] == sort shard
                    && all (\(_, running, used, _) -> running < 2 || used <= memoryBudgetMiB) trace
            Left _ -> False) [1 .. ciShardCount])
    , testCase "the host runner's groups launch once, with estimated memory within the budget whenever two run" $
        case selectGroupNames (Arguments Nothing ["testHostValidation"] False Nothing) names of
            Right host -> let trace = admissionTrace host
                 in testAssertTrue (length host == 7 && sort [name | (_, _, _, name) <- trace] == sort host
                    && all (\(_, running, used, _) -> running < 2 || used <= memoryBudgetMiB) trace)
            Left e -> Just e
    , testCase "naming an opt-in group with a shard is refused" $
        testAssertTrue (isLeft (selectGroupNames (Arguments Nothing ["testHostValidation"] False (Just (1, ciShardCount))) names))
    , testCase "opt-in groups take no part in the shard assignment" $
        testAssertTrue (any isOptIn names && all (\count -> all (\index ->
            fmap (any isOptIn) (selectGroupNames (Arguments Nothing [] False (Just (index, count))) names) == Right False)
            [1 .. count]) [1, 3, 7])
    , testCase "a memory-heavy emitter check admits a small filler, not another large MIR group" $
        testAssertEq (admitWhileRoom ["testMirEmit:1/4", "testMirSupport", "testCli"]) ["testMirEmit:1/4", "testCli"]
    , testCase "an oversized group runs alone, and launch order is longest work first with stable ties" $
        testAssertEq
            ( admitGroup 1000 snd 0 [("big", 4000 :: Int), ("small", 10)]
            , admitGroup 1000 snd 4000 [("big", 4000 :: Int), ("small", 10)]
            , launchOrder id ["newA", "testCli", "newB"] )
            ( Just (("big", 4000), [("small", 10)])
            , Nothing
            , ["testCli", "newA", "newB"] )
    ]
  where
    admitWhileRoom = go 0
      where
        go used queue = case admitGroup memoryBudgetMiB estimatedPeakMiB used queue of
            Just (name, rest) -> name : go (used + estimatedPeakMiB name) rest
            Nothing -> []
    suite = filter (not . isOptIn) names
    assignments = assignShards 3 suite
    normalCount = ciShardCount - length bootstrapGroups
    loads = [runnerSpan [name | (name, assigned) <- assignShards normalCount (filter (`notElem` bootstrapGroups) suite), assigned == index] | index <- [1 .. normalCount]]
    -- (the selections, which assign the shards again for each index, only for the counts CI could use)
    complete count =
        let assigned = assignShards count names
            selected = [selectGroupNames (Arguments Nothing [] False (Just (index, count))) names | index <- [1 .. count]]
         in sort (map fst assigned) == sort names
            && all (\(_, index) -> index >= 1 && index <= count) assigned
            && (count > ciShardCount || fmap (sort . concat) (sequence selected) == Right (sort suite))
    filtered index =
        let chosen = ["testCli", "testBootstrap"] ++ [groupName batch | (_, split) <- batches, batch <- take 1 split]
         in selectGroupNames (Arguments Nothing chosen False (Just (index, 3))) names
            == Right [name | name <- names, name `elem` chosen, lookup name assignments == Just index]
    aliasComplete (original, split) =
        let alias = groupName original
            expected = map groupName split
         in selectGroupNames (Arguments Nothing [alias] False Nothing) names == Right expected
            && selectGroupNames (Arguments Nothing (alias : expected ++ [alias]) False Nothing) names == Right expected
    aliasFiltered (original, split) index =
        selectGroupNames (Arguments Nothing [groupName original] False (Just (index, 4))) names
            == Right [groupName batch | batch <- split,
                lookup (groupName batch) (assignShards 4 suite) == Just index]
    sameBatch label (original, split) =
        let originalPaths = filter (elem label) (leafPaths original)
            holders = [filter (elem label) (map (drop 1) (leafPaths batch)) | batch <- split]
         in null originalPaths || filter (not . null) holders == [originalPaths]
    unique :: Eq a => [a] -> [a]
    unique = foldl' (\seen name -> if name `elem` seen then seen else name : seen) []
    invalidShards = ["", "1", "0/3", "1/0", "4/3", "-1/3", "1/-3", "1/3/2", "1//3", "/3", "1/", "one/3", "1/three", "1.0/3", " 1/3", "1/3 ", "1/+3", show (toInteger (maxBound :: Int) + 1) ++ "/3", "1/" ++ show (toInteger (maxBound :: Int) + 1)]
    isLeft (Left _) = True
    isLeft (Right _) = False

-- (in the order of the last four CI shards they are given)
bootstrapGroups :: [String]
bootstrapGroups = ["testParserBootstrap:1/2", "testParserBootstrap:2/2", "testBootstrap", "testFrontendBootstrap"]
