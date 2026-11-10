module TestScheduling
    ( Arguments (..)
    , parseArguments
    , selectGroupNames
    , useWorkerProcesses
    , assignShards
    , groupWeight
    , isSelfHosted
    , splitTestGroups
    , groupName
    , leafPaths
    , testScheduling
    ) where

import Control.Exception (evaluate)
import Data.Char (isDigit)
import Data.IORef (modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (delete, foldl', isInfixOf, isPrefixOf, minimumBy, sort, sortBy)
import System.Environment (getEnvironment, getExecutablePath)
import System.Exit (ExitCode (..))
import System.Process (CreateProcess (..), proc)
import Native (readProcessOutput)
import System.Timeout (timeout)
import Data.Ord (comparing)
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

selectGroupNames :: Arguments -> [String] -> Either String [String]
selectGroupNames arguments names
    | not (null unknown) = Left ("unknown test groups: " ++ unwords unknown)
    | otherwise = Right [name | name <- names, requested name, inShard name]
  where
    chosen = argumentGroups arguments
    expansion name = [registered | registered <- names,
        registered == name || (name ++ ":") `isPrefixOf` registered]
    unknown = [name | name <- chosen, null (expansion name)]
    expanded = concatMap expansion chosen
    requested name = null chosen || name `elem` expanded
    assignments = case argumentShard arguments of
        Nothing -> []
        Just (_, count) -> assignShards count names
    inShard name = case argumentShard arguments of
        Nothing -> True
        Just (index, _) -> lookup name assignments == Just index

useWorkerProcesses :: Arguments -> Int -> Int -> Bool
useWorkerProcesses arguments jobs selectedCount =
    not (argumentChild arguments) && jobs > 1 && selectedCount > 0

assignShards :: Int -> [String] -> [(String, Int)]
assignShards count names
    | count <= 0 = []
    -- Run 41883710449: sibling compiler tests contended with the private cold bootstrap.
    | count == 7 && not (null isolated) =
        [(name, normalShards !! (index - 1))
            | (name, index) <- assignShards (length normalShards) (filter (\name -> name `notElem` map fst isolated) names)]
        ++ isolated
    | otherwise = [(name, index) | (_, index, assigned) <- balance bins, unit <- reverse assigned, name <- unit]
  where
    isolated = [(name, index) | (name, index) <- [("testParserBootstrap:1/2", 4), ("testParserBootstrap:2/2", 5), ("testBootstrap", 6), ("testFrontendBootstrap", 7)], name `elem` names]
    normalShards = [index | index <- [1 .. 7], index `notElem` map snd isolated]
    selfHosted = filter isSelfHosted names
    units = [selfHosted | not (null selfHosted)] ++ [[name] | name <- names, not (isSelfHosted name)]
    bins = foldl' assign [(0, index, []) | index <- [1 .. min count (length names)]]
        (sortBy (comparing (negate . shardWeight)) units)
    assign shards unit =
        let (_, target, _) = minimumBy (comparing (\(weight, index, _) -> (weight, index))) shards
         in [if index == target then (weight + shardWeight unit, index, unit : assigned) else shard
            | shard@(weight, index, assigned) <- shards]
    balance [] = []
    balance shards
        | spread shards <= 1 = shards
        | spread best < spread shards = balance best
        | otherwise = shards
      where
        (_, heavy, heavyUnits) = minimumBy (comparing (\(weight, index, _) -> (negate weight, index))) shards
        (_, light, lightUnits) = minimumBy (comparing (\(weight, index, _) -> (weight, index))) shards
        best = minimumBy (comparing spread) (shards :
            [exchange outgoing incoming | outgoing <- heavyUnits, incoming <- [] : lightUnits])
        exchange outgoing incoming =
            [ if index == heavy then (weight - shardWeight outgoing + shardWeight incoming, index, replace outgoing incoming assigned)
              else if index == light then (weight + shardWeight outgoing - shardWeight incoming, index, replace incoming outgoing assigned)
              else shard
            | shard@(weight, index, assigned) <- shards]
        replace outgoing incoming assigned = [incoming | not (null incoming)] ++ delete outgoing assigned
    spread shards = maximum loads - minimum loads
      where loads = [weight | (weight, _, _) <- shards]

isSelfHosted :: String -> Bool
isSelfHosted = isPrefixOf "testMirSelfHosted:"

shardWeight :: [String] -> Int
shardWeight names = sum [groupWeight name | name <- names, not (isSelfHosted name)]
    + case [groupWeight name | name <- names, isSelfHosted name] of
        [] -> 0
        work -> maximum work

-- Measured four-CPU warm-tool work on eb8bb49 (2026-11-05), rounded up; the testAstData, testAstReader and
-- testDifferential batches on the commit that added interface data (2026-11-08); testDifferential
-- after it left the compiler's own packages (one CPU, warm tools, scaled as the earlier batches).
-- The native preparation prefix is measured separately; genuine cold A and
-- Bootstrap include their cold work. Unmeasured rows retain run 41978818567.
groupWeight :: String -> Int
groupWeight name = maybe 1 id (lookup name weights)
  where
    weights =
        [ ("testParse", 1)
        , ("testParseEval", 1)
        , ("testValidateWithExpectedMatch", 1)
        , ("testValidateWithExpectedMismatch", 1)
        , ("testValidationFail", 1)
        , ("testValidationCache", 2)
        , ("testHaskellParity", 1)
        , ("testUserRewriteValidation", 1)
        , ("testParseVal", 1)
        , ("testParseValFail", 1)
        , ("testCrashRegression", 1)
        , ("testExamples", 10)
        , ("testCli", 1)
        , ("testMir", 1)
        , ("testMirSelfHosted:1/4", 47)
        , ("testMirSelfHosted:2/4", 43)
        , ("testMirSelfHosted:3/4", 79)
        , ("testMirSelfHosted:4/4", 32)
        , ("testIntRange", 1)
        , ("testPipeline", 1)
        , ("testControlFlow", 2)
        , ("testLists", 2)
        , ("testForallSyntax", 1)
        , ("testForallInstantiation", 1)
        , ("testForallProof", 1)
        , ("testForallLoops", 2)
        , ("testPrettyProofs", 1)
        , ("testMulDivNegative", 1)
        , ("testCrlf", 1)
        , ("testEnumCast", 1)
        , ("testListProofs", 1)
        , ("testEqualityByParts", 1)
        , ("testEnums", 2)
        , ("testStructs", 1)
        , ("testGenericLists", 1)
        , ("testTypeCheck", 1)
        , ("testRecursion", 1)
        , ("testSolverCache", 1)
        , ("testTermination", 2)
        , ("testRefinedArithmetic", 1)
        , ("testLinearArithmetic", 2)
        , ("testIfJoin", 1)
        , ("testModulo", 1)
        , ("testCallsAndReturnJoin", 1)
        , ("testForLoops", 2)
        , ("testInferredInvariants", 3)
        , ("testCfgValidation", 3)
        , ("testPrecedence", 1)
        , ("testFirstLast", 1)
        , ("testFunctionCalls", 1)
        , ("testCallsUseContracts", 1)
        , ("testNative:1/4", 58)
        , ("testNative:2/4", 55)
        , ("testNative:3/4", 54)
        , ("testNative:4/4", 57)
        , ("testOwnership", 222)
        , ("testTraits", 4)
        , ("testArrays", 3)
        , ("testBox", 2)
        , ("testDeref", 1)
        , ("testPointers", 6)
        , ("testBorrow", 2)
        , ("testCopies", 5)
        , ("testGenerics", 2)
        , ("testSequence", 5)
        , ("testStrings", 209)
        , ("testBytes", 1)
        , ("testConnectives", 1)
        , ("testMirData", 51)
        , ("testMirEvalLists", 1)
        , ("testMirReader", 58)
        , ("testMirVerify:1/4", 31)
        , ("testMirVerify:2/4", 33)
        , ("testMirVerify:3/4", 67)
        , ("testMirVerify:4/4", 73)
        , ("testMirErase", 65)
        , ("testMirVerifyPrograms", 49)
        , ("testMirEmit:1/4", 2)
        , ("testMirEmit:2/4", 58)
        , ("testMirEmit:3/4", 5)
        , ("testMirEmit:4/4", 109)
        , ("testMirEmitPrograms", 126)
        , ("testBootstrap", 248)
        , ("testFrontendBootstrap", 640)
        , ("testEq", 2)
        , ("testHashMap", 2)
        , ("testHashSet", 2)
        , ("testModules", 172)
        , ("testDataCodec", 199)
        , ("testBuiltinRegistry", 1)
        , ("testSharedCache", 190)
        , ("testVerdictLocks", 1)
        , ("testSharedCacheProbe", 1)
        , ("testScheduling", 16)
        , ("testAstData:1/4", 126)
        , ("testAstData:2/4", 219)
        , ("testAstData:3/4", 219)
        , ("testAstData:4/4", 12)
        , ("testParser:1/4", 62)
        , ("testParser:2/4", 39)
        , ("testParser:3/4", 187)
        , ("testParser:4/4", 203)
        , ("testParserBootstrap:1/2", 315)
        , ("testParserBootstrap:2/2", 265)
        , ("testParserUnicode", 8)
        , ("testAstReader:1/4", 300)
        , ("testAstReader:2/4", 220)
        , ("testAstReader:3/4", 34)
        , ("testAstReader:4/4", 9)
        , ("testDifferential", 10)
        , ("testParity", 170)
        , ("testLibModules", 5)
        , ("testNativeStorageModules", 201)
        , ("testMirSupport", 61)
        ]

groupName :: Test -> String
groupName (TestCase name _) = name
groupName (TestList name _) = name
groupName (TestParallel name _) = name

leafTests :: Test -> [Test]
leafTests test@TestCase{} = [test]
-- These cases overwrite and execute the same memory_limit file, so they must stay in one process.
leafTests test@(TestList "memory" _) = [test]
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
        path | "lib/mir/emit/emit.tersus" `elem` path || "lib/mir/mir_reader/mir_reader.tersus" `elem` path -> 30
        path | "the IR of a loop, interpreted" `elem` path || "raw lists and Boxes library" `elem` path -> 30
        path | "MIR loops" `elem` path -> 32
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
                    && (not worker || "using -N1" `isInfixOf` errors)
                    then Nothing
                    else Just ("unexpected worker routing: " ++ show (code, output, errors))

testScheduling :: [String] -> [(Test, [Test])] -> Test
testScheduling names batches = TestList "testScheduling"
    [ testCase "no flags preserve the full suite" $
        testAssertEq (parseArguments [] >>= (`selectGroupNames` names)) (Right names)
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
    , TestCase "explicit parallel single group uses one N1 worker with RTS statistics" $
        routingProbe ["-j", "4", "testSharedCacheProbe"] (Just 1) True True
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
    , testCase "seven CI shards reserve the last four for the bootstrap groups, one each" $
        let assigned = assignShards 7 names
         in testAssertTrue ([name | (name, shard) <- assigned, shard == 7] == ["testFrontendBootstrap"]
            && [name | (name, shard) <- assigned, shard == 6] == ["testBootstrap"]
            && [name | (name, shard) <- assigned, shard == 5] == ["testParserBootstrap:2/2"]
            && [name | (name, shard) <- assigned, shard == 4] == ["testParserBootstrap:1/2"]
            && [(name, shard) | (name, shard) <- assigned, name `notElem` bootstrapGroups]
                == assignShards 3 (filter (`notElem` bootstrapGroups) names))
    , testCase "seven-shard isolation retains aliases and filtered bootstrap selection" $
        testAssertTrue (all (\index ->
            selectGroupNames (Arguments Nothing ["testBootstrap"] False (Just (index, 7))) names
                == Right ["testBootstrap" | index == 6]
            && selectGroupNames (Arguments Nothing ["testParserBootstrap"] False (Just (index, 7))) names
                == Right (["testParserBootstrap:1/2" | index == 4] ++ ["testParserBootstrap:2/2" | index == 5])
            && selectGroupNames (Arguments Nothing ["testFrontendBootstrap"] False (Just (index, 7))) names
                == Right ["testFrontendBootstrap" | index == 7]
            && selectGroupNames (Arguments Nothing ["testNative"] False (Just (index, 7))) names
                == Right [name | name <- names, "testNative:" `isPrefixOf` name,
                    lookup name (assignShards 7 names) == Just index]) [1 .. 7])
    , testCase "bootstrap isolation is limited to seven shards and handles sparse inputs" $
        testAssertTrue
            ( assignShards 7 ["testBootstrap"] == [("testBootstrap", 6)]
              && assignShards 7 ["testParserBootstrap:2/2"] == [("testParserBootstrap:2/2", 5)]
              && assignShards 7 ["testParserBootstrap:1/2"] == [("testParserBootstrap:1/2", 4)]
              && assignShards 7 ["testFrontendBootstrap"] == [("testFrontendBootstrap", 7)]
              && assignShards 7 ["testParserBootstrap:2/2", "newA", "newB", "newC", "newD", "newE"]
                  == [("newA", 1), ("newB", 2), ("newC", 3), ("newD", 4), ("newE", 6), ("testParserBootstrap:2/2", 5)]
              && assignShards 7 ["testBootstrap", "testParserBootstrap:1/2", "testParserBootstrap:2/2"]
                  == [("testParserBootstrap:1/2", 4), ("testParserBootstrap:2/2", 5), ("testBootstrap", 6)]
              && assignShards 7 ["newA", "newB"] == [("newA", 1), ("newB", 2)]
              && assignShards 1 ["testBootstrap", "newA"] == [("testBootstrap", 1), ("newA", 1)]
              && sort (map snd (assignShards 2 ["testBootstrap", "newA"])) == [1, 2]
              && null (assignShards 0 ["testBootstrap"])
              && null (assignShards 7 []))
    , testCase "examples and strings remain unbatched to avoid duplicate cold startup" $
        testAssertTrue (all (`elem` names) ["testExamples", "testStrings"]
            && not (any (\name -> "testExamples:" `isPrefixOf` name || "testStrings:" `isPrefixOf` name) names))
    , testCase "empty groups and invalid partition counts are safe" $
        testAssertTrue (null (assignShards 3 []) && null (assignShards 0 names) && null (assignShards (-1) names))
    , testCase "unprofiled groups are retained and ties are deterministic" $
        testAssertEq (assignShards 2 ["newA", "newB", "newC"]) [("newA", 1), ("newC", 1), ("newB", 2)]
    , testCase "largest measured registered groups are spread before small groups" $
        testAssertEq (assignShards 3 ["testNative:1/4", "testMirVerify:1/4", "testMirEmit:1/4", "testBootstrap"])
            [("testBootstrap", 1), ("testNative:1/4", 2), ("testMirVerify:1/4", 3), ("testMirEmit:1/4", 3)]
    , testCase "three shard estimated loads differ by at most one short group" $
        testAssertTrue (maximum loads - minimum loads <= 11)
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
                        "testAstData" -> "whole parsed and elaborated source corpus"
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
    , testCase "parser bootstrap launch weights retain measured cold and warm paired frontiers" $
        testAssertEq (map (groupWeight . groupName) parserBootstrapGroups) [315,265]
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
                ++ map groupWeight ["testParity", "testMirData", "testOwnership", "testSharedCache", "testModules", "testMirEmitPrograms"]
                ++ map (groupWeight . groupName) parserBootstrapGroups)
            && all (> 0) (map groupWeight names)
            && maximum loads - minimum loads <= 11)
    , testCase "batch launch weights retain measured warm work without dividing again" $
        testAssertEq
            [map (groupWeight . groupName) split | (original, split) <- batches,
                groupName original `elem` ["testNative", "testMirEmit", "testMirVerify"]]
            [[58,55,54,57], [2,58,5,109], [31,33,67,73]]
    , testCase "AST and parser launch weights use actual whole-batch measurements" $
        testAssertEq
            [map (groupWeight . groupName) split | (original, split) <- batches,
                groupName original `elem` ["testAstData", "testParser"]]
            [[126,219,219,12], [62,39,187,203]]
    , testCase "AST reader launch weights retain actual whole-batch measurements" $
        testAssertEq [map (groupWeight . groupName) split | (original, split) <- batches,
            groupName original == "testAstReader"] [[300,220,34,9]]
    , testCase "measured tail groups are not launched as unprofiled one-second work" $
        testAssertEq (map groupWeight ["testAstReader:1/4", "testParity", "testMirData", "testOwnership", "testSharedCache", "testModules", "testMirEmitPrograms", "testParserBootstrap:2/2"])
            [300,170,51,222,190,172,126,265]
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
            [("products", 225), ("relations", 19), ("entailment cache", 2), ("execution", 55), ("driver", 54),
             ("MIR contracts", 60), ("MIR arithmetic", 22), ("MIR sequences", 32), ("MIR data", 21),
             ("MIR list updates", 19), ("MIR branches", 14), ("MIR loops", 22), ("bridges", 18),
             ("join hull", 35), ("loop candidate provenance", 6)]
    , testCase "self-hosted cache-sharing batches belong to one shard for every count" $
        testAssertTrue (all (\count ->
            length (unique [index | (name, index) <- assignShards count names, isSelfHosted name]) == 1)
            [1 .. length names + 1])
    , testCase "other original groups remain individually shardable" $
        testAssertEq (map snd (assignShards 4 ["testNative:1/4", "testNative:2/4", "testNative:3/4", "testNative:4/4"]))
            [1,2,3,4]
    , testCase "self-hosted cold launch cost is charged once, not per batch" $
        let selfHosted = filter isSelfHosted names
         in testAssertEq (shardWeight selfHosted) (maximum (map groupWeight selfHosted))
    , testCase "fixed native memory_limit users stay ordered in one batch" $
        testAssertTrue (all memorySerial batches)
    , testCase "small and empty trees never create empty batches" $
        testAssertTrue (null (splitTestGroups 4 (TestList "empty" []))
            && map groupName (splitTestGroups 4 (testCase "single" Nothing)) == ["single:1/1"])
    ]
  where
    assignments = assignShards 3 names
    loads = [shardWeight [name | (name, assigned) <- assignments, assigned == index] | index <- [1 .. 3]]
    complete count =
        let assigned = assignShards count names
            selected = [selectGroupNames (Arguments Nothing [] False (Just (index, count))) names | index <- [1 .. count]]
         in sort (map fst assigned) == sort names
            && all (\(_, index) -> index >= 1 && index <= count) assigned
            && fmap (sort . concat) (sequence selected) == Right (sort names)
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
                lookup (groupName batch) (assignShards 4 names) == Just index]
    memorySerial (original, split) =
        let originalPaths = filter (elem "memory") (leafPaths original)
            holders = [filter (elem "memory") (map (drop 1) (leafPaths batch)) | batch <- split]
         in null originalPaths || filter (not . null) holders == [originalPaths]
    unique :: Eq a => [a] -> [a]
    unique = foldl' (\seen name -> if name `elem` seen then seen else name : seen) []
    invalidShards = ["", "1", "0/3", "1/0", "4/3", "-1/3", "1/-3", "1/3/2", "1//3", "/3", "1/", "one/3", "1/three", "1.0/3", " 1/3", "1/3 ", "1/+3", show (toInteger (maxBound :: Int) + 1) ++ "/3", "1/" ++ show (toInteger (maxBound :: Int) + 1)]
    isLeft (Left _) = True
    isLeft (Right _) = False

bootstrapGroups :: [String]
bootstrapGroups = ["testBootstrap", "testParserBootstrap:1/2", "testParserBootstrap:2/2", "testFrontendBootstrap"]
