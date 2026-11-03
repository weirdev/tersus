module TestScheduling
    ( Arguments (..)
    , parseArguments
    , selectGroupNames
    , assignShards
    , groupWeight
    , splitTestGroups
    , groupName
    , leafPaths
    , testScheduling
    ) where

import Control.Exception (evaluate)
import Data.Char (isDigit)
import Data.IORef (modifyIORef', newIORef, readIORef)
import Data.List (delete, foldl', isPrefixOf, minimumBy, sort, sortBy)
import Data.Ord (comparing)
import System.Mem.StableName (makeStableName)
import TestHarness (Test (..), TestResult, testAssertEq, testAssertTrue, testCase)
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

assignShards :: Int -> [String] -> [(String, Int)]
assignShards count names
    | count <= 0 = []
    | otherwise = [(name, index) | (_, index, assigned) <- balance bins, unit <- reverse assigned, name <- unit]
  where
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

-- Run 41687475071 (2026-11-03): each batch time includes its cold dependencies and contention.
groupWeight :: String -> Int
groupWeight name = maybe 1 id (lookup name weights)
  where
    weights =
        [("testMirSelfHosted:" ++ show index ++ "/4", weight)
            | (index, weight) <- zip [1 :: Int ..] [31, 544, 124, 52]]
        ++ [(original ++ ":" ++ show index ++ "/4", weight)
            | (original, work) <-
                [("testMirEmit", [408, 671, 566, 374]),
                 ("testMirVerify", [373, 687, 627, 673]),
                 ("testNative", [512, 704, 476, 471])],
              (index, weight) <- zip [1 :: Int ..] work]
        ++ [ ("testBootstrap", 296)
           , ("testMir", 437)
           , ("testMirErase", 285)
           , ("testExamples", 236)
           , ("testStrings", 395)
           , ("testMirReader", 278)
           , ("testAstReader", 274)
           , ("testParity", 215)
           , ("testAstData", 50)
           , ("testOwnership", 47)
           , ("testMirData", 171)
           , ("testMirEmitPrograms", 10)
           , ("testCopies", 7)
           , ("testSequence", 8)
           , ("testMirVerifyPrograms", 5)
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
        path | "examples/mir/emit/emit.tersus" `elem` path || "examples/mir/mir_reader/mir_reader.tersus" `elem` path -> 30
        path | "the IR of a loop, interpreted" `elem` path || "raw lists and Boxes library" `elem` path -> 30
        path | "MIR loops" `elem` path -> 32
        path | "MIR branches" `elem` path -> 16
        path | any (`elem` path) ["MIR contracts", "MIR sequences", "MIR data", "MIR list updates"] -> 8
        path | "interpreted" `elem` path || "pre-erasure, interpreted" `elem` path
            || "function-list identity, interpreted" `elem` path || "call metadata, interpreted" `elem` path -> 5
        _ -> length (leafPaths test)

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
    , testCase "all registered group names are unique" $
        testAssertEq (length names) (length (unique names))
    , testCase "every group belongs to exactly one shard for every tested count" $
        testAssertTrue (all complete [1 .. length names + 1])
    , testCase "empty groups and invalid partition counts are safe" $
        testAssertTrue (null (assignShards 3 []) && null (assignShards 0 names) && null (assignShards (-1) names))
    , testCase "unprofiled groups are retained and ties are deterministic" $
        testAssertEq (assignShards 2 ["newA", "newB", "newC"]) [("newA", 1), ("newC", 1), ("newB", 2)]
    , testCase "largest measured registered groups are spread before small groups" $
        testAssertEq (assignShards 3 ["testNative:1/4", "testMirVerify:1/4", "testMirEmit:1/4", "testBootstrap"])
            [("testNative:1/4", 1), ("testMirEmit:1/4", 2), ("testMirVerify:1/4", 3), ("testBootstrap", 3)]
    , testCase "three shard estimated loads differ by at most one short group" $
        testAssertTrue (maximum loads - minimum loads <= 11)
    , testCase "CLI and cold bootstrap are covered exactly once" $
        testAssertTrue (all (\name -> length (filter ((== name) . fst) assignments) == 1)
            ["testCli", "testBootstrap"])
    , testCase "explicit filters intersect the full-suite shard assignment" $
        testAssertTrue (all filtered [1 .. 3])
    , testCase "unknown explicit groups fail even on an empty shard" $
        testAssertTrue (isLeft (selectGroupNames (Arguments Nothing ["noSuchGroup"] False (Just (99, 99))) names))
    , testCase "huge valid shard counts do not allocate one bin per empty shard" $
        testAssertEq (selectGroupNames (Arguments Nothing [] False (Just (maxBound, maxBound))) names) (Right [])
    , testCase "all old leaf paths occur exactly once in the registered batches" $
        testAssertTrue (all (\(original, split) ->
            sort (leafPaths original) == sort (concatMap (map (drop 1) . leafPaths) split)) batches)
    , TestCase "batches keep the original case action objects" $ do
        preserved <- mapM sameActions batches
        pure (testAssertTrue (and preserved))
    , testCase "each expensive group has four nonempty registered batches and no original duplicate" $
        testAssertTrue (all (\(original, split) -> length split == 4
            && groupName original `notElem` names
            && all (\batch -> groupName batch `elem` names && not (null (leafPaths batch))) split) batches)
    , testCase "batch launch weights retain measured cold costs without dividing again" $
        testAssertEq
            [map (groupWeight . groupName) split | (original, split) <- batches,
                groupName original `elem` ["testNative", "testMirEmit", "testMirVerify"]]
            [[512,704,476,471], [408,671,566,374], [373,687,627,673]]
    , testCase "measured tail groups are not launched as unprofiled one-second work" $
        testAssertEq (map groupWeight ["testAstReader", "testParity", "testMirData", "testStrings"])
            [274,215,171,395]
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
        let leaf index = TestCase "duplicate label" (modifyIORef' seen (index :) >> pure Nothing)
            fixture = TestList "root" [TestParallel "parallel" [leaf 1, leaf 2], TestList "fixed" [leaf 3, leaf 4]]
            split = splitTestGroups 4 fixture
        results <- mapM snd (concatMap leafActions split)
        executed <- readIORef seen
        pure (testAssertTrue (sort executed == [1,2,3,4]
            && results == replicate 4 Nothing
            && sort (leafPaths fixture) == sort (concatMap (map (drop 1) . leafPaths) split)))
    , testCase "all 1564 self-hosted query assertions remain in their families" $
        testAssertEq selfHostedFamilyManifest
            [("equality graphs", 1056), ("products", 225), ("relations", 68), ("execution", 23),
             ("MIR contracts", 41), ("MIR arithmetic", 22), ("MIR sequences", 32), ("MIR data", 21),
             ("MIR list updates", 19), ("MIR branches", 14), ("MIR loops", 21), ("bridges", 22)]
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
    sameActions (original, split) = do
        before <- identities (leafActions original)
        after <- identities [(drop 1 path, action) | batch <- split, (path, action) <- leafActions batch]
        pure (length before == length after && null (foldl' (flip delete) after before))
    identities = mapM (\(path, action) -> do
        stable <- evaluate action >>= makeStableName
        pure (path, stable))
    unique :: Eq a => [a] -> [a]
    unique = foldl' (\seen name -> if name `elem` seen then seen else name : seen) []
    invalidShards = ["", "1", "0/3", "1/0", "4/3", "-1/3", "1/-3", "1/3/2", "1//3", "/3", "1/", "one/3", "1/three", "1.0/3", " 1/3", "1/3 ", "1/+3", show (toInteger (maxBound :: Int) + 1) ++ "/3", "1/" ++ show (toInteger (maxBound :: Int) + 1)]
    isLeft (Left _) = True
    isLeft (Right _) = False
