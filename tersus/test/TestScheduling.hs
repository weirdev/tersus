module TestScheduling
    ( Arguments (..)
    , parseArguments
    , selectGroupNames
    , assignShards
    , groupWeight
    , testScheduling
    ) where

import Data.Char (isDigit)
import Data.List (foldl', isPrefixOf, minimumBy, sort, sortBy)
import Data.Ord (comparing)
import TestHarness (Test (..), testAssertEq, testAssertTrue, testCase)

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
    unknown = [name | name <- chosen, name `notElem` names]
    requested name = null chosen || name `elem` chosen
    assignments = case argumentShard arguments of
        Nothing -> []
        Just (_, count) -> assignShards count names
    inShard name = case argumentShard arguments of
        Nothing -> True
        Just (index, _) -> lookup name assignments == Just index

assignShards :: Int -> [String] -> [(String, Int)]
assignShards count names
    | count <= 0 = []
    | otherwise = [(name, index) | (_, index, assigned) <- bins, name <- reverse assigned]
  where
    bins = foldl' assign [(0, index, []) | index <- [1 .. min count (length names)]]
        (sortBy (comparing (negate . groupWeight)) names)
    assign shards name =
        let (_, target, _) = minimumBy (comparing (\(weight, index, _) -> (weight, index))) shards
         in [if index == target then (weight + groupWeight name, index, name : assigned) else shard
            | shard@(weight, index, assigned) <- shards]

-- Seconds from the full cold four-core run on 2026-11-02; unprofiled groups still run, with weight 1.
groupWeight :: String -> Int
groupWeight name = case lookup name weights of
    Just weight -> weight
    Nothing -> 1
  where
    weights =
        [ ("testMirEmit", 643)
        , ("testMirVerify", 584)
        , ("testNative", 506)
        , ("testBootstrap", 448)
        , ("testMir", 298)
        , ("testMirSelfHosted", 267)
        , ("testMirErase", 141)
        , ("testExamples", 119)
        , ("testStrings", 72)
        , ("testMirReader", 49)
        , ("testOwnership", 11)
        , ("testMirData", 9)
        , ("testMirEmitPrograms", 8)
        , ("testCopies", 5)
        , ("testSequence", 4)
        , ("testMirVerifyPrograms", 2)
        ]

testScheduling :: [String] -> Test
testScheduling names = TestList "testScheduling"
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
    , testCase "largest measured groups are spread before small groups" $
        testAssertEq (assignShards 3 ["testNative", "testMirVerify", "testMirEmit", "testBootstrap"])
            [("testMirEmit", 1), ("testMirVerify", 2), ("testNative", 3), ("testBootstrap", 3)]
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
    ]
  where
    assignments = assignShards 3 names
    loads = [sum [groupWeight name | (name, assigned) <- assignments, assigned == index] | index <- [1 .. 3]]
    complete count =
        let assigned = assignShards count names
            selected = [selectGroupNames (Arguments Nothing [] False (Just (index, count))) names | index <- [1 .. count]]
         in sort (map fst assigned) == sort names
            && all (\(_, index) -> index >= 1 && index <= count) assigned
            && fmap (sort . concat) (sequence selected) == Right (sort names)
    filtered index =
        let chosen = ["testCli", "testBootstrap", "testMirEmit"]
         in selectGroupNames (Arguments Nothing chosen False (Just (index, 3))) names
            == Right [name | name <- names, name `elem` chosen, lookup name assignments == Just index]
    unique = foldl' (\seen name -> if name `elem` seen then seen else name : seen) []
    invalidShards = ["", "1", "0/3", "1/0", "4/3", "-1/3", "1/-3", "1/3/2", "1//3", "/3", "1/", "one/3", "1/three", "1.0/3", " 1/3", "1/3 ", "1/+3", show (toInteger (maxBound :: Int) + 1) ++ "/3", "1/" ++ show (toInteger (maxBound :: Int) + 1)]
    isLeft (Left _) = True
    isLeft (Right _) = False
