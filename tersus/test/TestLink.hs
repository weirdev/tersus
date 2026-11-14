module TestLink (testLink, linkProbeProgram, probeSource) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Mir as M
import MirData (readLowered, writeLowered)
import MirEval (RunEnv (..), Outcome (..), runProgramEnv)
import ElaboratorTool (bootstrapLoader)
import LibPackage (libPackage)
import PackageCompile (compileModulesUsing, lowerCompiledPackage)
import PackageData (Snapshot (..), resolverFromFiles)
import PreludeSource (toolPackageFiles)
import TestHarness
import Utils

probeSource :: String
probeSource = unlines
    [ "import data::reader::reader { readRecords, tokenizeStrict };"
    , "import mir::full::full { fullAt, printFull };"
    , "r = readRecords(0 - 1); if !r.ok { return 1; };"
    , "rows = []; for line in &r.value { ts = tokenizeStrict(line); if !ts.ok { return 1; }; rows = push(rows, ts.value); };"
    , "p = fullAt(&rows); if !p.ok { return 1; }; printFull(&p.value);"
    ]

linkProbeProgram :: Result M.Program String
linkProbeProgram = compileModulesUsing bootstrapLoader libPackage (Snapshot (resolverFromFiles files) "lib/probe/driver.tersus" False) `bindResult` lowerCompiledPackage
  where
    files = toolPackageFiles ++ [("lib/probe/package.tersus", ""), ("lib/probe/driver.tersus", probeSource)]

asUnit :: M.Program -> M.Lowered
asUnit p = M.Lowered p Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty []

roundTrip :: M.Program -> TestResult
roundTrip original = writeLowered (asUnit original) `eitherResult` \input ->
    linkProbeProgram `eitherResult` \tool ->
        runProgramEnv RunEnv{envArgs = [], envInput = input, envFile = const Nothing} tool `eitherResult` \out ->
            readLowered (outStdout out) `eitherResult` \back -> firstFailure
                [ testAssertEq (M.lowProgram back) original
                , testAssertEq (show (M.lowProgram back)) (show original)
                , testAssertEq (writeLowered back) (Ok input)
                ]

firstFailure :: [TestResult] -> TestResult
firstFailure [] = Nothing
firstFailure (Just e : _) = Just e
firstFailure (Nothing : rest) = firstFailure rest

eitherResult :: Result a String -> (a -> TestResult) -> TestResult
eitherResult (Error e) _ = Just e
eitherResult (Ok a) f = f a

empty :: M.Program
empty = M.Program Map.empty Map.empty mainFn Map.empty Map.empty Map.empty Map.empty
  where
    mainFn = M.Function "" [] Nothing Map.empty (Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)) [] [] [] [] [] M.emptySpec

testLink :: Test
testLink = TestList "testLink"
    [ testCase "full MIR3 common reader/writer compiles" $ linkProbeProgram `eitherResult` (const Nothing)
    , testCase "empty full MIR3 round trip" (roundTrip empty)
    ]
