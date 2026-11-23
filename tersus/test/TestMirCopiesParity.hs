module TestMirCopiesParity
    ( testMirCopiesParity, testMirCopyKeys, nativeCopiesProbe, witnessSource, packSource, sourceUnits, checkWitness, compareProgram
    , testFncReview, testStandaloneFnc, standaloneFncLowered, standaloneFncExpected, standaloneFncLegacyInput
    , testMirCopiesDivergence, divergenceProgram, checkDivergence
    , empty, int, block, function, bounded, template, rootId, recursion, growthRefusal, wideStatements, checkWideStatements
    ) where

import Control.Concurrent.MVar (MVar, newMVar)
import Data.Char (chr, isAlphaNum, isLower, isUpper)
import Data.List (find, intercalate, isInfixOf, isPrefixOf, sort, stripPrefix)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Directory (listDirectory)
import System.Exit (ExitCode (..))
import System.FilePath (takeExtension, (</>))
import System.IO.Unsafe (unsafePerformIO)

import qualified Compile
import DataCodec (argTokens, quote, sizeTokens, typeTokens)
import ElaboratorTool (bootstrapLoader)
import LibPackage (libPackage)
import qualified Link
import Lowering (finishProgramWith)
import qualified Mir as M
import MirCopiesNameProfile (nameProfilePrefix)
import MirCopiesOracle (coveredKey, genericKey, makeCopiesWith)
import MirData (readLowered, writeProgram)
import qualified MirHousekeeping as Housekeeping
import MirMoves (finishLowered)
import MirPass (programData, runPassWith)
import qualified Native
import PackageCompile (compileModulesUsing, lowerCompiledPackage, packageLinkInputs)
import PackageData (ModuleId (..), Snapshot (..), resolverFromFiles)
import PreludeSource (toolPackageFiles)
import Seed (cachedSeed, compilerSnapshotHash)
import qualified Syntax as S
import TestHarness
import Types (Arg (..), FnClause (..), FnClauseToken (..), FnContract (..), Size (..), Type (..), instanceName, renderTypeForName, substitute)
import Utils

{-# NOINLINE probeCache #-}
probeCache :: MVar (Maybe FilePath)
probeCache = unsafePerformIO (newMVar Nothing)

nativeCopiesProbe :: IO (Result FilePath String)
nativeCopiesProbe = memoizedTestExecutable probeCache $ do
    sources <- mirSources ["copies", "pack", "instances", "link"]
    copies <- readFile "dev/mir-copies/probe.tersus"
    audit <- readFile "dev/mir-copies-fused/audit.tersus"
    link <- readFile "dev/mir-copies-fused/driver.tersus"
    emitter <- readFile "lib/mir/emit/emit.tersus"
    let auditRequest = case lookup "lib/mir/link/link.tersus" sources of
            Just production -> mergeAuditRequest production
            Nothing -> Error "missing production link.tersus"
    case (auditRequest, emitterInput link emitter) of
        (Ok request, Ok driver) -> buildProbe (sources ++
            [ ("lib/copiesprobe/package.tersus", "")
            , ("lib/copiesprobe/profile/reader.tersus", profileReader)
            , ("lib/copiesprobe/copies.tersus", copies)
            , ("lib/copiesprobe/link.tersus", driver)
            , ("lib/copiesprobe/audit.tersus", audit)
            , ("lib/copiesprobe/auditRequest.tersus", request)
            , ("lib/copiesprobe/pack.tersus", packProbeSource)
            , ("lib/copiesprobe/keys.tersus", keyProbeSource)
            , (probeEntry, probeDriver)
            ])
        (Error e, _) -> pure (Error e)
        (_, Error e) -> pure (Error e)

probeEntry :: FilePath
probeEntry = "lib/copiesprobe/driver.tersus"

probeDriver :: String
probeDriver = unlines
    [ "import data::reader::reader { readRecord };"
    , "import copiesprobe::copies { runCopiesProbe };"
    , "import copiesprobe::link { runLinkProbe };"
    , "import copiesprobe::pack { runPackProbe };"
    , "import copiesprobe::keys { keyProbe };"
    , "mode = readRecord(); if !mode.ok { return 2; };"
    , "status = 2;"
    , "if mode.value = \"copies\" { status = runCopiesProbe(); };"
    , "if mode.value = \"link\" { status = runLinkProbe(); };"
    , "if mode.value = \"pack\" { status = runPackProbe(); };"
    , "if mode.value = \"keys\" { status = keyProbe(); };"
    , "if status != 0 { return status; };"
    ]

mirSources :: [FilePath] -> IO [(FilePath, String)]
mirSources = fmap concat . mapM (sourcesIn . ("lib/mir" </>))
  where
    sourcesIn dir = do
        files <- listDirectory dir
        mapM (sourceFile . (dir </>)) [file | file <- sort files, takeExtension file == ".tersus"]

sourceFile :: FilePath -> IO (FilePath, String)
sourceFile path = (,) path <$> readFile path

mountSources :: [(FilePath, String)] -> [(FilePath, String)] -> [(FilePath, String)]
mountSources mounted files = filter ((`notElem` map fst mounted) . fst) files ++ mounted

hostNameProfile :: String
hostNameProfile = unlines (("name-classes " ++ show (length ranges)) : map row ranges)
  where
    ranges = go 128
    limit = 0x10ffff
    mask i = let c = chr i in fromEnum (isUpper c) + 2 * fromEnum (isLower c) + 4 * fromEnum (isAlphaNum c)
    go lo
        | lo > limit = []
        | k == 0 = go (lo + 1)
        | otherwise = (lo, hi, k) : go (hi + 1)
      where
        k = mask lo
        hi = end lo
        end i | i < limit && mask (i + 1) == k = end (i + 1)
              | otherwise = i
    row (lo, hi, k) = unwords [show lo, show hi, show k]

profileReader :: String
profileReader = unlines
    [ "import data::reader::reader { tokenizeMir };"
    , "import mir::full::tokens { integerAt, wordIs };"
    , "import mir::instances::names { InstanceNameClasses, InstanceNameRange };"
    , "struct ProbeNameProfile { classes: InstanceNameClasses, end: Int, ok: Bool };"
    , "fn badNameProfile() -> ProbeNameProfile ~ { return ProbeNameProfile { classes: InstanceNameClasses { ranges: [], pinned: false }, end: 0, ok: false }; };"
    , "fn readNameProfile(lines: &List<String>) -> ProbeNameProfile ~ {"
    , "    if size(lines) = 0 { return badNameProfile(); };"
    , "    header = tokenizeMir(get(lines, 0)); ns = integerAt(&header.value, 1);"
    , "    if !header.ok || !wordIs(&header.value, 0, \"name-classes\") || size(header.value) != 2 || !ns.ok || ns.value < 0 || ns.value >= size(lines) { return badNameProfile(); };"
    , "    ranges = []; prev = 127; end = 1 + ns.value;"
    , "    for i in 1..end {"
    , "        row = tokenizeMir(get(lines, i)); lo = integerAt(&row.value, 0); hi = integerAt(&row.value, 1); mask = integerAt(&row.value, 2);"
    , "        if !row.ok || size(row.value) != 3 || !lo.ok || !hi.ok || !mask.ok || lo.value <= prev || hi.value < lo.value || hi.value > 1114111 || mask.value < 1 || mask.value > 7 { return badNameProfile(); };"
    , "        ranges = push(ranges, InstanceNameRange { lo: lo.value, hi: hi.value, mask: mask.value }); prev = hi.value;"
    , "    };"
    , "    return ProbeNameProfile { classes: InstanceNameClasses { ranges: ranges, pinned: false }, end: end, ok: true };"
    , "};"
    ]

buildProbe :: [(FilePath, String)] -> IO (Result FilePath String)
buildProbe mounted = do
    key <- nativeCacheKey [Housekeeping.ownedContentKey compilerSnapshotHash (show files) []]
    case key of
        Error e -> pure (Error e)
        Ok complete -> Native.cachedProgram "mir-copies-probe" complete "the MIR copies and pack test tool" build
  where
    files = mountSources mounted toolPackageFiles
    snapshot = Snapshot (resolverFromFiles files) probeEntry False
    source = compileModulesUsing bootstrapLoader libPackage snapshot `bindResult` lowerCompiledPackage
    build output = do
        seed <- cachedSeed
        case (seed, source) of
            (Error e, _) -> pure (Error e)
            (_, Error e) -> pure (Error e)
            (Ok emitter, Ok program) -> do
                owned <- Housekeeping.ownedWith emitter program
                case owned of
                    Error e -> pure (Error e)
                    Ok lowered -> do
                        ir <- Native.runWithInput emitter (writeProgram lowered)
                        case ir of
                            Error e -> pure (Error e)
                            Ok llvm -> Native.buildExecutable output llvm

-- Inspect the merged program before printFull can canonicalize it, without changing runLink.
mergeAuditRequest :: String -> Result String String
mergeAuditRequest source = case dropWhile (/= signature) (lines source) of
    _ : body -> case break (== "};") body of
        (handler, _ : _) -> case break (== copiesBranch) handler of
            (parser, suffix) | suffix == productionSuffix -> Ok (unlines (imports ++ [auditSignature] ++ parser ++ auditSuffix))
            _ -> bad
        _ -> bad
    _ -> bad
  where
    signature = "fn mergeRequest(lines: &List<List<Token>>, copies: Bool) -> Bool ~ {"
    copiesBranch = "    if copies {"
    productionSuffix =
        [ copiesBranch
        , "        problem = runFusedUnits(lines, at, &units);"
        , "        if problem != \"\" { return linkError(&problem); };"
        , "        return true;"
        , "    };"
        , "    if at != size(lines) { return linkError(\"the linking request has trailing data\"); };"
        , linkUnits
        , "    printFull(&linked.program); return true;"
        ]
    linkUnits = "    linked = linkPrograms(&units); if !linked.ok { return linkError(&linked.message); };"
    imports =
        [ "import data::codec::codec { Token };"
        , "import mir::full::full { fullAt };"
        , "import mir::full::tokens { integerAt, textAt, wordIs, quotedAt };"
        , "import mir::full::read { recordAt };"
        , "import mir::link::link { takeRows, linkError };"
        , "import mir::link::merge { LinkUnit, linkPrograms };"
        , "import copiesprobe::audit { auditMerge };"
        ]
    auditSignature = "fn inspectMerge(lines: &List<List<Token>>) -> Bool ~ {"
    auditSuffix =
        [ linkUnits
        , "    problem = auditMerge(lines, at, linked.program);"
        , "    if problem != \"\" { return linkError(&problem); };"
        , "    return true;"
        , "};"
        ]
    bad = Error "the production Link merge handler no longer matches the dev audit"

emitterInput :: String -> String -> Result String String
emitterInput driver source = case (break (== "fn runLinkProbe() -> Int ~ {") (lines driver), dropWhile (not . starts) (lines source)) of
    ((imports, body@(_ : _)), reader@(_ : _)) -> case break (== "};") reader of
        (definition, closer : _) -> Ok (unlines (imports ++ definition ++ closer : body))
        _ -> bad
    _ -> bad
  where
    starts = maybe False (const True) . stripPrefix "fn readEmitterInput()"
    bad = Error "the production emitter input reader no longer matches the dev overlay"

packProbeSource :: String
packProbeSource = unlines
    [ "import data::codec::codec { Token };"
    , "import data::reader::reader { readRecords, tokenizeMir };"
    , "import mir::full::full { FullBlock, FullRecord, FullFunction, FullProgram, fullAt, printFull };"
    , "import mir::full::environments { resolveEnv };"
    , "import mir::full::records { envEntries, replaceEnv };"
    , "import mir::full::tokens { integerAt, intToken, name, textAt, tokenLine, word };"
    , "import mir::link::merge { fnIndex, rowIndex };"
    , "import mir::pack::body { PackSpread };"
    , "import mir::pack::expand { expandPack };"
    , "fn inlineFunction(fun: FullFunction, shared: &List<List<Token>>) -> FullFunction ~ {"
    , "    loops = []; for l in &fun.loops { loops = push(loops, FullRecord { name: clone(l.name), tokens: replaceEnv(&l.tokens, resolveEnv(&l.tokens, shared)) }); };"
    , "    blocks = []; for b in &fun.blocks {"
    , "        rows = []; for r in &b.lines { rows = push(rows, replaceEnv(r, resolveEnv(r, shared))); };"
    , "        blocks = push(blocks, FullBlock { lines: rows, ..b });"
    , "    };"
    , "    return FullFunction { env: replaceEnv(&fun.env, resolveEnv(&fun.env, shared)), loops: loops, blocks: blocks, ..fun };"
    , "};"
    , "fn printRecord(row: &List<Token>) -> Int ~ { tokenLine(row).print(); return \"\\n\".print(); };"
    , "fn printIndexes(tag: &String, indexes: &HashMap<Int, HashMap<String, String>>) -> Int ~ {"
    , "    for group in indexes.entries() {"
    , "        prefix = push(push([], word(clone(tag))), intToken(group.key)); printRecord(&prefix);"
    , "        for binding in group.value.entries() { printRecord(push(push(clone(prefix), name(clone(binding.key))), word(clone(binding.value)))); };"
    , "    }; return 0;"
    , "};"
    , "fn printSpreads(spreads: &HashMap<String, PackSpread>) -> Int ~ {"
    , "    for e in spreads.entries() {"
    , "        row = push(push(push([], word(\"spread\")), name(clone(e.key))), name(clone(e.value.callee)));"
    , "        printRecord(push(push(row, intToken(e.value.lo)), intToken(e.value.hi)));"
    , "    }; return 0;"
    , "};"
    , "fn runPackProbe() -> Int ~ {"
    , "    r = readRecords(0 - 1); if !r.ok || size(r.value) = 0 { return 2; };"
    , "    request = tokenizeMir(get(&r.value, 0)); if !request.ok || size(request.value) != 3 { return 2; };"
    , "    target = textAt(&request.value, 0); pack = textAt(&request.value, 1); count = integerAt(&request.value, 2);"
    , "    if !count.ok { return 2; };"
    , "    rows = []; for i in 1..size(r.value) { ts = tokenizeMir(get(&r.value, i)); if !ts.ok { return 2; }; rows = push(rows, ts.value); };"
    , "    parsed = fullAt(&rows); if !parsed.ok { \"pack probe could not read MIR3\\n\".printError(); return 2; };"
    , "    p = parsed.value; j = rowIndex(&p.bounded, &target); i = fnIndex(&p.functions, &target);"
    , "    if i < 0 || j < 0 { \"pack probe could not find the bounded function\\n\".printError(); return 2; };"
    , "    bounded = clone(get(&p.bounded, j)); fun = inlineFunction(clone(get(&p.functions, i)), &p.shared);"
    , "    expanded = expandPack(&bounded, &pack, count.value, fun, p.arena);"
    , "    if size(expanded.error.bytes) != 0 { expanded.error.printError(); \"\\n\".printError(); return 1; };"
    , "    printIndexes(\"block\", &expanded.blocks); printIndexes(\"local\", &expanded.locals); printSpreads(&expanded.spreads);"
    , "    ordered = push([], word(\"env-order\")); for e in envEntries(&expanded.fun.env, 1) { ordered = push(ordered, name(clone(e.name))); }; printRecord(&ordered);"
    , "    out = FullProgram { functions: set(p.functions, i, expanded.fun), arena: expanded.arena, ..p };"
    , "    printFull(&out); return 0;"
    , "};"
    ]

withResult :: Result a String -> (a -> IO TestResult) -> IO TestResult
withResult (Error e) _ = pure (Just e)
withResult (Ok a) f = f a

requestCopies :: String -> Set.Set String -> M.Program -> ((ExitCode, String, String) -> TestResult) -> IO TestResult
requestCopies mode library program check = withResult (programData program) $ \payload -> do
    tool <- nativeCopiesProbe
    withResult tool $ \executable -> do
        (code, out, err) <- Native.runWithInputFull executable ("copies\n" ++ hostNameProfile ++ unwords (mode : map quote (Set.toList library)) ++ "\n" ++ payload)
        pure (check (code, out, decodeUtf8 err))

compareCopies :: String -> Set.Set String -> M.Program -> Either String (M.Program -> TestResult) -> IO TestResult
compareCopies mode library input outcome = case (makeCopiesWith library referenceInput, outcome) of
    (Error expected, Left refusal) | expected == refusal ->
        requestCopies mode library input (\actual -> testAssertEq actual (ExitSuccess, "1\n", expected ++ "\n"))
    (Ok expected, Right nonVacuous) -> case nonVacuous expected of
        Just e -> pure (Just ("oracle fixture: " ++ e))
        Nothing -> requestCopies mode library input $ \(code, out, err) ->
            testAssertEq (code, err) (ExitSuccess, "") <|> compareProgram expected out
    (Error actual, Left refusal) -> pure (testAssertEq actual refusal)
    (Error e, Right _) -> pure (Just ("unexpected Haskell refusal: " ++ e))
    (Ok _, Left refusal) -> pure (Just ("Haskell accepted; expected " ++ refusal))
  where
    referenceInput = if mode == "linked" then M.completeInstances input else input

compareProgram :: M.Program -> String -> TestResult
compareProgram expected out = case readLowered out of
    Error e -> Just ("copies probe wrote unreadable MIR3: " ++ e ++ "; output starts " ++ take 120 out)
    Ok lowered ->
        let actual = M.lowProgram lowered in case (programData expected, programData actual) of
            (Ok want, Ok got) ->
                let rows = zip3 ([1 ..] :: [Int]) (map Just (lines want) ++ repeat Nothing) (map Just (lines got) ++ repeat Nothing)
                    differing = find (\(_, a, b) -> a /= b) (take (max (length (lines want)) (length (lines got))) rows)
                in case differing of
                    Just (i, a, b) -> Just ("canonical MIR3 line " ++ show i ++ ": expected " ++ show a ++ ", got " ++ show b)
                    Nothing -> testAssertTrue (expected == actual && show expected == show actual)
            (Error e, _) -> Just ("cannot encode Haskell result: " ++ e)
            (_, Error e) -> Just ("cannot encode native result: " ++ e)

(<|>) :: TestResult -> TestResult -> TestResult
Nothing <|> other = other
failure <|> _ = failure

oldMerge :: [(ModuleId, M.Program)] -> IO (Result M.Program String)
oldMerge = runOldMerge . oldMergeRequest

runOldMerge :: Result String String -> IO (Result M.Program String)
runOldMerge (Error e) = pure (Error e)
runOldMerge (Ok request) = runPassWith cachedSeed "the linker written in Tersus" request

oldMergeRequest :: [(ModuleId, M.Program)] -> Result String String
oldMergeRequest units = flatResultMap unitData units `bindResult` \parts ->
    Ok ("pass link\nmerge " ++ show (length units) ++ "\n" ++ concat parts)
  where
    unitData (modId, p) = mapResult (linkUnitData modId) (programData p)

linkUnitData :: ModuleId -> String -> String
linkUnitData (ModuleId pkg modu) text =
    unwords ["unit", quote pkg, maybe "none" (("some " ++) . quote) modu, show (length (lines text))] ++ "\n" ++ text

linkedCase :: Result [(ModuleId, M.Program)] String -> (Set.Set String -> M.Program -> TestResult) -> IO TestResult
linkedCase compiled check = withResult compiled $ \units -> do
    merged <- oldMerge units
    let library = Set.fromList [n | (ModuleId "tersuslib" _, p) <- units, n <- Map.keys (M.progBounded p)]
    withResult merged $ \input -> compareCopies "linked" library input (Right (check library))

sourceUnits :: String -> Result [(ModuleId, M.Program)] String
sourceUnits source = compiled `bindResult` packageLinkInputs `bindResult` (Ok . uncurry (++))
  where
    entry = "app/main.tersus"
    snapshot = Snapshot (resolverFromFiles [("app/package.tersus", ""), (entry, source)]) entry False
    compiled = compileModulesUsing bootstrapLoader libPackage snapshot

standalone :: Set.Set String -> Result M.Lowered String -> Either String (M.Program -> TestResult) -> IO TestResult
standalone library lowered expected = withResult (lowered `bindResult` finishLowered) $ \input -> compareCopies "copies" library input expected

asUnit :: M.Program -> M.Lowered
asUnit p = M.Lowered p Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty []

fromStatements :: String -> [S.Statement] -> Result M.Lowered String
fromStatements declarations statements = Compile.parseSourceParts True declarations `bindResult` \(_, library, body) ->
    Compile.elaborateStatements (library ++ body ++ statements)

testMirCopiesParity :: Test
testMirCopiesParity = TestList "testMirCopiesParity"
    [ TestCase "old decoded Link input: witness check, hidden size, lifted body and library retention" $
        linkedCase (sourceUnits witnessSource) checkWitness
    , TestCase "old decoded Link input: nested instance retains its permission field" $
        linkedCase (Ok [(rootId, permissionProgram)]) (const checkPermission)
    , TestCase "old decoded Link input: heterogeneous pack slice, loop and proof" $
        linkedCase (sourceUnits packSource) (\_ p -> case Map.lookup "forward[Int, Bool, Int]" (M.progFunctions p) of
            Just f -> testAssertEq (calls f) ["sink[Int, Bool, Int]"]
            Nothing -> Just "oracle fixture has no heterogeneous forward copy")
    , TestCase "standalone no-work leaves the program and does not force the library set" $
        standalone Set.empty plain (Right (\p -> testAssertEq noWork (Ok p)))
    , testMirCopiesDivergence
    , TestCase "standalone no-library retains the unused template" $
        standalone Set.empty (Ok (asUnit wideKeys)) (Right (checkWideKeys True))
    , TestCase "standalone explicit library retains only the used template; wide distinct sizes stay distinct" $
        standalone (Set.fromList ["sized", "unused"]) (Ok (asUnit wideKeys)) (Right (checkWideKeys False))
    , TestCase "standalone statement request retains an arbitrary runtime and proof integer"
        (standalone Set.empty wideStatements (Right checkWideStatements))
    , TestCase "same-key recursion deduplicates before the growth check and aliases are last-wins" $
        standalone Set.empty (Ok (asUnit (recursion False))) (Right checkRecursion)
    , TestCase "standalone move refusal wins over recursive copy growth" $
        pure moveBeforeCopies
    , TestCase "recursive growth is refused exactly" $
        standalone Set.empty (Ok (asUnit (recursion True))) (Left growthRefusal)
    , TestCase "frame word arithmetic does not wrap at 64 bits" $
        standalone Set.empty (Ok (asUnit frameProgram)) (Left frameRefusal)
    , TestCase "copy refusal is prefixed only after a successful merge" linkRefusals
    , TestCase "raw contract function type is accepted by Haskell but refused by the native Full reader" strictFnc
    ]
  where
    plain = Compile.elaborateStatements [S.Return (S.Val (S.VInt 7))]
    noWork = plain `bindResult` finishLowered `bindResult` Link.standaloneCopies (error "no-work forced its library")

testMirCopiesDivergence :: Test
testMirCopiesDivergence = TestList "testMirCopiesDivergence"
    [ TestCase "divergence propagates through a specialized bound call and transitively to its caller copy" $
        compareCopies "copies" Set.empty divergenceProgram (Right checkDivergence)
    , TestCase "no-work leaves even a copy-named caller of a divergent function unchanged" $
        compareCopies "copies" Set.empty divergenceNoWork (Right (\p -> testAssertEq p divergenceNoWork))
    ]

divergenceProgram :: M.Program
divergenceProgram = empty
    { M.progGenerics = Map.singleton "Holder" (["T"], [("value", t)])
    , M.progFunctions = Map.fromList [(M.fnName f, f) | f <- generics ++ [ordinary, guardCheck, acceptCallback]]
    , M.progBounded = Map.fromList [(M.fnName f, bounded) | f <- generics]
    , M.progInstances = Map.fromList
        [ ("outer[Holder<Int>]", ("outer", [ArgType (holder TInt)]))
        , ("boundAtT", ("throughBound", [ArgType t]))
        , ("implAtT", (stepImpl, [ArgType t]))
        , (stepImplInt, (stepImpl, [ArgType TInt]))
        , ("referenceOnly[Int]", ("referenceOnly", [ArgType TInt]))
        ]
    , M.progMain = start (M.progMain empty) [("referenceOnly[Int]", [])]
    }
  where
    t = TParam "T"
    holder ty = TNamed "Holder" [ArgType ty]
    arg = M.Local 1
    passed = [M.Move arg]
    withArg ty f = f{M.fnParams = [arg], M.fnLocals = Map.insert arg (M.LocalDecl ty Nothing) (M.fnLocals f)}
    start f prefix = started
        { M.fnLocals = Map.insert arg (M.LocalDecl (holder TInt) Nothing) (M.fnLocals started)
        , M.fnBlocks = Map.adjust initHolder (M.BlockId 0) (M.fnBlocks started)
        }
      where
        started = calling f (prefix ++ [("outer[Holder<Int>]", passed)])
        initHolder b = b{M.blockStatements = [M.Assign arg (M.MakeData (instanceName "Holder" [ArgType TInt]) [("value", int 0)])]}
    ordinary = start (function "ordinary") []
    guardCheck = start (function "Step for Holder::guard[Int]") []
    outer = withArg t (calling (template "outer") [("boundAtT", passed)])
    throughBound = withArg t (calling (template "throughBound") [("<$param T as Step>::step", passed)])
    witness = mayDiverge (withArg (holder t) (calling (template "Step for Holder::step") [("implAtT", passed)]))
    impl = mayDiverge (withArg (holder t) (template stepImpl))
    acceptCallback = withArg (TFn [holder TInt] TInt) (function "acceptCallback")
    referenceOnly = calling (template "referenceOnly") [("acceptCallback", [M.Const (M.CFn stepImplInt)])]
    generics = [outer, throughBound, witness, impl, referenceOnly]

stepImpl, stepImplInt :: String
stepImpl = "<Holder as Step>::step"
stepImplInt = stepImpl ++ "[Int]"

mayDiverge :: M.Function -> M.Function
mayDiverge f = f{M.fnSpec = (M.fnSpec f){M.specTermination = Just S.MayDiverge}}

checkDivergence :: M.Program -> TestResult
checkDivergence p = foldr (<|>) callbackArgument (map check expected)
  where
    functions = Map.insert "main" (M.progMain p) (M.progFunctions p)
    outer = "outer[Holder<Int>]"
    inner = "throughBound[Holder<Int>]"
    witness = "Step for Holder::step[Int]"
    expected =
        [ (outer, Just S.MayDiverge, [inner])
        , (inner, Just S.MayDiverge, [witness])
        , (witness, Just S.MayDiverge, [stepImplInt])
        , (stepImplInt, Just S.MayDiverge, [])
        , ("ordinary", Nothing, [outer])
        , ("Step for Holder::guard[Int]", Nothing, [outer])
        , ("referenceOnly[Int]", Nothing, ["acceptCallback"])
        , ("main", Nothing, ["referenceOnly[Int]", outer])
        ]
    callbackArgument =
        let args = [os | Just f <- [Map.lookup "referenceOnly[Int]" functions]
                       , M.BasicBlock _ (M.Call _ os _ _) <- Map.elems (M.fnBlocks f)]
        in testAssertEq args [[M.Const (M.CFn stepImplInt)]]
    check (name, term, callees) = case Map.lookup name functions of
        Nothing -> Just ("missing function " ++ name)
        Just f -> fmap ((name ++ ": ") ++) (testAssertEq (M.specTermination (M.fnSpec f), calls f) (term, callees))

divergenceNoWork :: M.Program
divergenceNoWork = empty
    { M.progFunctions = Map.fromList [(M.fnName f, f) | f <- [caller, seed]] }
  where
    caller = calling (function "caller[Int]") [("seed", [])]
    seed = mayDiverge (function "seed")

witnessSource :: String
witnessSource = unlines
    [ "trait Feed<A> { fn feed(self: &Self) -> A [{ }] [{ affirm size(return) >= 1; }]; };"
    , "struct F3 { k: Int };"
    , "impl Feed<Array<Int, 3>> for F3 { fn feed(self: &Self) -> Array<Int, 3> { return #[1, 2, 3]; }; };"
    , "fn measure<T: Feed<Array<Int, n>>, n>(t: &T) -> Int [{ }] [{ affirm return >= 1; }] {"
    , "    fn oneMore(x: Int) -> Int { return x + 1; }; a = t.feed(); return oneMore(n + size(a));"
    , "}; xs = [1, 2]; ys = clone(xs); f = F3 { k: 0 }; return measure(&f) + size(ys);"
    ]

checkWitness :: Set.Set String -> M.Program -> TestResult
checkWitness library p = testAssertTrue (not (Set.null kept) && not (Set.null dropped))
    <|> testAssertTrue (any ("::oneMore" `isInfixOf`) [n | n <- Map.keys functions, "measure[" `isPrefixOf` n])
    <|> case Map.lookup "measure[F3, 3]" functions of
        Nothing -> Just "oracle fixture has no measure[F3, 3] copy"
        Just f -> testAssertEq (Map.lookup "n" (M.specEnv (M.fnSpec f))) (Just (int 3))
            <|> testAssertTrue (any (" for F3::feed" `isInfixOf`) (calls f))
  where
    functions = M.progFunctions p
    kept = Set.intersection library (Map.keysSet functions)
    dropped = Set.difference library (Map.keysSet functions)

packSource :: String
packSource = unlines
    [ "trait Score { fn score(self: &Self) -> Int; };"
    , "impl Score for Int { fn score(self: &Self) -> Int { return self; }; };"
    , "impl Score for Bool { fn score(self: &Self) -> Int { return 1; }; };"
    , "fn sink<..U: Score>(prefix: Int, rest: &..U) -> Int"
    , "  [{ affirm forall i in 0..size(rest): Score::score(get(rest, i)) >= 0; }] [{ }] {"
    , "    n = prefix; for i in 0..size(rest) { n = n + get(rest, i).score(); }; return n;"
    , "};"
    , "fn forward<..T: Score>(args: &..T) -> Int"
    , "  [{ affirm size(args) >= 1; affirm forall i in 0..size(args): Score::score(get(args, i)) >= 0; }] [{ }] {"
    , "    return sink(7, 0, slice(args, 1, size(args)));"
    , "}; return sink(0) + forward(1, true, 2);"
    ]

int :: Integer -> M.Operand
int = M.Const . M.CInt

block :: [M.Statement] -> M.Terminator -> M.BasicBlock
block = M.BasicBlock

function :: String -> M.Function
function n = M.Function n [] (Just TInt) (Map.singleton (M.Local 0) (M.LocalDecl TInt Nothing))
    (Map.singleton (M.BlockId 0) (block [M.Assign (M.Local 0) (M.Use (int 0))] M.Return)) [] [] [] [] [] M.emptySpec

empty :: M.Program
empty = M.Program Map.empty Map.empty (function "main") Map.empty Map.empty Map.empty Map.empty

rootId :: ModuleId
rootId = ModuleId "app" (Just "main")

permissionProgram :: M.Program
permissionProgram = empty
    { M.progGenerics = Map.fromList
        [("Holder", (["T"], [("value", TParam "T")])), ("List", (["T"], [("blk", TBlock (TParam "T")), ("len", TInt)]))]
    , M.progMain = (M.progMain empty){M.fnLocals = Map.insert (M.Local 1) (M.LocalDecl (TRef holder) (Just "h")) (M.fnLocals (M.progMain empty))}
    }
  where
    holder = TNamed "Holder" [ArgType (TNamed "List" [ArgType TInt])]

checkPermission :: M.Program -> TestResult
checkPermission p =
    testAssertEq (Map.lookup (instanceName "List" [ArgType TInt]) (M.progTypes p))
        (Just (M.StructDecl [("blk", TBlock TInt), ("len", TInt)]))

bounded :: M.BoundedFn
bounded = M.BoundedFn [] [] [] []

template :: String -> M.Function
template n = (function n){M.fnTypeParams = ["T"]}

calling :: M.Function -> [(String, [M.Operand])] -> M.Function
calling f cs = f{M.fnBlocks = Map.fromList (zip (map M.BlockId [0 ..]) blocks)}
  where
    blocks = [block [] (M.Call (M.Const (M.CFn name)) args (M.Local 0) (M.BlockId (i + 1))) | (i, (name, args)) <- zip [0 ..] cs]
        ++ [block [] M.Return]

calls :: M.Function -> [String]
calls f = [n | M.BasicBlock _ (M.Call (M.Const (M.CFn n)) _ _ _) <- Map.elems (M.fnBlocks f)]

wide, wider :: Integer
wide = 2 ^ (130 :: Int) + 11
wider = wide + 2 ^ (64 :: Int)

testMirCopyKeys :: Test
testMirCopyKeys = TestList "testMirCopyKeys"
    [ TestCase "structural keys, last alias, colliding labels and signed wide substitution" $ do
        tool <- nativeCopiesProbe
        withResult tool $ \executable -> do
            actual <- Native.runWithInputFull executable ("keys\n" ++ hostNameProfile)
            pure (testAssertEq actual (ExitSuccess, expected, ""))
    ]
  where
    label t n = "f[" ++ renderTypeForName t ++ ", " ++ show n ++ "]"
    distinct = TNamed "Int" []
    sizeArg = SizeConst (negate wider)
    original = TRef (TArrayOf (TParam "T") (SizeParam "n"))
    expected = unlines
        [ "last", "named", label TInt wider, label TInt wide, label distinct wide
        , unwords (typeTokens (substitute [("n", sizeArg)] [("T", TInt)] original))
        ]

keyProbeSource :: String
keyProbeSource = unlines
        [ "import copiesprobe::profile::reader { readNameProfile };"
        , "import data::reader::reader { readRecords };"
        , "import mir::copies::keys { CopyBinding, CopyInstance, NamedCopy, concreteKey, copyName, nameOf };"
        , "import mir::copies::types { substituteType };"
        , "import mir::full::tokens { name, tokenLine, word };"
        , "fn keyProbe() -> Int ~ {"
        , "    input = readRecords(0 - 1); if !input.ok { return 2; };"
        , "    profile = readNameProfile(&input.value); if !profile.ok || profile.end != size(input.value) { return 2; };"
        , "    a = " ++ key TInt wide ++ "; b = " ++ key TInt wider ++ "; c = " ++ key distinct wide ++ ";"
        , "    if !a.found || !b.found || !c.found { return 1; };"
        , "    aliases = [NamedCopy { key: clone(a.value), name: \"first\" }, NamedCopy { key: clone(a.value), name: \"last\" }, NamedCopy { key: clone(c.value), name: \"named\" }];"
        , "    nameOf(&profile.classes, &aliases, &a.value).print(); \"\\n\".print(); nameOf(&profile.classes, &aliases, &c.value).print(); \"\\n\".print();"
        , "    nameOf(&profile.classes, &aliases, &b.value).print(); \"\\n\".print(); copyName(&profile.classes, &a.value).print(); \"\\n\".print(); copyName(&profile.classes, &c.value).print(); \"\\n\".print();"
        , "    sizes = [CopyBinding { name: \"n\", tokens: " ++ tokens (sizeTokens sizeArg) ++ " }];"
        , "    types = [CopyBinding { name: \"T\", tokens: " ++ tokens (typeTokens TInt) ++ " }];"
        , "    ty = " ++ tokens (typeTokens original) ++ ";"
        , "    tokenLine(substituteType(&ty, &sizes, &types)).print(); \"\\n\".print(); return 0;"
        , "};"
        ]
  where
    sizeArg = SizeConst (negate wider)
    original = TRef (TArrayOf (TParam "T") (SizeParam "n"))
    distinct = TNamed "Int" []
    key t n = "concreteKey(CopyInstance { function: \"f\", args: [" ++ tokens (argTokens (ArgType t)) ++ ", "
        ++ tokens (argTokens (ArgSize (SizeConst n))) ++ "] })"
    tokens ts = "[" ++ intercalate ", " (map token ts) ++ "]"
    token s@('"' : _) = "name(" ++ s ++ ")"
    token s = "word(" ++ quote s ++ ")"

wideKeys :: M.Program
wideKeys = empty
    { M.progFunctions = Map.fromList [("sized", sized), ("unused", template "unused")]
    , M.progBounded = Map.fromList [("sized", bounded{M.boundedSizes = ["n"]}), ("unused", bounded)]
    , M.progInstances = Map.fromList [(name, ("sized", [ArgType TInt, ArgSize (SizeConst n)])) | (name, n) <- [("smallBitsA", wide), ("smallBitsB", wider)]]
    , M.progMain = calling (M.progMain empty) [("smallBitsA", [int wide]), ("smallBitsB", [int wider])]
    }
  where
    sized = (template "sized")
        { M.fnSizeParams = ["n"], M.fnParams = [M.Local 1]
        , M.fnLocals = Map.fromList [(M.Local 0, M.LocalDecl TInt Nothing), (M.Local 1, M.LocalDecl TInt (Just "n"))]
        , M.fnSpec = M.emptySpec{M.specEnv = Map.singleton "n" (M.Copy (M.Local 1))}
        , M.fnBlocks = Map.singleton (M.BlockId 0) (block [M.Assign (M.Local 0) (M.Use (M.Copy (M.Local 1)))] M.Return)
        }

checkWideKeys :: Bool -> M.Program -> TestResult
checkWideKeys retainUnused p = testAssertEq (Map.member "unused" functions) retainUnused
    <|> testAssertEq (Map.lookup "sized" functions >>= Map.lookup genericKey . M.specEnv . M.fnSpec) (Just (int 0))
    <|> testAssertEq (map lookupSize ["smallBitsA", "smallBitsB"]) (map (Just . int) [wide, wider])
  where
    functions = M.progFunctions p
    lookupSize n = Map.lookup n functions >>= Map.lookup "n" . M.specEnv . M.fnSpec

wideStatements :: Result M.Lowered String
wideStatements = fromStatements "trait Measure { fn measure(self: &Self) -> Int; }; impl Measure for Int { fn measure(self: &Self) -> Int { return self; }; }; fn read<T: Measure>(x: &T) -> Int { return x.measure(); };"
    [ S.ValidationStatement (S.AssignProofVar "proofWide" (S.Val (S.VInt (negate wider))))
    , S.Let "runtimeWide" (S.Val (S.VInt wide))
    , S.Return (S.F (S.Var "read") [S.Var "runtimeWide"])
    ]

checkWideStatements :: M.Program -> TestResult
checkWideStatements p =
    testAssertEq (filter ("read[" `isPrefixOf`) (calls mainFn)) ["read[Int]"]
    <|> testAssertEq (Map.member "read[Int]" (M.progFunctions p)) True
    <|> testAssertEq runtimeLiterals [wide]
    <|> testAssertEq proofLiterals [negate wider]
  where
    mainFn = M.progMain p
    blocks = Map.elems (M.fnBlocks mainFn)
    stmts = concatMap M.blockStatements blocks
    runtimeLiterals = [n | M.Assign _ (M.Use (M.Const (M.CInt n))) <- stmts, n > intMax]
        ++ [n | M.BasicBlock _ (M.Call _ args _ _) <- blocks, M.Const (M.CInt n) <- args, n > intMax]
    proofLiterals = [n | M.Ghost _ (M.GhostValidation (S.AssignProofVar _ (S.Val (S.VInt n)))) <- stmts, n < intMin]

recursion :: Bool -> M.Program
recursion grows = empty
    { M.progFunctions = Map.singleton "recur" (calling (template "recur") [("symbolic", [])])
    , M.progBounded = Map.singleton "recur" bounded
    , M.progInstances = Map.fromList
        [("a", ("recur", [ArgType TInt])), ("z", ("recur", [ArgType TInt])), ("symbolic", ("recur", [ArgType symbolic]))]
    , M.progMain = calling (M.progMain empty) [("a", [])]
    }
  where
    symbolic = if grows then TArrayOf (TParam "T") (SizeConst 1) else TParam "T"

checkRecursion :: M.Program -> TestResult
checkRecursion p = testAssertEq (calls (M.progMain p)) ["z"] <|> case Map.lookup "z" (M.progFunctions p) of
    Just f -> testAssertEq (calls f) ["z"] <|> testAssertTrue (Map.member coveredKey (M.specEnv (M.fnSpec f)))
    Nothing -> Just "last concrete alias did not produce the recursive copy"

growthRefusal :: String
growthRefusal = "Type error: recur calls itself with the types Array<Int, 1>, which are not those it is made for: a function with bounds is made for each type, and one that is made for a bigger type at each call would never end"

moveBeforeCopies :: TestResult
moveBeforeCopies = case finishLowered lowered of
    Error e | "Move error: " `isPrefixOf` e && "was moved" `isInfixOf` e ->
        testAssertEq (finishProgramWith Set.empty lowered) (Error e)
            <|> testAssertEq (makeCopiesWith Set.empty broken) (Error growthRefusal)
    result -> Just ("expected a move refusal, got " ++ show result)
  where
    p = recursion True
    mainFn = M.progMain p
    ty = TNamed "Thing" []
    l = M.Local
    bad = [ M.Assign (l 1) (M.MakeData "Thing" [("value", int 1)])
          , M.Assign (l 2) (M.Use (M.Move (l 1)))
          , M.Assign (l 3) (M.Use (M.Move (l 1)))
          ]
    addStatements b = b{M.blockStatements = bad ++ M.blockStatements b}
    broken = p
        { M.progTypes = Map.singleton "Thing" (M.StructDecl [("value", TInt)])
        , M.progMain = mainFn
            { M.fnBlocks = Map.adjust addStatements (M.BlockId 0) (M.fnBlocks mainFn)
            , M.fnLocals = Map.union (M.fnLocals mainFn) (Map.fromList [(l i, M.LocalDecl ty (Just n)) | (i, n) <- [(1, "original"), (2, "first"), (3, "second")]])
            }
        }
    lowered = asUnit broken

frameProgram :: M.Program
frameProgram = empty
    { M.progFunctions = Map.singleton "frame" f
    , M.progBounded = Map.singleton "frame" bounded
    , M.progInstances = Map.singleton "frameAlias" ("frame", [ArgType (TArrayOf TInt (SizeConst frameSize))])
    , M.progMain = calling (M.progMain empty) [("frameAlias", [])]
    }
  where
    base = template "frame"
    f = base{M.fnLocals = Map.insert (M.Local 1) (M.LocalDecl (TArrayOf (TParam "T") (SizeConst frameSize)) (Just "a")) (M.fnLocals base)}

frameSize :: Integer
frameSize = 4294967297

frameRefusal :: String
frameRefusal = "Type error: frame cannot be made as frameAlias for this call: Array<Array<Int, " ++ n ++ ">, " ++ n ++ "> takes "
    ++ show (frameSize * frameSize) ++ " words, more than the 8192 that an array held in a frame can have"
  where
    n = show frameSize

linkRefusals :: IO TestResult
linkRefusals = do
    merged <- oldMerge colliding
    pure (testAssertEq merged (Error collision)
        <|> testAssertEq (Link.linkPrograms colliding) (Error collision)
        <|> testAssertEq (Link.linkPrograms units) (Error ("Validation failed: " ++ growthRefusal)))
  where
    units = [(rootId, recursion True)]
    colliding = units ++ [(rootId, empty)]
    collision = "link error: module app::main has inconsistent units"

strictFnc :: IO TestResult
strictFnc = withResult standaloneFncExpected $ \expected ->
    case checkStandaloneFnc expected of
        Just e -> pure (Just ("oracle fixture: " ++ e))
        Nothing -> withResult (finishLowered standaloneFncLowered) $ \input ->
            requestCopies "copies" Set.empty input (testAssertEq (ExitSuccess, "2\n", "copies probe could not read MIR3\n"))

testFncReview :: Test
testFncReview = TestList "testFncReview" [testStandaloneFnc, testFncWitness, testRawFncCopies, testRawFncControls]

testStandaloneFnc :: Test
testStandaloneFnc = TestCase "standalone finish preserves contract bytes and specializes nested function types" $
    withResult standaloneFncExpected $ \expected ->
        withResult (finishProgramWith Set.empty standaloneFncLowered) $ \actual -> do
            legacy <- runOldMerge standaloneFncLegacyInput
            pure (checkStandaloneFnc expected <|> checkStandaloneFnc actual
                <|> testAssertEq (programData actual) (programData expected)
                <|> testAssertEq actual expected
                <|> testAssertEq legacy (Error "the linking request contains unreadable MIR3")
                <|> testAssertEq (finishProgramWith Set.empty (asUnit noWork)) (Ok noWork))
  where
    noWork = empty{M.progTypes = M.progTypes (M.lowProgram standaloneFncLowered)}

standaloneFncExpected :: Result M.Program String
standaloneFncExpected = finishLowered standaloneFncLowered `bindResult` makeCopiesWith Set.empty

standaloneFncLegacyInput :: Result String String
standaloneFncLegacyInput = finishLowered standaloneFncLowered `bindResult` \input -> oldMergeRequest [(rootId, input)]

standaloneFncLowered :: M.Lowered
standaloneFncLowered = asUnit $ empty
    { M.progTypes = Map.singleton "Callback" (M.StructDecl [("f", callbackType TInt (SizeConst 8))])
    , M.progGenerics = Map.fromList
        [ ("CallbackHolder", (["T", "n"], [("f", callbackType (TParam "T") (SizeParam "n"))]))
        , ("Envelope", (["F"], [("f", TParam "F")]))
        ]
    , M.progFunctions = Map.singleton "sized" sized
    , M.progBounded = Map.singleton "sized" bounded{M.boundedSizes = ["n"]}
    , M.progInstances = Map.fromList [(name, ("sized", [ArgType ty, ArgSize (SizeConst n)])) | (name, ty, n) <- fncCopies]
    , M.progMain = calling (M.progMain empty) [(name, [int n]) | (name, _, n) <- fncCopies]
    }
  where
    base = template "sized"
    sized = base
        { M.fnSizeParams = ["n"], M.fnParams = [M.Local 1]
        , M.fnLocals = Map.union (Map.fromList
            [ (M.Local 1, M.LocalDecl TInt (Just "n"))
            , (M.Local 2, M.LocalDecl (nestedCallbackType (TParam "T") (SizeParam "n")) (Just "callback"))
            , (M.Local 3, M.LocalDecl (TFn [holderType (TParam "T") (SizeParam "n")] TInt) Nothing)
            , (M.Local 4, M.LocalDecl (TFn [envelopeType (TParam "T") (SizeParam "n")] TInt) Nothing)
            ]) (M.fnLocals base)
        }

holderType :: Type -> Size -> Type
holderType t n = TNamed "CallbackHolder" [ArgType t, ArgSize n]

envelopeType :: Type -> Size -> Type
envelopeType t n = TNamed "Envelope" [ArgType (callbackType t n)]

fncCopies :: [(String, Type, Integer)]
fncCopies = [("ints2", TInt, 2), ("ints3", TInt, 3), ("bools2", TBool, 2)]

nestedCallbackType :: Type -> Size -> Type
nestedCallbackType t n = TFn [callbackType t n] TInt

callbackType :: Type -> Size -> Type
callbackType t n = TFnContract [TRef (TArrayOf t n)] t (FnContract ["x"]
    [FnClause [FnWord "affirm", FnWord "size", FnName "x", FnWord "gt", FnWord "0001"]]
    [FnClause [FnWord "affirm", FnWord "eq", FnWord "return", FnName "x"]])

checkStandaloneFnc :: M.Program -> TestResult
checkStandaloneFnc p =
    testAssertEq (calls (M.progMain p)) [name | (name, _, _) <- fncCopies]
    <|> foldr (<|>) Nothing [checkCopy name ty n | (name, ty, n) <- fncCopies]
  where
    checkCopy name ty n = case Map.lookup name (M.progFunctions p) >>= Map.lookup (M.Local 2) . M.fnLocals of
        Nothing -> Just ("missing callback local in " ++ name)
        Just local -> testAssertEq (unwords (typeTokens (M.localType local)))
            (unwords (typeTokens (nestedCallbackType ty (SizeConst n))))
            <|> checkField (holderType ty (SizeConst n)) ty n
            <|> checkField (envelopeType ty (SizeConst n)) ty n
    checkField (TNamed base args) ty n = testAssertEq (Map.lookup (instanceName base args) (M.progTypes p))
        (Just (M.StructDecl [("f", callbackType ty (SizeConst n))]))
    checkField _ _ _ = Just "expected a named callback struct"

testFncWitness :: Test
testFncWitness = TestCase "standalone finish ignores section words inside the witness check's return contract" $
    withResult (finishLowered fncWitnessLowered `bindResult` makeCopiesWith Set.empty) $ \expected ->
        withResult (finishProgramWith Set.empty fncWitnessLowered) $ \actual ->
            pure (checkFncWitness expected <|> withProgramData expected actual)
  where
    withProgramData expected actual = case programData actual of
        Error e -> Just e
        Ok out -> compareProgram expected out

fncWitnessLowered :: M.Lowered
fncWitnessLowered = asUnit $ empty
    { M.progFunctions = Map.fromList [(M.fnName f, f) | f <- [factory, impl, witness, identity]]
    , M.progBounded = Map.fromList [("factory", bounded), (M.fnName witness, bounded)]
    , M.progInstances = Map.fromList
        [("factoryInt", ("factory", [ArgType TInt])), ("witnessInt", (M.fnName witness, [ArgType TInt]))]
    , M.progMain = (calling (M.progMain empty) [("factoryInt", [])])
        { M.fnReturns = Just fncWitnessType, M.fnLocals = Map.singleton (M.Local 0) (M.LocalDecl fncWitnessType Nothing) }
    }
  where
    factory = (template "factory")
        { M.fnReturns = Just fncWitnessType, M.fnLocals = resultLocals TInt
        , M.fnBlocks = Map.fromList
            [ (M.BlockId 0, block [M.Assign (M.Local 1) (M.Use (int 7))]
                (M.Call (M.Const (M.CFn "<$param T as Factory>::make")) [M.Copy (M.Local 1)] (M.Local 0) (M.BlockId 1)))
            , (M.BlockId 1, block [] M.Return)
            ]
        }
    make name ty = (function name)
        { M.fnReturns = Just fncWitnessType, M.fnLocals = resultLocals ty, M.fnParams = [M.Local 1]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (block [M.Assign (M.Local 0) (M.Use (M.Const (M.CFn "identity")))] M.Return)
        }
    witness = (make "Factory for Int::make" (TParam "U")){M.fnTypeParams = ["U"]}
    impl = make "<Int as Factory>::make" TInt
    identity = (function "identity")
        { M.fnParams = [M.Local 1], M.fnLocals = Map.fromList [(l, M.LocalDecl TInt Nothing) | l <- [M.Local 0, M.Local 1]]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (block [M.Assign (M.Local 0) (M.Use (M.Copy (M.Local 1)))] M.Return)
        }
    resultLocals ty = Map.fromList [(M.Local 0, M.LocalDecl fncWitnessType Nothing), (M.Local 1, M.LocalDecl ty Nothing)]

fncWitnessType :: Type
fncWitnessType = TFnContract [TInt] TInt (FnContract ["x"] [FnClause [FnWord "sizeparams"]] [FnClause [FnWord "typeparams"]])

checkFncWitness :: M.Program -> TestResult
checkFncWitness p = testAssertEq (calls (M.progMain p)) ["factoryInt"]
    <|> testAssertEq (fmap callOperands (Map.lookup "factoryInt" functions)) (Just [("witnessInt", [M.Copy (M.Local 1)])])
    <|> testAssertEq (Map.lookup "witnessInt" functions >>= M.fnReturns) (Just fncWitnessType)
  where
    functions = M.progFunctions p
    callOperands f = [(n, args) | M.BasicBlock _ (M.Call (M.Const (M.CFn n)) args _ _) <- Map.elems (M.fnBlocks f)]

testRawFncCopies :: Test
testRawFncCopies = TestCase "raw copies ignores padded fnc counts but distinguishes the contract words 1 and 0001" $
    withResult (rawFncInput "w") $ \payload ->
        withResult (readLowered payload `bindResult` (makeCopiesWith Set.empty . M.lowProgram)) $ \expected ->
            case checkRawFncCopies expected of
                Just e -> pure (Just ("oracle fixture: " ++ e))
                Nothing -> do
                    seed <- cachedSeed
                    withResult seed $ \executable -> do
                        (code, out, err) <- Native.runWithInputFull executable (rawCopiesRequest payload)
                        pure (testAssertEq (code, err) (ExitSuccess, "") <|> compareProgram expected out)

rawFncInput :: String -> Result String String
rawFncInput bTokenMarker = programData p `bindResult` \payload -> case break (isPrefixOf "bounded ") (lines payload) of
    (before, declaration : after) -> Ok (unlines (before ++ [declaration] ++ instances ++ after))
    _ -> Error "raw fnc fixture has no bounded declaration"
  where
    p = empty
        { M.progFunctions = Map.singleton "takeCallback" ((template "takeCallback")
            { M.fnLocals = Map.fromList [(M.Local 0, M.LocalDecl TInt Nothing), (M.Local 1, M.LocalDecl (TParam "T") Nothing)] })
        , M.progBounded = Map.singleton "takeCallback" bounded
        , M.progMain = calling (M.progMain empty) [(name, []) | name <- ["a", "b", "c"]]
        }
    instances =
        [ "instance \"a\" \"takeCallback\" 1 type " ++ unwords (typeTokens (rawFncType "1"))
        , "instance \"b\" \"takeCallback\" 01 type fnc 01 int int 01 \"x\" 00 01 03 w return w gt " ++ bTokenMarker ++ " 1"
        , "instance \"c\" \"takeCallback\" 1 type " ++ unwords (typeTokens (rawFncType "0001"))
        ]

rawFncType :: String -> Type
rawFncType n = TFnContract [TInt] TInt (FnContract ["x"] [] [FnClause [FnWord "return", FnWord "gt", FnWord n]])

checkRawFncCopies :: M.Program -> TestResult
checkRawFncCopies p = testAssertEq (calls (M.progMain p)) ["b", "b", "c"]
    <|> testAssertEq (Map.keys functions) ["b", "c", "takeCallback"]
    <|> testAssertEq (map copyType ["b", "c"]) (map (Just . typeTokens . rawFncType) ["1", "0001"])
  where
    functions = M.progFunctions p
    copyType n = typeTokens . M.localType <$> (Map.lookup n functions >>= Map.lookup (M.Local 1) . M.fnLocals)

rawCopiesRequest :: String -> String
rawCopiesRequest payload = profiledRequest ("pass link\ncopies " ++ show (length (lines payload)) ++ "\n" ++ payload)

profiledRequest :: String -> String
profiledRequest request = request ++ nameProfilePrefix [request]

testRawFncControls :: Test
testRawFncControls = TestCase "malformed fnc is refused by copies; the valid raw fnc is refused by merge, merge-copies and mono" $
    withResult (rawFncInput "w") $ \valid ->
        withResult (rawFncInput "z") $ \malformed -> do
            seed <- cachedSeed
            withResult seed $ \executable -> do
                let unit = linkUnitData rootId valid
                    linkError = "the linking request contains unreadable MIR3"
                    check (label, request, message) = do
                        actual <- Native.runWithInputFull executable request
                        pure (fmap ((label ++ ": ") ++) (testAssertEq actual (ExitSuccess, "1\n", message ++ "\n")))
                results <- mapM check
                    [ ("malformed copies", rawCopiesRequest malformed, "the copies request contains unreadable MIR3")
                    , ("merge", "pass link\nmerge 1\n" ++ unit, linkError)
                    , ("merge-copies", profiledRequest ("pass link\nmerge-copies 1\n" ++ unit), linkError)
                    , ("mono", "pass mono\n" ++ valid, "the input is not full MIR version 3")
                    ]
                pure (foldr (<|>) Nothing results)
