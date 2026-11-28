module TestMirValidationMono (testMirValidationMono) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Monad (forM)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import System.Exit (ExitCode (..))
import System.IO.Unsafe (unsafePerformIO)

import Compile (lowerSourceUsing)
import ElaboratorTool (bootstrapLoader)
import LibPackage (libPackage)
import qualified Mir as M
import MirCopiesNameProfile (nameProfilePrefix)
import MirData (readCheckedLowered, writeOwnedProgram)
import MirHousekeeping (ownedWith, ownedContentKey)
import MirMono (monomorphizeForValidation)
import MirPass (programData)
import qualified Native
import PackageCompile (compileModulesUsing, lowerCompiledPackage)
import PackageData (Snapshot (..), resolverFromFiles)
import PreludeSource (toolPackageFiles)
import Seed (cachedSeed, compilerSnapshotHash)
import SelfHostedMir (encodePrepared, sourceContainerView)
import qualified Syntax as S
import TestHarness
import TestMirCopiesParity (compareProgram, empty, function, int, profileReader, template, witnessSource)
import TestMirMono (monoFixtures)
import Types (Arg (..), FnClause (..), FnClauseToken (..), FnContract (..), OwnershipFacts (..), Size (..), Type (..), instanceName)
import Utils
import ValidatorNative (prepareEncodedTexts, prepareTexts)

{-# NOINLINE probeCache #-}
probeCache :: MVar (Maybe (Result FilePath String))
probeCache = unsafePerformIO (newMVar Nothing)

probe :: IO (Result FilePath String)
probe = modifyMVar probeCache $ \saved -> case saved of
    Just result -> pure (saved, result)
    Nothing -> do
        result <- buildProbe
        pure (Just result, result)

buildProbe :: IO (Result FilePath String)
buildProbe = do
    modules <- forM ["driver", "mono", "types"] $ \name -> do
        source <- readFile ("dev/mir-validation-mono/" ++ name ++ ".tersus")
        pure (prefix ++ name ++ ".tersus", source)
    let files = toolPackageFiles ++ modules ++ [(prefix ++ "package.tersus", ""), (prefix ++ "profile.tersus", profileReader)]
        snapshot = Snapshot (resolverFromFiles files) (prefix ++ "driver.tersus") False
        source = compileModulesUsing bootstrapLoader libPackage snapshot `bindResult` lowerCompiledPackage
    key <- nativeCacheKey [ownedContentKey compilerSnapshotHash (show files) []]
    case key of
        Error e -> pure (Error e)
        Ok complete -> Native.cachedProgram "mir-validation-mono-probe" complete "the validation mono test tool" $ \output -> do
            seed <- cachedSeed
            case (seed, source) of
                (Ok emitter, Ok p) -> do
                    owned <- ownedWith emitter p
                    case owned of
                        Error e -> pure (Error e)
                        Ok lowered -> case writeOwnedProgram lowered of
                            Error e -> pure (Error e)
                            Ok mirText -> do
                                llvm <- Native.runWithInput emitter mirText
                                case llvm of
                                    Error e -> pure (Error e)
                                    Ok ir -> Native.buildExecutable output ir
                (Error e, _) -> pure (Error e)
                (_, Error e) -> pure (Error e)
  where
    prefix = "lib/validationmonoprobe/"

runProbe :: String -> IO (Result (ExitCode, String, String) String)
runProbe request = do
    exe <- probe
    case exe of
        Error e -> pure (Error e)
        Ok path -> Ok <$> Native.runWithInputFull path (profile ++ request)
  where
    profile = case nameProfilePrefix [request] of
        "" -> "name-classes 0\n"
        text -> text

compareMono :: M.Program -> (M.Program -> TestResult) -> IO TestResult
compareMono original check = case programData original of
    Error e -> pure (Just ("host cannot transport fixture: " ++ e))
    Ok input -> do
        result <- runProbe input
        pure $ case result of
            Ok (ExitSuccess, out, "") -> case readCheckedLowered out of
                Ok lowered -> compareProgram expected out `orElse` check (M.lowProgram lowered)
                Error e -> Just ("unreadable probe output: " ++ e)
            Ok (code, out, err) -> Just ("validation mono probe: " ++ show code ++ " " ++ err ++ take 160 out)
            Error e -> Just e
  where
    expected = (monomorphizeForValidation original){M.progCaptureStorage = Map.empty}

orElse :: TestResult -> TestResult -> TestResult
orElse Nothing other = other
orElse failure _ = failure

lowerFixture :: String -> Result M.Program String
lowerFixture = lowerSourceUsing bootstrapLoader libPackage False True

proofParity :: IO TestResult
proofParity = case lowerFixture source of
    Error e -> pure (Just e)
    Ok lowered -> do
        let raw = lowered{M.progMain = inlineArray (M.progMain lowered)}
        logical <- check False raw (sourceContainerView raw)
        physical <- check True raw raw
        pure (logical `orElse` physical `orElse` testAssertTrue (prepareTexts False raw /= prepareTexts True raw))
  where
    source = unlines
        [ "fn evidence(xs: &List<Int>) -> Int { return 0; };"
        , "fn count<n>(a: Array<Int, n>) -> Int [{ }] [{ affirm return = n; }] { affirm size(a) = n; return n; };"
        , "return count(#[1, 2]);"
        ]
    inlineArray f = f{M.fnBlocks = Map.map rewrite (M.fnBlocks f)}
      where
        constants = Map.fromList [(l, c) | b <- Map.elems (M.fnBlocks f), M.Assign l (M.Use (M.Const c@M.CArray{})) <- M.blockStatements b]
        operand o = case o of
            M.Copy l | Just c <- Map.lookup l constants -> M.Const c
            M.Move l | Just c <- Map.lookup l constants -> M.Const c
            _ -> o
        keep s = case s of M.Assign l (M.Use (M.Const M.CArray{})) -> Map.notMember l constants; _ -> True
        rewrite b = b{M.blockStatements = filter keep (M.blockStatements b), M.blockTerminator = case M.blockTerminator b of
            M.Call f' args dest next -> M.Call f' (map operand args) dest next
            term -> term}
    check physical raw input = compareMono input $ \actual ->
        let templates = Map.filter (\f -> not (null (M.fnSizeParams f) && null (M.fnTypeParams f))) (M.progFunctions input)
            prepared p = p{M.progFunctions = Map.union (M.progFunctions p) templates, M.progTypes = Map.union (M.progTypes p) (M.progTypes input)}
            texts = prepareEncodedTexts . encodePrepared physical . prepared
            expected = prepareTexts physical raw
        in case expected of
            Error e -> Just ("fixture must reach validator serialization: " ++ e)
            Ok requests -> case lookup "count<2>" requests of
                Nothing -> Just "fixture has no prepared count<2> request"
                Just request ->
                    let withoutProofs f = f{M.fnSpec = M.emptySpec, M.fnBlocks = Map.map stripGhosts (M.fnBlocks f)}
                        stripGhosts b = b{M.blockStatements = [s | s <- M.blockStatements b, case s of M.Ghost{} -> False; _ -> True]}
                        stripped = actual{M.progFunctions = Map.adjust withoutProofs "count<2>" (M.progFunctions actual)}
                    in testAssertTrue (texts actual == expected)
                        `orElse` testAssertTrue (case texts stripped of Ok rs -> lookup "count<2>" rs /= Just request; Error _ -> True)

boxedOrdering :: IO TestResult
boxedOrdering = compareMono raw $ \actual -> foldr orElse Nothing
    [ testAssertEq (prepareTexts physical p) (Error message)
    | physical <- [False, True], p <- [raw, actual]
    ]
  where
    raw = empty{M.progMain = mainFn{M.fnParams = [M.Local 1], M.fnLocals = Map.insert (M.Local 1) decl (M.fnLocals mainFn)}}
    mainFn = M.progMain empty
    decl = M.LocalDecl (TBoxedClosure False (TFn [] (TUninit TInt))) Nothing
    message = "the program uses a feature the Tersus validator does not model yet: a boxed closure has an unsupported signature"

sharedEnvironment :: Bool -> IO TestResult
sharedEnvironment apply = case programData original of
    Error e -> pure (Just e)
    Ok input -> do
        let raw = unlines (concatMap change (lines input))
        result <- runProbe raw
        pure $ case (readCheckedLowered raw, result) of
            (Ok source, Ok (ExitSuccess, out, "")) ->
                let expected = monomorphizeForValidation (M.lowProgram source)
                    actualEnv = M.specEnv . M.fnSpec <$> Map.lookup label (M.progFunctions expected)
                in testAssertEq actualEnv (Just (Map.fromList [("n", expectedN), ("shadow", int 9)]))
                    `orElse` compareProgram expected out
            (parsed, output) -> Just ("shared env control: " ++ eitherResult parsed ++ "; " ++ eitherResult output)
  where
    eitherResult (Error e) = e
    eitherResult (Ok _) = "parsed"
    expectedN = if apply then int 2 else M.Copy (M.Local 1)
    label = if apply then "sharedSize<2>" else "sharedSize"
    change row
        | "function \"sharedSize\" " `isPrefixOf` row = ["shared 2 \"n\" copy 1 \"shadow\" copy 1", row]
        | row == "env none 2 \"n\" copy 1 \"shadow\" const int 9" = ["env 0 1 \"shadow\" const int 9"]
        | otherwise = [row]
    original = empty{M.progFunctions = Map.singleton "sharedSize" target, M.progMain = mainFn}
    ordinary = M.progMain empty
    target = (function "sharedSize")
        { M.fnSizeParams = ["n" | apply], M.fnParams = [M.Local 1]
        , M.fnLocals = Map.insert (M.Local 1) (M.LocalDecl TInt Nothing) (M.fnLocals ordinary)
        , M.fnSpec = M.emptySpec{M.specEnv = Map.fromList [("n", M.Copy (M.Local 1)), ("shadow", int 9)]}
        }
    mainFn = ordinary{M.fnBlocks = Map.fromList
        [(M.BlockId 0, M.BasicBlock [] (M.Call (M.Const (M.CFn "sharedSize")) [int 2] (M.Local 0) (M.BlockId 1))), (M.BlockId 1, M.BasicBlock [] M.Return)]}

runtimeRefusal :: IO TestResult
runtimeRefusal = case programData empty of
    Error e -> pure (Just e)
    Ok input -> do
        let broken = unlines [if "assign 0 use " `isPrefixOf` row then "assign 0 packclosure const int 0" else row | row <- lines input]
        result <- runProbe broken
        pure (testAssertTrue (broken /= input) `orElse` testAssertEq result (Ok (ExitSuccess, "2\n", "validation mono probe could not read MIR3\n")))

boxedClosureParity :: IO TestResult
boxedClosureParity = case lowerFixture source of
    Error e -> pure (Just e)
    Ok live -> do
        r1 <- compareMono live $ \actual ->
            testAssertTrue (any ("keep<" `isPrefixOf`) (Map.keys (M.progFunctions actual)))
        r2 <- compareMono rawBoxed $ \actual ->
            testAssertTrue (any ("wrap<@boxed:" `isPrefixOf`) (Map.keys (M.progFunctions actual)))
                `orElse` testAssertTrue (Map.member "matchContract<Bool>" (M.progFunctions actual))
                `orElse` testAssertTrue (Map.member "matchContract<Int>" (M.progFunctions actual))
        pure (r1 `orElse` r2)
  where
    source = "fn keep<T>(x: T) -> T { return x; }; xs = keep([1, 2]); let f: Closure<fn() -> Int> = move fn() -> Int => size(xs); return f();"
    decl ty = M.LocalDecl ty Nothing
    boxedSig = TBoxedClosure False (TFn [] TInt)
    contractSig = TBoxedClosure True (TFnContract [TParam "T"] TInt (FnContract ["x"] [] []))
    concreteContract = TBoxedClosure True (TFnContract [TBool] TInt (FnContract ["x"] [] []))
    otherContract = TBoxedClosure True (TFnContract [TBool] TInt (FnContract ["y"] [] []))
    wrapFn = (template "wrap")
        { M.fnTypeParams = ["T"], M.fnSizeParams = ["n"], M.fnParams = [M.Local 1, M.Local 2]
        , M.fnReturns = Just (TParam "T")
        , M.fnLocals = Map.fromList [(M.Local 0, decl (TParam "T")), (M.Local 1, decl (TParam "T")), (M.Local 2, decl TInt), (M.Local 3, decl boxedSig)]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [M.Assign (M.Local 3) (M.PackClosure (M.Copy (M.Local 2)) "thunk")] M.Return)
        }
    matchFn = (template "matchContract")
        { M.fnTypeParams = ["T"], M.fnParams = [M.Local 1], M.fnReturns = Just TInt
        , M.fnLocals = Map.fromList [(M.Local 0, decl TInt), (M.Local 1, decl contractSig)]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)
        }
    rawBoxed = empty
        { M.progFunctions = Map.fromList [("wrap", wrapFn), ("matchContract", matchFn)]
        , M.progMain = (M.progMain empty)
            { M.fnLocals = Map.fromList [(M.Local 0, decl boxedSig), (M.Local 1, decl boxedSig), (M.Local 2, decl concreteContract), (M.Local 3, decl TInt), (M.Local 4, decl otherContract)]
            , M.fnBlocks = Map.fromList
                [ (M.BlockId 0, M.BasicBlock [] (M.Call (M.Const (M.CFn "wrap")) [M.Copy (M.Local 1), int 3] (M.Local 0) (M.BlockId 1)))
                , (M.BlockId 1, M.BasicBlock [] (M.Call (M.Const (M.CFn "matchContract")) [M.Copy (M.Local 2)] (M.Local 3) (M.BlockId 2)))
                , (M.BlockId 2, M.BasicBlock [] (M.Call (M.Const (M.CFn "matchContract")) [M.Copy (M.Local 4)] (M.Local 3) (M.BlockId 3)))
                , (M.BlockId 3, M.BasicBlock [] M.Return)
                ]
            }
        }

witnessParity :: IO TestResult
witnessParity = case lowerFixture witnessSource of
    Error e -> pure (Just e)
    Ok input -> compareMono input $ \actual ->
        testAssertTrue (any (isPrefixOf "Feed for F3::feed") (Map.keys (M.progFunctions actual)))

callbackAndShortSizes :: M.Program
callbackAndShortSizes = empty
    { M.progFunctions = Map.singleton "take" takeFn
    , M.progMain = (calling (M.progMain empty) [[M.Copy (M.Local 1), int wide, int 4], [M.Copy (M.Local 2), int wide, int 4], [int wide], [], [M.Copy (M.Local 1)]])
        { M.fnLocals = Map.fromList [(M.Local 0, decl TInt), (M.Local 1, decl (callback TInt "z")), (M.Local 2, decl (callback TInt "a"))] }
    }
  where
    decl ty = M.LocalDecl ty Nothing
    param = TParam "T"
    holder = TNamed "Holder" [ArgType (callback param "sizeparams"), ArgSize (SizeParam "n")]
    label = instanceName "Holder" [ArgType (callback param "sizeparams"), ArgSize (SizeParam "n")]
    callback ty marker = TFnContract [ty] ty (FnContract ["x"] [FnClause [FnWord marker, FnWord "named", FnName "N", FnWord "0", FnWord "p", FnName "n"]] [])
    wide = negate (2 ^ (132 :: Int) + 7)
    proof = S.ProofAssert (S.CTerm (S.VBool True))
    env = Map.fromList [("n", M.Copy (M.Local 2)), ("m", M.Move (M.Local 3)), ("frozen", M.Const (M.CFn "take")), ("datum", M.Const (M.CData label []))]
    takeFn = (template "take")
        { M.fnTypeParams = ["T", "U"], M.fnSizeParams = ["n", "m"], M.fnParams = map M.Local [1, 2, 3]
        , M.fnReturns = Just (callback param "typeparams")
        , M.fnLocals = Map.fromList [(M.Local 0, decl TInt), (M.Local 1, decl param), (M.Local 2, decl TInt), (M.Local 3, decl TInt), (M.Local 4, decl holder)]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock
            [M.Ghost env (M.GhostValidation proof), M.AssignRef (M.Local 4) [M.RefField label "field", M.RefIndex (M.Move (M.Local 2))] (M.Use (M.Const (M.CData label [])))] M.Return)
        , M.fnSpec = M.emptySpec{M.specEnv = env, M.specEnsures = [proof], M.specLoops = Map.singleton (M.BlockId 0) (M.LoopSpec [proof] Nothing env (M.BlockId 0))}
        }
    calling f args = f{M.fnBlocks = Map.fromList $ zip (map M.BlockId [0..]) $
        [M.BasicBlock [] (M.Call (M.Const (M.CFn "take")) a (M.Local 0) (M.BlockId i)) | (i,a) <- zip [1..] args] ++ [M.BasicBlock [] M.Return]}

dropRounds :: M.Program
dropRounds = empty
    { M.progFunctions = Map.fromList [(M.fnName f, f) | f <- namedSeed : map dropFn [1..5]]
    , M.progGenerics = Map.fromList [(base n, (["T"], [("perm", TBlock (TParam "T"))])) | n <- [1..6]]
    , M.progMain = (M.progMain empty){M.fnLocals = Map.fromList [(M.Local 0, decl TInt), (M.Local 1, decl (holder 1 TInt))]}
    }
  where
    base n = "Layer" ++ show (n :: Int)
    holder n ty = TNamed (base n) [ArgType ty]
    decl ty = M.LocalDecl ty Nothing
    namedSeed = (template "unreachable")
        { M.fnLocals = Map.fromList [(M.Local n, decl (holder n TInt)) | n <- [2..5]] }
    dropFn n = (template ("<" ++ base n ++ " as Drop>::drop"))
        { M.fnParams = [M.Local 1], M.fnReturns = Nothing
        , M.fnLocals = Map.fromList [(M.Local 1, decl (holder n (TParam "T"))), (M.Local 2, decl (holder (n+1) (TParam "T")))]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)
        }

checkedRolesParity :: M.Program
checkedRolesParity = empty
    { M.progFunctions = Map.fromList [(M.fnName f, f) | f <- [dropOuter, cloneOuter, dropInner]]
    , M.progGenerics = Map.fromList [("Outer", (["T", "n"], [("buf", TArrayOf (TParam "T") (SizeParam "n"))])), ("Inner", (["T"], [("v", TParam "T")]))]
    , M.progOwnership = Just $ Map.fromList
        [ ("Outer<Bool, 3>", OwnershipFacts Nothing (Just ("std$core$ownership$Drop", "outerDrop")) (Just ("std$core$ownership$Clone", "outerClone")) Nothing)
        , ("Inner<Bool>", OwnershipFacts Nothing (Just ("std$core$ownership$Drop", "innerDrop")) Nothing Nothing)
        ]
    , M.progMain = (M.progMain empty){M.fnLocals = Map.fromList [(M.Local 0, decl TInt), (M.Local 1, decl outerConcrete)]}
    }
  where
    decl ty = M.LocalDecl ty Nothing
    outerConcrete = TNamed "Outer" [ArgType TBool, ArgSize (SizeConst 3)]
    outerParam = TNamed "Outer" [ArgType (TParam "T"), ArgSize (SizeParam "n")]
    innerParam = TNamed "Inner" [ArgType (TParam "T")]
    dropOuter = (template "outerDrop")
        { M.fnTypeParams = ["T"], M.fnSizeParams = ["n"], M.fnParams = [M.Local 1, M.Local 2], M.fnReturns = Nothing
        , M.fnLocals = Map.fromList [(M.Local 1, decl outerParam), (M.Local 2, decl TInt), (M.Local 3, decl innerParam)]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)
        }
    cloneOuter = (template "outerClone")
        { M.fnTypeParams = ["T"], M.fnSizeParams = ["n"], M.fnParams = [M.Local 1, M.Local 2], M.fnReturns = Just outerParam
        , M.fnLocals = Map.fromList [(M.Local 0, decl outerParam), (M.Local 1, decl (TRef outerParam)), (M.Local 2, decl TInt)]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)
        }
    dropInner = (template "innerDrop")
        { M.fnTypeParams = ["T"], M.fnParams = [M.Local 1], M.fnReturns = Nothing
        , M.fnLocals = Map.fromList [(M.Local 1, decl innerParam)]
        , M.fnBlocks = Map.singleton (M.BlockId 0) (M.BasicBlock [] M.Return)
        }

testMirValidationMono :: Test
testMirValidationMono = TestList "testMirValidationMono"
    [ TestList "direct Haskell validation mono parity" [TestCase label (compareMono p (const Nothing)) | (label, p) <- monoFixtures]
    , TestCase "fnc structural collisions; wide and undersupplied sizes; frozen payloads and rewritten environments" $
        compareMono callbackAndShortSizes $ \p -> testAssertEq (Map.size (M.progFunctions p)) 3
    , TestCase "exactly four Drop discovery rounds retain instance permissions" $ compareMono dropRounds $ \p ->
        testAssertEq (Map.keys (M.progFunctions p)) ["<Layer" ++ show n ++ "<Int> as Drop>::drop" | n <- [1 :: Int ..4]]
            `orElse` testAssertEq (Map.lookup "Layer5<Int>" (M.progTypes p)) (Just (M.StructDecl [("perm", TBlock TInt)]))
    , TestCase "checked ownership roles specialize and retarget Drop and Clone with sizes across rounds" $ compareMono checkedRolesParity $ \p ->
        testAssertEq (Map.lookup "Outer<Bool, 3>" =<< M.progOwnership p)
            (Just (OwnershipFacts Nothing (Just ("std$core$ownership$Drop", "outerDrop<Bool, 3>")) (Just ("std$core$ownership$Clone", "outerClone<Bool, 3>")) Nothing))
            `orElse` testAssertEq (Map.lookup "Inner<Bool>" =<< M.progOwnership p)
                (Just (OwnershipFacts Nothing (Just ("std$core$ownership$Drop", "innerDrop<Bool>")) Nothing Nothing))
    , TestCase "live proof input bytes in both logical and physical views" proofParity
    , TestCase "live trait witness input through standalone Full" witnessParity
    , TestCase "boxed closure specialization and packclosure parity" boxedClosureParity
    , TestCase "boxed annotation refusal wins over malformed main" boxedOrdering
    , TestCase "standalone Full explicitly refuses malformed packclosure rows" runtimeRefusal
    , TestCase "raw shared environment rewrites hidden locals and preserves inline shadows" (sharedEnvironment True)
    , TestCase "no generic preserves raw shared environment semantics" (sharedEnvironment False)
    ]
