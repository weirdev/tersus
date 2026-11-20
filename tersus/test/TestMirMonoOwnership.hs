module TestMirMonoOwnership (testMirMonoOwnership, testMirMonoOwnershipUsing, testMirMonoOwnershipFnShapesUsing) where

import Data.Char (isSpace)
import Control.Exception (bracket)
import Data.IORef (newIORef, modifyIORef', readIORef)
import System.Directory (getTemporaryDirectory, removeFile, getPermissions, setPermissions, Permissions(..))
import System.FilePath ((</>))
import System.IO (openTempFile, hClose)
import Data.List (isPrefixOf, isInfixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (ExitCode(..))
import Mir
import MirData (readLowered, readProgram, writeProgram, writeProgramWithGhosts, writeLowered)
import MirHousekeeping (Tool(..), ownershipTool, monomorphizeWith, monomorphizeOwnershipWith, eraseGhosts, nativeProgram)
import MirOwnershipData (ownershipInput, restoreOwnership)
import Native (runWithInputFull)
import qualified Syntax as S
import Types (Type(..), Size(..), Signature(..))
import TestHarness
import TestMirMono (monoFixtures, metadataProgram, genericProgram, legacyPackInput)
import TestClosures (closureAdder, closureCounter, closureModuleFiles)
import Compile (lowerSourceUsing)
import ElaboratorTool (Loader, bootstrapLoader)
import qualified PackageCompile as Package
import qualified Modules as Mod
import MirLists (lowerLists)
import MirHousekeeping (listLibrary)
import qualified MirEval
import Native (runWithInput, buildExecutableWith)
import Hash (fingerprint)
import Utils

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse

stage :: String -> Result a String -> Result a String
stage prefix (Error e) = Error (prefix ++ e)
stage _ ok = ok

staged :: IO Tool -> Program -> IO (Result Program String)
staged getTool p = do
    mono <- monomorphizeWith getTool p
    case mono of
        Error e -> pure (Error e)
        Ok original -> stagedOwnership getTool "ownership" original

stagedOwnership :: IO Tool -> String -> Program -> IO (Result Program String)
stagedOwnership getTool pass original = do
    selected <- getTool
    case selected of
        ToolFailed e -> pure (Error e)
        ToolInterpreted _ -> pure (Error "the ownership passes run natively only")
        ToolNative exe -> do
            (code,out,errors) <- runWithInputFull exe ("pass " ++ pass ++ "\n" ++ writeProgramWithGhosts (ownershipInput original))
            pure $ case code of
                ExitFailure n -> Error ("the ownership tool exited with " ++ show n ++ ": " ++ trimEnd errors)
                ExitSuccess
                    | trim out == "1" -> Error ("the ownership tool refused " ++ pass ++ ": " ++ trimEnd errors)
                    | not (null (trim errors)) -> Error ("the ownership tool reported: " ++ trimEnd errors)
                    | take 1 (lines out) /= ["tersus-mir 2"] -> Error "the ownership tool did not write MIR version 2"
                    | otherwise -> stage "the ownership tool wrote unreadable MIR: " (readProgram out) `bindResult` restoreOwnership original

compareAdapters :: IO Tool -> Program -> IO TestResult
compareAdapters tool p = do
    expected <- staged tool p
    actual <- monomorphizeOwnershipWith tool p
    pure (testAssertEq actual expected <> testAssertEq (show actual) (show expected) <> testAssertEq (wire actual) (wire expected))
  where
    wire (Error e) = Error e
    wire (Ok value) = writeLowered (unit value)

compareRaw :: IO Tool -> Program -> IO TestResult
compareRaw tool p = case writeLowered (unit p) of
    Error e -> pure (Just e)
    Ok input -> compareRawInput tool input

compareRawInput :: IO Tool -> String -> IO TestResult
compareRawInput tool input = do
    selected <- tool
    case selected of
        ToolNative exe -> do
            mono@(code,monoOut,monoErrors) <- runWithInputFull exe ("pass mono\n" ++ input)
            fused <- runWithInputFull exe ("pass mono-ownership\n" ++ input)
            case (code,monoErrors,readLowered monoOut) of
                (ExitSuccess,"",Ok value) -> do
                    (ownedCode,ownedOut,ownedErrors) <- runWithInputFull exe ("pass ownership\n" ++ writeProgramWithGhosts (ownershipInput (lowProgram value)))
                    pure (testAssertEq fused (ownedCode,monoOut ++ ownedOut,ownedErrors))
                _ -> pure (testAssertEq fused mono)
        ToolFailed e -> pure (Just e)
        _ -> pure (Just "raw fusion controls require a native emitter")

unit :: Program -> Lowered
unit p = Lowered p Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty []

unwritableMetadata :: Program -> Program
unwritableMetadata p = p{progMain=(progMain p){fnSpec=(fnSpec (progMain p)){specRequires=[S.ProofAssert payload]}}}
  where
    payload = S.CTerm (S.VFunct [] [] [] (S.NativeFunct (Signature [] (TArrayOf TInt (SizeConst (10 ^ (30 :: Int)))) [] [] [] []) Nothing []) [])

withReplies :: (String, String, Int) -> (String, String, Int) -> IO TestResult
withReplies mono owned = case writeLowered (unit metadataProgram) of
    Error e -> pure (Just e)
    Ok validMono -> do
        directory <- getTemporaryDirectory
        bracket (openTempFile directory "tersus-fused-replies") cleanup $ \(script,handle) -> do
            hClose handle
            let responses = [("mono",mono),("ownership",owned),("mono-ownership",combined)]
                combined = if first mono == validMono then (first mono ++ first owned, second owned, third owned) else mono
                branch (selector,(_,_,status)) = "'pass " ++ selector ++ "') cat '" ++ script ++ "." ++ selector ++ ".out'; cat '" ++ script ++ "." ++ selector ++ ".err' >&2; exit " ++ show status ++ ";;\n"
            mapM_ (\(selector,(out,err,_)) -> writeFile (script ++ "." ++ selector ++ ".out") out >> writeFile (script ++ "." ++ selector ++ ".err") err) responses
            writeFile script ("#!/bin/sh\nIFS= read -r header\ncat >/dev/null\ncase \"$header\" in\n" ++ concatMap branch responses ++ "*) exit 99;;\nesac\n")
            permissions <- getPermissions script
            setPermissions script permissions{executable=True}
            count <- newIORef (0 :: Int)
            let getter = modifyIORef' count (+1) >> pure (ToolNative script)
            expected <- staged getter genericProgram
            stagedCount <- readIORef count
            modifyIORef' count (const 0)
            actual <- monomorphizeOwnershipWith getter genericProgram
            fusedCount <- readIORef count
            pure (testAssertEq actual expected <> testAssertEq stagedCount (if first mono == validMono then 2 else 1) <> testAssertEq fusedCount 1)
  where
    first (a,_,_) = a
    second (_,b,_) = b
    third (_,_,c) = c
    cleanup (script,_) = mapM_ removeFile (script : [script ++ "." ++ selector ++ "." ++ stream | selector <- ["mono","ownership","mono-ownership"], stream <- ["out","err"]])

replyControls :: [Test]
replyControls = case writeLowered (unit metadataProgram) of
    Error e -> [testCase "reply fixture serializes" (Just e)]
    Ok mono ->
        let owned = writeProgramWithGhosts (ownershipInput metadataProgram)
            success = (mono,"",0)
            cases =
                [("one selected native tool acquisition",success,(owned,"",0))
                ,("Mono refusal",("1\n","mono-refusal\n",0),(owned,"",0))
                ,("Mono native exit",("","mono-exit\n",7),(owned,"",0))
                ,("ownership refusal after complete Mono",success,("1\n","owner-refusal\n",0))
                ,("ownership native exit after complete Mono",success,("","owner-exit\n",7))
                ,("ownership stderr after complete Mono",success,(owned,"owner-reported\n",0))
                ,("a complete Mono receipt alone is not success",success,("","",0))
                ,("trailing ownership records are refused",success,(owned ++ "unexpected-record\n","",0))
                ,("truncated Mono payload is refused",("tersus-mir 3\ndata 9\n","",0),(owned,"",0))
                ,("invalid complete Mono preserves native exit",("tersus-mir 3\ndata 2\ntersus-ast 1 mir\nroot 0\n","mono-exit\n",7),(owned,"",0))
                ,("invalid complete Mono preserves stderr precedence",("tersus-mir 3\ndata 2\ntersus-ast 1 mir\nroot 0\n","mono-reported\n",0),(owned,"",0))
                ,("invalid complete Mono preserves decoder error",("tersus-mir 3\ndata 2\ntersus-ast 1 mir\nroot 0\n","",0),(owned,"",0))
                ]
         in [TestCase label (withReplies a b) | (label,a,b) <- cases]

testMirMonoOwnershipFnShapesUsing :: Loader -> IO Tool -> Test
testMirMonoOwnershipFnShapesUsing loader tool = TestList "current Fn shape fusion"
    [ TestCase "borrowed Fn contract, zero-field object and named wrapper" $ checked "fn-contract" 12 (lower fnContract)
    , TestCase "FnMut preserves updates through the borrowed receiver" $ checked "fn-mut" 1202 (lower (closureCounter ++ "fn twice<F: FnMut() -> Int>(f: &mut F) -> Int { a = f(); b = f(); return a * 10 + b; }; c = Counter { count: 0 }; r = twice(&mut c); return r * 100 + c.count;"))
    , TestCase "FnOnce consumes the receiver and owning argument" $ checked "fn-once" 5 (lower fnOnce)
    , TestCase "a Copy capture inferred from its Fn bound preserves fused metadata" $ checked "closure-copy" 15 (lower "fn apply<F: Fn(Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; n = 10; return apply(fn(x) => x + n, 5);")
    , TestCase "a borrowed capture preserves its Fn body through fusion" $ checked "closure-borrow" 12 (lower "fn apply<F: Fn(Int) -> Int>(f: &F, x: Int) -> Int { return f(x); }; xs = [1, 2]; f = fn(x: Int) -> Int => x + size(xs); return apply(&f, 10);")
    , TestCase "an FnMut capture retains updates across both calls" $ checked "closure-mut" 1202 (lower "fn twice<F: FnMut() -> Int>(f: &mut F) -> Int { a = f(); b = f(); return a * 10 + b; }; count = 0; c = fn() -> Int { count = count + 1; return count; }; return twice(&mut c) * 100 + count;")
    , TestCase "an FnOnce capture retains ownership of its list" $ checked "closure-once" 2 (lower "fn useOnce<F: FnOnce() -> List<Int>>(f: F) -> Int { ys = f(); return size(ys); }; xs = [1, 2]; f = fn() -> List<Int> => xs; return useOnce(f);")
    , TestCase "an inferred cross-module capture keeps the no-generic ownership path" $ checkedWithGeneric False "closure-modules" 15
        (Package.compileModulesWith loader (Mod.Snapshot (Mod.resolverFromFiles
            [("app/package.tersus", ""), ("app/main.tersus", "import app::apply; n = 10; return apply::apply(fn(x) => x + n, 5);"), ("app/apply.tersus", "fn apply<F: Fn(Int) -> Int>(f: &F, x: Int) -> Int { return f(x); };")]) "app/main.tersus" False)
            `bindResult` Package.lowerCompiledPackage)
    , TestCase "unsupported cross-module Fn is refused before native passes" $ do
        let forbidden = error "unsupported cross-module Fn acquired a native pass tool"
            afterLowering run = case package of
                Error e -> pure (Error e)
                Ok p -> run forbidden p
            expected = Error "in module app: Type error: apply needs F to implement Fn(...), and app$provider$provider$Adder does not" :: Result Program String
        stagedResult <- afterLowering staged
        fusedResult <- afterLowering monomorphizeOwnershipWith
        pure (testAssertEq stagedResult expected <> testAssertEq fusedResult expected)
    ]
  where
    lower = lowerSourceUsing loader False True
    package = Package.compileModulesWith loader (Mod.Snapshot (Mod.resolverFromFiles moduleFiles) "app/main.tersus" False) `bindResult` Package.lowerCompiledPackage
    moduleFiles = [(path,case path of
        "app/main.tersus" -> "import app::apply; import app::provider; fn hold<F>(f: &F) -> &F from f [{ }] [{ }] { return f; }; a = provider::Adder { n: 10 }; return apply::apply(hold(&a), 5);"
        "app/apply.tersus" -> source
        _ -> source) | (path,source) <- closureModuleFiles]
        ++ [("app/provider/provider.tersus", closureAdder)]
    fnContract = "struct Inc { }; impl Fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] for Inc { fn call(self: &Self, x: Int) -> Int [{ }] [{ affirm return > x; }] { return x + 1; }; }; fn inc(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] { return x + 1; }; fn useIt<F: Fn(x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }]>(f: &F, x: Int) -> Int [{ affirm x > 0; }] [{ affirm return > x; }] { return f(x); }; i = Inc { }; return useIt(&i, 5) + useIt(inc, 5);"
    fnOnce = "struct Once { xs: List<Int> }; impl FnOnce(x: List<Int>) -> Int for Once { fn call(self: Self, x: List<Int>) -> Int { return size(self.xs) + size(x); }; }; fn useOnce<F: FnOnce(x: List<Int>) -> Int>(f: F, x: List<Int>) -> Int { return f(x); }; o = Once { xs: [1, 2] }; return useOnce(o, [3, 4, 5]);"
    checked = checkedWithGeneric True
    checkedWithGeneric requireGeneric label wanted lowered = case lowered of
        Error e -> pure (Just (label ++ " lowering: " ++ e))
        Ok p -> do
            let generics program = [fnName fn | fn <- Map.elems (progFunctions program), not (null (fnTypeParams fn) && null (fnSizeParams fn))]
                expectedRoute program = not (null (generics program)) == requireGeneric
            if not (expectedRoute p) then pure (Just (label ++ " lowering selected the wrong generic route")) else do
                expanded <- stagedOwnership tool "expand" p
                library <- listLibrary
                case expanded `bindResult` \value -> lowerLists library value of
                    Error e -> pure (Just (label ++ " native preparation: " ++ e))
                    Ok native -> if not (expectedRoute native) then pure (Just (label ++ " native preparation changed the generic route")) else do
                        count <- newIORef (0 :: Int)
                        let getter = modifyIORef' count (+1) >> tool
                        expected <- staged getter native
                        stagedCount <- readIORef count
                        modifyIORef' count (const 0)
                        actual <- monomorphizeOwnershipWith getter native
                        fusedCount <- readIORef count
                        raw <- compareRaw tool native
                        case (expected, actual) of
                            (Ok reference, Ok fused) -> do
                                emitted <- execute label fused
                                putStrLn ((if requireGeneric then "[FN_FUSION_ROUTE] " else "[FN_NO_GENERIC_ROUTE] ") ++ label ++ " lowered=" ++ show (generics p) ++ " native=" ++ show (generics native) ++ " acquisitions=" ++ show (stagedCount,fusedCount) ++ " wire=" ++ show (wireHash native))
                                pure (testAssertEq (stagedCount,fusedCount) (if requireGeneric then (2,1) else (1,1))
                                    <> testAssertEq (show fused) (show reference)
                                    <> testAssertEq (writeLowered (unit fused)) (writeLowered (unit reference))
                                    <> raw <> testAssertEq (MirEval.runProgram p) (Ok (Just (MirEval.MInt wanted)))
                                    <> testAssertEq emitted (Ok (ExitSuccess,show wanted ++ "\n","")))
                            _ -> pure (Just (label ++ " staged/fused failure: " ++ show (expected,actual)))
    wireHash program = mapResult (fingerprint . pure) (writeLowered (unit program))
    execute label program = do
        selected <- tool
        case selected of
            ToolNative exe -> do
                ir <- runWithInput exe (writeProgram program)
                case ir of
                    Error e -> pure (Error e)
                    Ok text -> do
                        directory <- getTemporaryDirectory
                        bracket (openTempFile directory ("tersus-" ++ label)) (\(path,_) -> removeFile path) $ \(path,handle) -> do
                            hClose handle
                            made <- buildExecutableWith [] path text
                            case made of
                                Error e -> pure (Error e)
                                Ok _ -> Ok <$> runWithInputFull path ""
            ToolFailed e -> pure (Error e)
            ToolInterpreted _ -> pure (Error "Fn native output requires a native emitter")

landedOwnershipReceipt :: IO Tool -> IO TestResult
landedOwnershipReceipt tool = case lowerSourceUsing bootstrapLoader False True source `bindResult` eraseGhosts `bindResult` nativeProgram of
    Error e -> pure (Just ("the landed generic refusal did not reach ownership: " ++ e))
    Ok program -> do
        raw <- compareRaw tool program
        selected <- tool
        case (selected, writeLowered (unit program)) of
            (ToolNative exe, Ok input) -> do
                (monoCode, monoText, monoErrors) <- runWithInputFull exe ("pass mono\n" ++ input)
                (fusedCode, fusedText, fusedErrors) <- runWithInputFull exe ("pass mono-ownership\n" ++ input)
                actual <- monomorphizeOwnershipWith tool program
                pure (raw <> testAssertEq monoCode ExitSuccess <> testAssertEq monoErrors ""
                    <> testAssertTrue (case readLowered monoText of Ok _ -> True; Error _ -> False)
                    <> testAssertEq fusedCode ExitSuccess
                    <> testAssertEq fusedText (monoText ++ "1\n")
                    <> testAssertTrue ("still looks at a part of it that holds a value with a drop" `isInfixOf` fusedErrors)
                    <> testAssertTrue (case actual of Error message -> "still looks at a part of it that holds a value with a drop" `isInfixOf` message; Ok _ -> False))
            (ToolFailed e, _) -> pure (Just e)
            (_, Error e) -> pure (Just e)
            _ -> pure (Just "landed fused receipt requires a native tool")
  where
    source = "struct H { addr: Addr<Int>, xs: List<Int>, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl Drop for H { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl H { fn new() -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, xs: [1, 2], blk: b }; }; }; struct W<T> { addr: Addr<Int>, x: T, ghost blk: Block<Int> } invariant [{ affirm base(blk) = addr; affirm whole(blk); affirm cap(blk) = 1; affirm count(blk) = 0; affirm filled(blk, 0) = false; }]; impl<T> Drop for W<T> { fn drop(self: Self) -> Int { return Addr::free(self.addr, self.blk); }; }; impl<T> W<T> { fn new(x: T) -> Self { (a, b) = Addr::alloc(1); return Self { addr: a, x: x, blk: b }; }; }; trait Sz { fn sz(self: &Self) -> Int; }; impl Sz for H { fn sz(self: &Self) -> Int { return size(self.xs); }; }; fn f<T: Sz>(w: W<T>, w2: W<T>) -> Int { v = w.x; w = w2; return v.sz(); }; return f(W::new(H::new()), W::new(H::new()));"

testMirMonoOwnership :: Test
testMirMonoOwnership = testMirMonoOwnershipUsing ownershipTool

testMirMonoOwnershipUsing :: IO Tool -> Test
testMirMonoOwnershipUsing tool = TestList "testMirMonoOwnership"
    [ testMirMonoOwnershipFnShapesUsing bootstrapLoader tool
    , TestList "staged versus fused metadata and substitution" [TestCase label (compareAdapters tool p) | (label,p) <- monoFixtures]
    , TestList "raw existing codec receipts" [TestCase label (compareRaw tool p) | (label,p) <- monoFixtures]
    , TestCase "landed ownership success preserves staged and fused metadata" $ do
        actual <- monomorphizeOwnershipWith tool genericProgram
        adapted <- compareAdapters tool genericProgram
        receipt <- compareRaw tool genericProgram
        pure (testAssertTrue (case actual of Ok _ -> True; Error _ -> False) <> adapted <> receipt)
    , TestCase "landed ownership errors retain the complete fused Mono receipt" (landedOwnershipReceipt tool)
    , TestCase "no generic keeps the ownership MIR2 writability domain" $ do
        let p = unwritableMetadata metadataProgram
        expected <- staged tool p
        actual <- monomorphizeOwnershipWith tool p
        pure (testAssertTrue (case writeLowered (unit p) of Error _ -> True; _ -> False)
            <> testAssertTrue (case expected of Ok _ -> True; _ -> False)
            <> testAssertEq actual expected <> testAssertEq (show actual) (show expected))
    , TestCase "generic discarded metadata retains full input refusal before tool acquisition" $ do
        let p = unwritableMetadata genericProgram
            forbidden = error "unwritable full input acquired a native tool"
        a <- staged forbidden p
        b <- monomorphizeOwnershipWith forbidden p
        pure (testAssertEq b a <> testAssertTrue (case b of Error _ -> True; _ -> False))
    , TestCase "failed generic tool has no fallback" (compareAdapters (pure (ToolFailed "fused-tool-failure")) genericProgram)
    , TestCase "interpreted generic tool has no fallback" (compareAdapters (pure (ToolInterpreted metadataProgram)) genericProgram)
    , TestCase "an ownership refusal after Mono remains a refusal" (compareAdapters tool negativeBlocks)
    , TestCase "legacy PackLoop input keeps both canonical staged receipts" (compareRawInput tool legacyPackInput)
    , TestCase "the fused full reader rejects a trailing blank-line suffix" $ case writeLowered (unit metadataProgram) of
        Error e -> pure (Just e)
        Ok input -> compareRefusal (input ++ "\nunknown-suffix\n")
    , TestList "adapter partial receipts and errors" replyControls
    , TestList "malformed full requests" [TestCase label (compareRefusal input) | (label,input) <- malformed]
    ]
  where
    negativeBlocks = genericProgram{progMain=(progMain genericProgram){fnBlocks=Map.singleton (BlockId (-1)) (BasicBlock [] Return)}}
    malformed = [("old runtime MIR is not full input","tersus-mir 2\n"),("incomplete full input","tersus-mir 3\nnot-mir\n"),("bad payload count","tersus-mir 3\ndata 1\n")]
    compareRefusal input = do
        selected <- tool
        case selected of
            ToolNative exe -> do
                a <- runWithInputFull exe ("pass mono\n" ++ input)
                b <- runWithInputFull exe ("pass mono-ownership\n" ++ input)
                pure (testAssertEq b a <> testAssertTrue (case b of (ExitSuccess,"1\n",err) -> not (null err); _ -> False))
            ToolFailed e -> pure (Just e)
            _ -> pure (Just "refusal controls require a native emitter")
