module TestMirMonoOwnership (testMirMonoOwnership, testMirMonoOwnershipUsing) where

import Data.Char (isSpace)
import Control.Exception (bracket)
import Data.IORef (newIORef, modifyIORef', readIORef)
import System.Directory (getTemporaryDirectory, removeFile, getPermissions, setPermissions, Permissions(..))
import System.FilePath ((</>))
import System.IO (openTempFile, hClose)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (ExitCode(..))
import Mir
import MirData (readLowered, readProgram, writeProgramWithGhosts, writeLowered)
import MirHousekeeping (Tool(..), ownershipTool, monomorphizeWith, monomorphizeOwnershipWith)
import MirOwnershipData (ownershipInput, restoreOwnership)
import Native (runWithInputFull)
import qualified Syntax as S
import Types (Type(..), Size(..), Signature(..))
import TestHarness
import TestMirMono (monoFixtures, metadataProgram, genericProgram)
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
        Ok original -> do
            selected <- getTool
            case selected of
                ToolFailed e -> pure (Error e)
                ToolInterpreted _ -> pure (Error "the ownership passes run natively only")
                ToolNative exe -> do
                    (code,out,errors) <- runWithInputFull exe ("pass ownership\n" ++ writeProgramWithGhosts (ownershipInput original))
                    pure $ case code of
                        ExitFailure n -> Error ("the ownership tool exited with " ++ show n ++ ": " ++ trimEnd errors)
                        ExitSuccess
                            | trim out == "1" -> Error ("the ownership tool refused ownership: " ++ trimEnd errors)
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
    Ok input -> do
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
                ]
         in [TestCase label (withReplies a b) | (label,a,b) <- cases]

testMirMonoOwnership :: Test
testMirMonoOwnership = testMirMonoOwnershipUsing ownershipTool

testMirMonoOwnershipUsing :: IO Tool -> Test
testMirMonoOwnershipUsing tool = TestList "testMirMonoOwnership"
    [ TestList "staged versus fused metadata and substitution" [TestCase label (compareAdapters tool p) | (label,p) <- monoFixtures]
    , TestList "raw existing codec receipts" [TestCase label (compareRaw tool p) | (label,p) <- monoFixtures]
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
