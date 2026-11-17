module TestMirMonoOwnership (testMirMonoOwnership, testMirMonoOwnershipUsing) where

import Data.Char (isSpace)
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
