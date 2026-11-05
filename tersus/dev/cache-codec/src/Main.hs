{-# LANGUAGE BangPatterns #-}
module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (IOException, evaluate, try)
import Control.Monad (unless, forM_)
import Data.Char (chr, isSpace)
import Data.List (isInfixOf, stripPrefix)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.Map.Strict as Map
import qualified Data.Binary as Binary
import Data.Binary.Put (runPut, putWord64be, putLazyByteString)
import Data.Bits (xor)
import Data.Word (Word64)
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Stats (getRTSStats, allocated_bytes)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.IO (IOMode (WriteMode), hSetFileSize, withBinaryFile)
import System.Mem (performGC)
import qualified Mir as M
import qualified Syntax as S
import qualified Types as T
import TestProgramBinary

legacyDecode :: String -> String -> M.Program
legacyDecode key text = case stripPrefix ("tersus-test-program 1\n" ++ key ++ "\n") text of
    Just body -> case reads body of
        [(program, rest)] | all isSpace rest -> program
        _ -> error "malformed legacy entry"
    _ -> error "legacy key/header mismatch"

legacyEncode :: String -> M.Program -> String
legacyEncode key program = "tersus-test-program 1\n" ++ key ++ "\n" ++ show program ++ "\n"

readLegacy :: FilePath -> IO String
readLegacy path = readFile path >>= evaluate . force

metric :: String -> IO a -> IO a
metric label action = do
    performGC
    before <- getRTSStats
    wall0 <- getMonotonicTimeNSec
    cpu0 <- getCPUTime
    result <- action
    cpu1 <- getCPUTime
    wall1 <- getMonotonicTimeNSec
    performGC
    after <- getRTSStats
    putStrLn $ unwords [label, "wall=" ++ show (fromIntegral (wall1-wall0)/1e9 :: Double),
        "cpu=" ++ show (fromIntegral (cpu1-cpu0)/1e12 :: Double),
        "allocated=" ++ show (allocated_bytes after - allocated_bytes before)]
    pure result

keyOf :: String -> String
keyOf = (!! 1) . lines

prepare :: FilePath -> IO ()
prepare path = do
    text <- readLegacy path
    let key = keyOf text
    program <- evaluate (force (legacyDecode key text))
    let bytes = encodeEntry key program
    _ <- evaluate (BL.length bytes)
    decoded <- either error (evaluate . force) (decodeEntry key bytes)
    unless (decoded == program && show decoded == show program) (error "full-state roundtrip mismatch")
    BL.writeFile (path ++ ".binary") bytes
    putStrLn $ "prepared " ++ path ++ " old=" ++ show (length text) ++ " binary=" ++ show (BL.length bytes)

benchmark :: String -> String -> FilePath -> IO ()
benchmark codec phase path = do
    -- Preparation is untimed and gives both codecs the identical, fully forced Program.
    text <- readLegacy path
    let key = keyOf text
    case (codec, phase) of
        ("old", "raw-read") -> metric "old/raw-read" (BS.readFile path) >> pure ()
        ("binary", "raw-read") -> metric "binary/raw-read" (BS.readFile (path ++ ".binary")) >> pure ()
        ("old", "read") -> metric "old/read" (readLegacy path) >> pure ()
        ("binary", "read") -> metric "binary/read" (readEntryBytes (path ++ ".binary")) >> pure ()
        ("old", "decode") -> metric "old/decode" (evaluate (force (legacyDecode key text))) >> pure ()
        ("binary", "decode") -> do
            bytes <- readEntryBytes (path ++ ".binary")
            metric "binary/decode" (either error (evaluate . force) (decodeEntry key bytes)) >> pure ()
        ("old", "encode") -> do
            program <- evaluate (force (legacyDecode key text))
            metric "old/encode" (evaluate (force (legacyEncode key program))) >> pure ()
        ("binary", "encode") -> do
            program <- evaluate (force (legacyDecode key text))
            metric "binary/encode" (evaluate (BL.length (encodeEntry key program))) >> pure ()
        _ -> error "unknown benchmark phase"

assert :: String -> Bool -> IO ()
assert label ok = unless ok (error label) >> putStrLn ("PASS " ++ label)

richProgram :: M.Program
richProgram = M.Program types functions mainFn generics invariants
  where
    huge :: Integer
    huge = 2 ^ (130 :: Int)
    proof = S.Forall "i" [S.FApp (S.ATerm "guard") [S.BVar "i"]] (S.FApp (S.ATerm "holds") [S.BVar "i", S.CTerm (S.VInt (huge))])
    validations = [S.ProofAssert proof, S.Assume (S.ATerm "trusted"), S.AssignProofVar "q" (S.Val value), S.Rewrite (S.UserRewrite "lemma" [proof])]
    value = S.VFunct ["x"] validations' validations' (S.BuiltinFunct (T.ToWord True 128)) [proof]
    validations' = [S.ProofAssert (S.ATerm "distinct builtin contract")]
    termination = Just (S.Recursing (Just (S.Counting (S.Var "n"))))
    env = Map.fromList [("x", M.Copy (M.Local 9)), ("callee", M.Const (M.CFn "fn\NUL\955\128512"))]
    spec = M.FunctionSpec validations validations termination (Map.singleton (M.BlockId 7) (M.LoopSpec validations termination env (M.BlockId 11))) env ["x.field"] ["x"] ["x"]
    ghosts = [M.GhostValidation v | v <- validations] ++ [M.GhostAxiom "ax" ["a"] validations validations, M.GhostProof "pr" ["b"] validations validations validations, M.GhostFunction "fn" "alias" False, M.GhostPosition 999 111, M.GhostDissolve (M.Local 9)]
    mainFn = M.Function "main" [M.Local 9] (Just (T.TForall ["n"] ["T"] (T.TFn [T.TMutRef (T.TParam "T")] (T.TArrayOf T.TInt (T.SizeParam "n")))))
        (Map.singleton (M.Local 9) (M.LocalDecl (T.TBlock (T.TUninit T.TByte)) (Just "ghost")))
        (Map.singleton (M.BlockId 7) (M.BasicBlock (map (M.Ghost env) ghosts ++ [M.AssignRef (M.Local 9) [M.RefField "S" "f", M.RefIndex (M.Const (M.CInt (-huge)))] (M.Use (M.Const (M.CArray [M.CBool True, M.CList [M.CInt (huge)]])))]) (M.Call (M.Const (M.CFn "fn")) [M.Move (M.Local 9)] (M.Local 0) (M.BlockId 11))))
        ["n"] ["T"] [M.Local 9] [M.Local 9] [M.Local 9] spec
    types = Map.fromList [("S", M.StructDecl [("f", T.TNamed "G" [T.ArgSize T.SizeAny, T.ArgType (T.TVar 77)])]), ("E", M.EnumDecl [("E::V", [("p", T.TAddr (T.TVariant "E::V"))])])]
    functions = Map.singleton "fn" mainFn{M.fnName = "fn"}
    generics = Map.singleton "G" (["n","T"],[("arr", T.TArrayOf (T.TParam "T") (T.SizeVar 7))])
    invariants = Map.singleton "G" validations

checks :: IO ()
checks = do
    let key = replicate 64 'a'
        bytes = encodeEntry key richProgram
        decoded = either error id (decodeEntry key bytes)
        rejected = either (const True) (const False) . decodeEntry key
    _ <- evaluate (force decoded)
    assert "rich roundtrip structural equality" (decoded == richProgram)
    assert "rich roundtrip full Show equality (Value Eq ignores builtin contracts)" (show decoded == show richProgram)
    let unusual = richProgram{M.progMain = (M.progMain richProgram){M.fnName = map chr [0,127,255,0xd7ff,0xd800,0xdfff,0x10ffff]}}
        unusualDecoded = either error id (decodeEntry key (encodeEntry key unusual))
    _ <- evaluate (force unusualDecoded)
    assert "all Char ranges survive without Unicode normalization" (show unusualDecoded == show unusual)
    assert "reject invalid key" (either (const True) (const False) (decodeEntry "bad" bytes))
    assert "reject different key" (either (const True) (const False) (decodeEntry (replicate 64 'b') bytes))
    assert "reject old header without fallback" (rejected (BL.fromStrict (BC.pack (legacyEncode key richProgram))))
    assert "reject trailing bytes" (rejected (bytes <> BL.singleton 0))
    forM_ [0,1,27,28,64,92,108,BL.length bytes `div` 2,BL.length bytes-1] $ \n -> assert ("reject truncated " ++ show n) (rejected (BL.take n bytes))
    let payload = Binary.encode richProgram
        prefix = BL.take (BL.length bytes - BL.length payload - 16) bytes
        digest bs = BL.foldl' (\h b -> (h `xor` fromIntegral b) * 1099511628211) (14695981039346656037 :: Word64) bs
        frame bs = prefix <> runPut (putWord64be (fromIntegral (BL.length bs)) >> putWord64be (digest bs) >> putLazyByteString bs)
    assert "valid integrity envelope is reconstructed exactly" (frame payload == bytes)
    assert "reject malformed binary with valid integrity envelope" (rejected (frame (BL.singleton 255)))
    assert "reject trailing payload inside valid envelope" (rejected (frame (payload <> BL.singleton 0)))
    assert "reject oversized declared length" (rejected (prefix <> runPut (putWord64be (fromIntegral maxEntryBytes+1) >> putWord64be 0)))
    forM_ [93,109,BL.length bytes `div` 2,BL.length bytes-1] $ \n ->
        assert ("reject corruption " ++ show n) (rejected (BL.take n bytes <> BL.singleton (BL.index bytes n `xor` 1) <> BL.drop (n+1) bytes))
    BL.writeFile "dev/cache-codec/fixtures/partial.binary" (BL.take (BL.length bytes-1) bytes)
    partial <- readEntryBytes "dev/cache-codec/fixtures/partial.binary"
    assert "partial disk read rejects rather than returning Program" (rejected partial)
    BS.writeFile "dev/cache-codec/fixtures/valid.binary" (BL.toStrict bytes)
    loaded <- readEntryBytes "dev/cache-codec/fixtures/valid.binary"
    assert "bounded disk read roundtrip" (loaded == bytes)
    withBinaryFile "dev/cache-codec/fixtures/oversized.binary" WriteMode $ \handle -> hSetFileSize handle (fromIntegral maxEntryBytes + 1)
    oversized <- try (readEntryBytes "dev/cache-codec/fixtures/oversized.binary") :: IO (Either IOException BL.ByteString)
    assert "oversized disk file rejected before materialization" (either (isInfixOf "exceeds size limit" . show) (const False) oversized)

main :: IO ()
main = getArgs >>= \args -> case args of
    ["prepare", path] -> prepare path
    ["bench", codec, phase, path] -> benchmark codec phase path
    ["checks"] -> checks
    _ -> error "prepare PATH | bench old|binary read|decode|encode PATH | checks"
