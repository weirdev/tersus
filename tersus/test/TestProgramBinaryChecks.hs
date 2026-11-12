module TestProgramBinaryChecks (binaryChecks, richProgram) where

import Control.DeepSeq (force)
import Control.Exception (IOException, evaluate, try)
import Control.Monad (unless, forM_)
import Data.Char (chr)
import Data.List (isInfixOf)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.Map.Strict as Map
import qualified Data.Binary as Binary
import Data.Binary.Put (runPut, putWord64be, putLazyByteString)
import Data.Bits (xor)
import Data.Word (Word64)
import System.FilePath ((</>))
import System.IO (IOMode (WriteMode), hSetFileSize, withBinaryFile)
import qualified Mir as M
import qualified Syntax as S
import qualified Types as T
import TestProgramBinary

assert :: String -> Bool -> IO ()
assert label ok = unless ok (error label) >> putStrLn ("PASS " ++ label)

richProgram :: M.Program
richProgram = M.Program types functions mainFn generics invariants bounded instances
  where
    huge :: Integer
    huge = 2 ^ (130 :: Int)
    proof = S.Forall "i" [S.FApp (S.ATerm "guard") [S.BVar "i"]] (S.FApp (S.ATerm "holds") [S.BVar "i", S.CTerm (S.VInt huge)])
    validations = [S.ProofAssert proof, S.Assume (S.ATerm "trusted"), S.AssignProofVar "q" (S.Val value), S.Rewrite (S.UserRewrite "lemma" [proof])]
    value = S.VFunct ["x"] validations' validations' (S.BuiltinFunct (T.ToWord True 128)) [proof]
    validations' = [S.ProofAssert (S.ATerm "distinct builtin contract")]
    termination = Just (S.Recursing (Just (S.Counting (S.Var "n"))))
    env = Map.fromList [("x", M.Copy (M.Local 9)), ("callee", M.Const (M.CFn "fn\NUL\955\128512"))]
    spec = M.FunctionSpec validations validations termination (Map.singleton (M.BlockId 7) (M.LoopSpec validations termination env (M.BlockId 11))) env ["x.field"] ["x"] ["x"]
    ghosts = [M.GhostValidation v | v <- validations] ++ [M.GhostAxiom "ax" ["a"] validations validations, M.GhostProof "pr" ["b"] validations validations validations, M.GhostFunction "fn" "alias" False, M.GhostPosition 999 111, M.GhostDissolve (M.Local 9)]
    mainFn = M.Function "main" [M.Local 9] (Just (T.TForall ["n"] ["T"] (T.TFn [T.TMutRef (T.TParam "T")] (T.TArrayOf T.TInt (T.SizeParam "n")))))
        (Map.singleton (M.Local 9) (M.LocalDecl (T.TBlock (T.TUninit T.TByte)) (Just "ghost")))
        (Map.singleton (M.BlockId 7) (M.BasicBlock (map (M.Ghost env) ghosts ++ [M.AssignRef (M.Local 9) [M.RefField "S" "f", M.RefIndex (M.Const (M.CInt (-huge)))] (M.Use (M.Const (M.CArray [M.CBool True, M.CList [M.CInt huge]])))]) (M.Call (M.Const (M.CFn "fn")) [M.Move (M.Local 9)] (M.Local 0) (M.BlockId 11))))
        ["n"] ["T"] [M.Local 9] [M.Local 9] [M.Local 9] spec
    types = Map.fromList [("S", M.StructDecl [("f", T.TNamed "G" [T.ArgSize T.SizeAny, T.ArgType (T.TVar 77)])]), ("E", M.EnumDecl [("E::V", [("p", T.TAddr (T.TVariant "E::V"))])])]
    functions = Map.singleton "fn" mainFn{M.fnName = "fn"}
    generics = Map.singleton "G" (["n","T"],[("arr", T.TArrayOf (T.TParam "T") (T.SizeVar 7))])
    invariants = Map.singleton "G" validations
    bounded = Map.singleton "fn" (M.BoundedFn ["n"] ["T"] ["fn::inner"])
    instances = Map.singleton "fn[Int, 3]" ("fn", [T.ArgType T.TInt, T.ArgSize (T.SizeConst 3)])

binaryChecks :: FilePath -> IO ()
binaryChecks dir = do
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
    let legacy = "tersus-test-program 1\n" ++ key ++ "\n" ++ show richProgram ++ "\n"
    assert "reject old header without fallback" (rejected (BL.fromStrict (BC.pack legacy)))
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
    BL.writeFile (dir </> "partial.binary") (BL.take (BL.length bytes-1) bytes)
    partial <- readEntryBytes (dir </> "partial.binary")
    assert "partial disk read rejects rather than returning Program" (rejected partial)
    BS.writeFile (dir </> "valid.binary") (BL.toStrict bytes)
    loaded <- readEntryBytes (dir </> "valid.binary")
    assert "bounded disk read roundtrip" (loaded == bytes)
    withBinaryFile (dir </> "oversized.binary") WriteMode $ \handle -> hSetFileSize handle (fromIntegral maxEntryBytes + 1)
    oversized <- try (readEntryBytes (dir </> "oversized.binary")) :: IO (Either IOException BL.ByteString)
    assert "oversized disk file rejected before materialization" (either (isInfixOf "exceeds size limit" . show) (const False) oversized)
