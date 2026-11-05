{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TestProgramBinary
    ( encodeEntry, decodeEntry, readEntryBytes, maxEntryBytes, codecVersion ) where

import Control.DeepSeq (NFData)
import Data.Binary (Binary, encode)
import Data.Binary.Get (getByteString, getWord64be, runGetOrFail)
import Data.Binary.Put (putByteString, putLazyByteString, putWord64be, runPut)
import qualified Data.Binary as Binary
import Data.Bits (xor)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BL
import Data.Int (Int64)
import Data.Word (Word64)
import GHC.Generics (Generic)
import System.IO (IOMode (ReadMode), hFileSize, withBinaryFile)
import qualified Mir as M
import qualified Syntax as S
import qualified Types as T

deriving instance Generic M.Local
instance Binary M.Local
instance NFData M.Local
deriving instance Generic M.BlockId
instance Binary M.BlockId
instance NFData M.BlockId
deriving instance Generic M.Program
instance Binary M.Program
instance NFData M.Program
deriving instance Generic M.TypeDecl
instance Binary M.TypeDecl
instance NFData M.TypeDecl
deriving instance Generic M.Function
instance Binary M.Function
instance NFData M.Function
deriving instance Generic M.LocalDecl
instance Binary M.LocalDecl
instance NFData M.LocalDecl
deriving instance Generic M.BasicBlock
instance Binary M.BasicBlock
instance NFData M.BasicBlock
deriving instance Generic M.Statement
instance Binary M.Statement
instance NFData M.Statement
deriving instance Generic M.GhostStatement
instance Binary M.GhostStatement
instance NFData M.GhostStatement
deriving instance Generic M.Rvalue
instance Binary M.Rvalue
instance NFData M.Rvalue
deriving instance Generic M.RefStep
instance Binary M.RefStep
instance NFData M.RefStep
deriving instance Generic M.BinOp
instance Binary M.BinOp
instance NFData M.BinOp
deriving instance Generic M.ListOp
instance Binary M.ListOp
instance NFData M.ListOp
deriving instance Generic M.Operand
instance Binary M.Operand
instance NFData M.Operand
deriving instance Generic M.Constant
instance Binary M.Constant
instance NFData M.Constant
deriving instance Generic M.Terminator
instance Binary M.Terminator
instance NFData M.Terminator
deriving instance Generic M.FunctionSpec
instance Binary M.FunctionSpec
instance NFData M.FunctionSpec
deriving instance Generic M.LoopSpec
instance Binary M.LoopSpec
instance NFData M.LoopSpec
deriving instance Generic T.Rel
instance Binary T.Rel
instance NFData T.Rel
deriving instance Generic T.BuiltinFunct
instance Binary T.BuiltinFunct
instance NFData T.BuiltinFunct
deriving instance Generic T.Type
instance Binary T.Type
instance NFData T.Type
deriving instance Generic T.Size
instance Binary T.Size
instance NFData T.Size
deriving instance Generic T.Arg
instance Binary T.Arg
instance NFData T.Arg
deriving instance Generic T.Signature
instance Binary T.Signature
instance NFData T.Signature
deriving instance Generic S.Termination
instance Binary S.Termination
instance NFData S.Termination
deriving instance Generic S.FunctBody
instance Binary S.FunctBody
instance NFData S.FunctBody
deriving instance Generic S.Value
instance Binary S.Value
instance NFData S.Value
deriving instance Generic S.Expression
instance Binary S.Expression
instance NFData S.Expression
deriving instance Generic S.ValidationStatement
instance Binary S.ValidationStatement
instance NFData S.ValidationStatement
deriving instance Generic S.Statement
instance Binary S.Statement
instance NFData S.Statement
deriving instance Generic S.TraitFn
instance Binary S.TraitFn
instance NFData S.TraitFn
deriving instance Generic (S.Proof i)
instance Binary i => Binary (S.Proof i)
instance NFData i => NFData (S.Proof i)
deriving instance Generic S.RwRule
instance Binary S.RwRule
instance NFData S.RwRule

codecVersion :: String
codecVersion = "tersus-test-program binary 1\n"

header :: BS.ByteString
header = BC.pack codecVersion

maxEntryBytes :: Int64
maxEntryBytes = 256 * 1024 * 1024

checksum :: BL.ByteString -> Word64
checksum = BL.foldl' (\h b -> (h `xor` fromIntegral b) * 1099511628211) 14695981039346656037

encodeEntry :: String -> M.Program -> BL.ByteString
encodeEntry key program = runPut $ do
    putByteString header
    putByteString (BC.pack key)
    putLazyByteString (BL.singleton 10)
    putWord64be (fromIntegral (BL.length payload))
    putWord64be (checksum payload)
    putLazyByteString payload
  where
    payload = encode program

decodeEntry :: String -> BL.ByteString -> Either String M.Program
decodeEntry key bytes
    | length key /= 64 || any (`notElem` "0123456789abcdef") key = Left "invalid cache key"
    | BL.length bytes > maxEntryBytes = Left "cache entry exceeds size limit"
    | otherwise = case runGetOrFail envelope bytes of
        Left (_, _, message) -> Left message
        Right (rest, _, (size, digest))
            | size > fromIntegral maxEntryBytes -> Left "payload exceeds size limit"
            | fromIntegral (BL.length rest) /= size -> Left "payload length mismatch or trailing bytes"
            | checksum rest /= digest -> Left "payload checksum mismatch"
            | otherwise -> case runGetOrFail Binary.get rest of
                Left (_, _, message) -> Left message
                Right (trailing, _, program)
                    | BL.null trailing -> Right program
                    | otherwise -> Left "trailing payload bytes"
  where
    envelope = do
        magic <- getByteString (BS.length header)
        if magic /= header then fail "invalid codec header" else pure ()
        actualKey <- getByteString 65
        if actualKey /= BC.pack (key ++ "\n") then fail "entry key mismatch" else pure ()
        size <- getWord64be
        digest <- getWord64be
        pure (size, digest)

readEntryBytes :: FilePath -> IO BL.ByteString
readEntryBytes path = withBinaryFile path ReadMode $ \handle -> do
    size <- hFileSize handle
    if size > fromIntegral maxEntryBytes
        then ioError (userError "cache entry exceeds size limit")
        else do
            bytes <- BS.hGet handle (fromIntegral size + 1)
            if fromIntegral (BS.length bytes) /= size
                then ioError (userError "cache file changed during read")
                else pure (BL.fromStrict bytes)
