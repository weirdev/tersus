module Main (main) where

import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (unless)
import Data.Char (isSpace)
import Data.List (stripPrefix)
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString as BS
import GHC.Clock (getMonotonicTimeNSec)
import GHC.Stats (getRTSStats, allocated_bytes)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.Mem (performGC)
import qualified Mir as M
import TestProgramBinary
import TestProgramBinaryChecks (binaryChecks)

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

main :: IO ()
main = getArgs >>= \args -> case args of
    ["prepare", path] -> prepare path
    ["bench", codec, phase, path] -> benchmark codec phase path
    ["checks"] -> binaryChecks "dev/cache-codec/fixtures"
    _ -> error "prepare PATH | bench old|binary read|decode|encode PATH | checks"
