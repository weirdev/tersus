module Main (main) where
import Control.Monad (unless)
import qualified Data.ByteString as BS
import GHC.Clock (getMonotonicTimeNSec)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import TestHarness (executableDigest, verifiedSeedIdentity)

measure :: String -> IO (Maybe String) -> IO (Maybe String)
measure name action = do
    a <- getMonotonicTimeNSec
    c <- getCPUTime
    value <- action
    d <- getCPUTime
    b <- getMonotonicTimeNSec
    putStrLn (name ++ " wall=" ++ show (fromIntegral (b-a)/1e9 :: Double) ++ " cpu=" ++ show (fromIntegral (d-c)/1e12 :: Double) ++ " accepted=" ++ show (value /= Nothing))
    pure value

main :: IO ()
main = do
    [file] <- getArgs
    BS.writeFile file (BS.replicate (36 * 1024 * 1024) 97)
    Just expected <- executableDigest file
    cold <- measure "cold-pin-verification" (verifiedSeedIdentity file expected)
    hot <- measure "hot-pin-verification" (verifiedSeedIdentity file expected)
    unless (cold == Just expected && hot == cold) (error "valid pin rejected")
    BS.writeFile file (BS.replicate (36 * 1024 * 1024) 98)
    miss <- measure "changed-pin-rejection" (verifiedSeedIdentity file expected)
    unless (miss == Nothing) (error "changed pin reused")
