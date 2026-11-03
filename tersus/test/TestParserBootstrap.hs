module TestParserBootstrap (testParserBootstrap) where

import Control.Exception (bracket, finally, evaluate)
import System.Directory (createDirectory, getTemporaryDirectory, removeDirectoryRecursive, removeFile)
import System.Environment (getArgs, getExecutablePath, lookupEnv, setEnv, unsetEnv)
import System.Exit (ExitCode (..))
import System.Process (proc, readCreateProcessWithExitCode)
import System.IO (hClose, openTempFile)
import System.FilePath ((</>))

import Pipeline (compileSource)
import TestHarness
import Utils

withEnv :: String -> Maybe String -> IO a -> IO a
withEnv key value action = bracket (lookupEnv key) restore $ \_ -> set value >> action
  where
    set Nothing = unsetEnv key
    set (Just text) = setEnv key text
    restore = set

testParserBootstrap :: Test
testParserBootstrap = TestList "testParserBootstrap" [TestCase "default whole Pipeline refuses failed native bootstrap" nativeFailure]

nativeFailure :: IO TestResult
nativeFailure = do
    args <- getArgs
    if "--child" `elem` args then failedBootstrap else do
        self <- getExecutablePath
        (status, out, err) <- readCreateProcessWithExitCode (proc self ["testParserBootstrap", "--child", "+RTS", "-N1", "-RTS"]) ""
        pure $ case status of
            ExitSuccess -> Nothing
            _ -> Just ("fresh parser bootstrap worker: " ++ out ++ err)

failedBootstrap :: IO TestResult
failedBootstrap = do
    tmp <- getTemporaryDirectory
    (home, handle) <- openTempFile tmp "tersus-parser-bootstrap-test"
    hClose handle
    removeFile home
    createDirectory home
    let seed = home </> "wrong-seed.ll"
    writeFile seed "not the pinned emitter seed\n"
    (withEnv "XDG_CACHE_HOME" (Just home) $
        withEnv "TERSUS_SEED_FILE" (Just seed) $
        withEnv "TERSUS_PARSER" Nothing $ do
            source <- pure ("return " ++ show (17 :: Int) ++ ";")
            result <- evaluate (compileSource source)
            pure $ case result of
                Error err -> testAssertErrorContains "Parser tool failure: Native parser bootstrap failed:" (Error err :: Result () String)
                Ok _ -> Just "the default whole Pipeline hid a failed native parser build")
        `finally` removeDirectoryRecursive home
