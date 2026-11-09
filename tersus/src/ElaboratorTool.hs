-- An elaborator executable (the elaborator written in Tersus, lib/elaborate) as the compiler's elaborator: the
-- request (ElaborateRequest) on its standard input, the response on its standard output.
module ElaboratorTool
    ( runElaborator
    , nativeElaborator
    , frontendToolFailure
    ) where

import Control.Concurrent (forkIO, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (IOException, finally, try)
import qualified Data.ByteString.Char8 as B
import Data.List (isInfixOf)
import System.Exit (ExitCode (..))
import System.IO (hClose, hSetBinaryMode)
import System.IO.Unsafe (unsafePerformIO)
import System.Process (CreateProcess (..), StdStream (..), proc, waitForProcess, withCreateProcess)

import ElaborateRequest
import Native (raiseStack)
import Utils

runElaborator :: FilePath -> Request -> IO (Result Response String)
runElaborator exe rq = case writeRequest rq of
    Error e -> pure (Error e)
    Ok text -> do
        -- (the elaborator recurses over the nesting of expressions, deeper than a default stack allows for a deep one;
        -- the data is ASCII, so it is passed as bytes rather than through the locale's decoding of a String)
        (code, out, err) <- withCreateProcess (proc "/bin/sh" ["-c", raiseStack, exe]){std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe} $
            \hin' hout' herr' ph -> case (hin', hout', herr') of
                (Just hin, Just hout, Just herr) -> do
                    mapM_ (`hSetBinaryMode` True) [hin, hout, herr]
                    outVar <- newEmptyMVar
                    errVar <- newEmptyMVar
                    _ <- forkIO (B.hGetContents hout >>= putMVar outVar)
                    _ <- forkIO (B.hGetContents herr >>= putMVar errVar)
                    _ <- try (B.hPut hin (B.pack text) `finally` hClose hin) :: IO (Either IOException ())
                    out <- takeMVar outVar
                    err <- takeMVar errVar
                    code <- waitForProcess ph
                    pure (code, out, err)
                _ -> pure (ExitFailure 1, B.empty, B.pack "no pipes to the elaborator")
        pure $ case code of
            ExitSuccess -> readResponseBytes (B.lines out)
            ExitFailure n -> Error ("exit " ++ show n ++ ": " ++ take 400 (B.unpack err))

-- The executable as the compiler's elaborator. An answer it cannot give refuses the module, with a reason that says
-- the tool failed, rather than being taken for the program's fault or answered by another elaborator.
{-# NOINLINE nativeElaborator #-}
nativeElaborator :: FilePath -> Elaborator
nativeElaborator exe rq = unsafePerformIO $ do
    answer <- runElaborator exe rq
    pure $ case answer of
        Ok response -> response
        Error e -> Refused (toolFailurePrefix ++ e)

toolFailurePrefix :: String
toolFailurePrefix = "Elaborator tool failure: "

frontendToolFailure :: String -> Bool
frontendToolFailure = isInfixOf toolFailurePrefix
