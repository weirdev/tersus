module MirPass (programData, runPassWith) where

import Data.Char (isSpace)
import qualified Data.Set as Set
import System.Exit (ExitCode (..))
import Mir (Lowered (..), Program)
import MirData (readLowered, writeLowered)
import Native (runWithInputFull)
import Utils

programData :: Program -> Result String String
programData program = writeLowered (Lowered program Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty [])

runPassWith :: IO (Result FilePath String) -> String -> String -> IO (Result Program String)
runPassWith tool label input = do
    made <- tool
    case made of
        Error e -> pure (Error e)
        Ok executable -> do
            (code, out, errors) <- runWithInputFull executable input
            pure $ case code of
                ExitFailure n -> Error (label ++ " exited with " ++ show n ++ ": " ++ trimEnd (decodeUtf8 errors))
                ExitSuccess
                    | trim out == "1" -> Error (trimEnd (decodeUtf8 errors))
                    | not (null (trim errors)) -> Error (label ++ " reported: " ++ trimEnd (decodeUtf8 errors))
                    | otherwise -> stage (label ++ " wrote unreadable MIR3: ") (mapResult lowProgram (readLowered out))

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse

stage :: String -> Result a String -> Result a String
stage prefix (Error e) = Error (prefix ++ e)
stage _ ok = ok
