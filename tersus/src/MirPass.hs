module MirPass (programData, runPassWith, runMonoOwnershipPassWith) where

import Data.Char (isSpace)
import Data.List (isPrefixOf)
import qualified Data.Set as Set
import System.Exit (ExitCode (..))
import Mir (Lowered (..), Program)
import MirData (readLowered, readProgram, writeLowered)
import MirOwnershipData (restoreOwnership)
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

runMonoOwnershipPassWith :: IO (Result FilePath String) -> String -> IO (Result Program String)
runMonoOwnershipPassWith tool input = do
    made <- tool
    case made of
        Error e -> pure (Error e)
        Ok executable -> do
            (code, out, errors) <- runWithInputFull executable input
            pure $ case monoReceipt out of
                Nothing -> case code of
                    ExitFailure n -> Error ("the monomorphization tool exited with " ++ show n ++ ": " ++ trimEnd (decodeUtf8 errors))
                    ExitSuccess
                        | trim out == "1" -> Error (trimEnd (decodeUtf8 errors))
                        | not (null (trim errors)) -> Error ("the monomorphization tool reported: " ++ trimEnd (decodeUtf8 errors))
                        | otherwise -> stage "the monomorphization tool wrote unreadable MIR3: " (mapResult lowProgram (readLowered out)) `bindResult` \_ -> Error "the ownership tool did not write MIR version 2"
                Just (mono, owned) ->
                    stage "the monomorphization tool wrote unreadable MIR3: " (mapResult lowProgram (readLowered mono)) `bindResult` \original ->
                        case code of
                            ExitFailure n -> Error ("the ownership tool exited with " ++ show n ++ ": " ++ trimEnd errors)
                            ExitSuccess
                                | trim owned == "1" -> Error ("the ownership tool refused ownership: " ++ trimEnd errors)
                                | not (null (trim errors)) -> Error ("the ownership tool reported: " ++ trimEnd errors)
                                | take 1 (lines owned) /= ["tersus-mir 2"] -> Error "the ownership tool did not write MIR version 2"
                                | otherwise -> stage "the ownership tool wrote unreadable MIR: " (readProgram owned) `bindResult` restoreOwnership original

monoReceipt :: String -> Maybe (String, String)
monoReceipt out = case break (isPrefixOf "data ") (lines out) of
    (records, header : remaining)
        | take 1 records == ["tersus-mir 3"] -> case words header of
            ["data", digits] -> case reads digits :: [(Integer, String)] of
                [(count, "")] | count >= 0 && show count == digits && header == "data " ++ digits && count <= toInteger (length remaining) ->
                    let (payload, owned) = splitAt (fromInteger count) remaining
                     in Just (unlines (records ++ header : payload), unlines owned)
                _ -> Nothing
            _ -> Nothing
    _ -> Nothing

trim :: String -> String
trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse

stage :: String -> Result a String -> Result a String
stage prefix (Error e) = Error (prefix ++ e)
stage _ ok = ok
