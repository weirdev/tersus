module MirPass (programData, runPassWith, validationMonoRequest, runMonoOwnershipPassWith) where

import Data.Char (isSpace)
import Data.List (isPrefixOf)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.Exit (ExitCode (..))
import Mir (Lowered (..), Program (..))
import MirCopiesNameProfile (nameProfilePrefix)
import MirData (readCheckedLowered, readProgram, writeCheckedLowered)
import Types (OwnershipFacts (..), tupleGeneric)
import MirOwnershipData (restoreOwnership)
import Native (runWithInputFull)
import Utils

-- The program as the native passes are given it, with its checked providers and facts (MirData.writeCheckedLowered)
programData :: Program -> Result String String
programData program = writeCheckedLowered (Lowered program Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty [])

validationMonoRequest :: String -> String
validationMonoRequest input = "pass validation-mono\nprogram " ++ show (length (lines input)) ++ "\n" ++ input ++ nameProfilePrefix [input]

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
                    | otherwise -> stage (label ++ " wrote unreadable MIR3: ") (mapResult lowProgram (readCheckedLowered out))

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
                        | otherwise -> stage "the monomorphization tool wrote unreadable MIR3: " (mapResult lowProgram (readCheckedLowered out)) `bindResult` \_ -> Error "the ownership tool did not write MIR version 2"
                Just (mono, owned) -> case mapResult lowProgram (readCheckedLowered mono) of
                    Error e -> case code of
                        ExitFailure n -> Error ("the monomorphization tool exited with " ++ show n ++ ": " ++ trimEnd (decodeUtf8 errors))
                        ExitSuccess
                            | not (null (trim errors)) -> Error ("the monomorphization tool reported: " ++ trimEnd (decodeUtf8 errors))
                            | otherwise -> Error ("the monomorphization tool wrote unreadable MIR3: " ++ e)
                    Ok original -> case code of
                        ExitFailure n -> Error ("the ownership tool exited with " ++ show n ++ ": " ++ trimEnd errors)
                        ExitSuccess
                            | trim owned == "1" -> Error ("the ownership tool refused ownership: " ++ trimEnd errors)
                            | not (null (trim errors)) -> Error ("the ownership tool reported: " ++ trimEnd errors)
                            | take 1 (lines owned) /= ["tersus-mir 2"] -> Error "the ownership tool did not write MIR version 2"
                            | otherwise -> stage "the ownership tool wrote unreadable MIR: " (readProgram owned) `bindResult` \output ->
                                agreeing original output `bindResult` \_ -> restoreOwnership original output

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

-- The owned program's checked facts are the receipt's for the types the receipt declares (its facts of other types are carried for
-- what follows, and the owned program declares none of them): each declared type has the receipt's row, as it is, or, for a
-- tuple the receipt has no row of, none; and its storage is the receipt's
agreeing :: Program -> Program -> Result () String
agreeing receipt owned = case (progOwnership receipt, progOwnership owned) of
    (Nothing, Nothing) -> Ok ()
    (Just facts, Just rows)
        | Map.lookup "List" (progProtocols owned) /= Map.lookup "List" (progProtocols receipt) || Map.lookup "Box" (progProtocols owned) /= Map.lookup "Box" (progProtocols receipt) ->
            Error "the ownership tool wrote another storage than its receipt has"
        | Map.keysSet rows /= declared -> Error "the ownership tool wrote checked facts of other types than its receipt declares"
        | not (all (agrees facts rows) (Set.toList declared)) -> Error "the ownership tool wrote other checked facts than its receipt has"
        | otherwise -> Ok ()
    _ -> Error "the ownership tool and its receipt disagree on whether the program has checked facts"
  where
    declared = Map.keysSet (progTypes receipt)
    agrees facts rows owner = case (Map.lookup owner facts, Map.lookup owner rows) of
        (Just expected, Just row) -> row == expected
        (Nothing, Just row) -> tupleGeneric (takeWhile (/= '<') owner) /= Nothing && row == OwnershipFacts Nothing Nothing Nothing Nothing
        _ -> False
