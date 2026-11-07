module TersusParser
    ( parseSource
    , parseSourceParts
    , parseFileWith
    , parseFileNative
    , parserExecutable
    , parseFileInterpreted
    , toolParseSource
    , runParserTool
    , runParserToolInterpreted
    , parserToolInput
    , parserResponse
    , emitParserIr
    , ownedParserProgram
    , parseWithEquality
    , parserKey
    ) where

import Control.Exception (evaluate)
import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import System.Environment (lookupEnv)
import System.Directory (doesFileExist)
import System.Exit (ExitCode (..))
import System.IO.Unsafe (unsafePerformIO)

import qualified AstData as A
import qualified FileParserProtocol as File
import qualified ParsedFile as FileData
import qualified ParserSeed
import SourceParse (SourceParts, parseSourcePartsWith, parseWithEqualityWith)
import Mir (Program)
import MirEval (MirValue (..), Outcome (..), RunEnv (..), runProgramEnv)
import MirHousekeeping (cachedParser, insertOwnership, nativeProgram, parserKey, parserIr, toolProgram)
import Native (runWithInputFull)
import Seed (cachedParserSeed)
import Syntax (Statement)
import ValidatorNative (cachedBootstrapEmitter)
import Utils

parseSource :: String -> Result [Statement] String
parseSource source = mapResult (\(_, library, body) -> library ++ body) (parseSourceParts True source)

parseSourceParts :: Bool -> String -> Result SourceParts String
parseSourceParts reserving source = unsafePerformIO $ do
    selected <- parserBackend
    pure $ case selected of
        Left e -> Error e
        Right _ -> parseSourcePartsWith parseFileWith reserving source

parseWithEquality :: String -> Either String [Statement]
parseWithEquality = parseWithEqualityWith parseFileWith

parserBackend :: IO (Either String String)
parserBackend = do
    selected <- lookupEnv "TERSUS_PARSER"
    pure $ case selected of
        Nothing -> Right "native"
        Just name | name `elem` ["native", "interpreted"] -> Right name
        Just name -> Left ("Unknown TERSUS_PARSER backend: " ++ name ++ "; expected native or interpreted")

parseFileWith :: FileData.Decls -> String -> Either String (FileData.ParsedFile, FileData.Decls)
parseFileWith declarations source = unsafePerformIO $ do
    selected <- parserBackend
    case selected of
        Left e -> pure (Left e)
        Right "interpreted" -> parseFileInterpreted declarations source
        Right _ -> parseFileNative declarations source

parseFileNative :: FileData.Decls -> String -> IO (Either String (FileData.ParsedFile, FileData.Decls))
parseFileNative = ParserSeed.parseFileWithTool parserExecutable

parserExecutable :: IO (Result FilePath String)
parserExecutable = do
    tool <- parserTool
    pure $ case tool of
        ToolNative exe -> Ok exe
        ToolFailed e -> Error e
        _ -> Error "native parser tool is not native"

parseFileInterpreted :: FileData.Decls -> String -> IO (Either String (FileData.ParsedFile, FileData.Decls))
parseFileInterpreted declarations source = case File.writeFileRequest declarations source of
    Error e -> pure (Left (failure e))
    Ok input -> do
        tool <- interpretedToolOnce
        answer <- runTool tool input
        pure $ case answer of
            Left e -> Left e
            Right text -> case File.readParsedFile text of
                Error e -> Left (failure ("invalid file reply: " ++ e))
                Ok parsed -> Right parsed

-- The exact production source orchestration with the native parser.
toolParseSource :: String -> IO (Either String String)
toolParseSource source = do
    parsed <- evaluate (parseSourcePartsWith (\declared text -> unsafePerformIO (parseFileNative declared text)) True source)
    pure $ case parsed of
        Error e -> Left e
        Ok (_, library, body) -> case A.writeParsed (library ++ body) of
            Error e -> Left (failure e)
            Ok text -> Right text

-- The parsed-AST stream protocol remains useful for exact stdout tests and the tiny
-- interpreted smoke set; the file protocol transports imports and declaration seeds.
parserToolInput :: Bool -> [String] -> String
parserToolInput locating segments =
    "tersus-parse 1\n" ++ (if locating then "1" else "0") ++ " " ++ show (length segments) ++ "\n" ++ concatMap segment segments
  where
    segment text = let bytes = encodeUtf8 text in show (length bytes) ++ "\n" ++ bytes

runParserTool :: Bool -> [String] -> IO (Either String String)
runParserTool = streamWithTool parserTool

runParserToolInterpreted :: Bool -> [String] -> IO (Either String String)
runParserToolInterpreted = streamWithTool interpretedToolOnce

streamWithTool :: IO Tool -> Bool -> [String] -> IO (Either String String)
streamWithTool makeTool locating segments = do
    tool <- makeTool
    answer <- runTool tool (parserToolInput locating segments)
    pure $ answer >>= \text -> parserResponse ExitSuccess text ""

runTool :: Tool -> String -> IO (Either String String)
runTool tool input = case tool of
    ToolFailed e -> pure (Left (failure e))
    ToolNative exe -> do
        (code, out, errors) <- runWithInputFull exe input
        pure $ case code of
            ExitFailure n -> Left (failure ("native parser exited " ++ show n ++ ": " ++ trimEnd (decodeUtf8 errors)))
            ExitSuccess
                | out == "1\n" && not (null errors) -> Left (trimEnd (decodeUtf8 errors))
                | otherwise -> Right out
    ToolInterpreted program -> pure $ case runInterpreted program input of
        Error e -> Left (failure e)
        Ok (out, errors, value)
            | value == Just (MInt 1) -> Left (trimEnd (decodeUtf8 errors))
            | value == Nothing -> Right out
            | otherwise -> Left (failure ("unexpected return value: " ++ show value))

parserResponse :: ExitCode -> String -> String -> Either String String
parserResponse code out errors = case code of
    ExitFailure n -> Left (failure ("native parser exited " ++ show n ++ ": " ++ trimEnd (decodeUtf8 errors)))
    ExitSuccess
        | take 11 out == "tersus-ast " -> case A.readParsed out of
            Ok _ -> Right out
            Error e -> Left (failure ("invalid AstData: " ++ e))
        | out == "1\n" && not (null errors) -> Left (trimEnd (decodeUtf8 errors))
        | otherwise -> Left (failure ("no valid AST or refusal: " ++ show (take 80 out) ++ "; " ++ trimEnd (decodeUtf8 errors)))

failure :: String -> String
failure = ParserSeed.failure

data Tool = ToolNative FilePath | ToolInterpreted Program | ToolFailed String

{-# NOINLINE toolBox #-}
toolBox :: MVar (Maybe Tool)
toolBox = unsafePerformIO (newMVar Nothing)

parserTool :: IO Tool
parserTool = modifyMVar toolBox $ \made -> do
    live <- case made of
        Just tool@(ToolNative exe) -> do
            present <- doesFileExist exe
            pure (if present then Just tool else Nothing)
        _ -> pure Nothing
    tool <- maybe nativeTool pure live
    let keep = case tool of ToolNative _ -> Just tool; _ -> Nothing
    pure (keep, tool)

{-# NOINLINE interpretedBox #-}
interpretedBox :: MVar (Maybe Tool)
interpretedBox = unsafePerformIO (newMVar Nothing)

interpretedToolOnce :: IO Tool
interpretedToolOnce = modifyMVar interpretedBox $ \made -> case made of
    Just tool -> pure (made, tool)
    Nothing -> do
        seed <- cachedParserSeed
        let tool = case seed of
                Error e -> ToolFailed e
                Ok _ -> case validatedParserProgram of
                    Error e -> ToolFailed e
                    Ok program -> ToolInterpreted program
        let keep = case tool of ToolInterpreted _ -> Just tool; _ -> Nothing
        pure (keep, tool)

nativeTool :: IO Tool
nativeTool = do
    seed <- cachedParserSeed
    case seed of
        Error e -> pure (ToolFailed e)
        Ok _ -> do
            bootstrap <- cachedBootstrapEmitter
            made <- case bootstrap of Error e -> pure (Error e); Ok _ -> cachedParser
            pure $ case made of
                Ok exe -> ToolNative exe
                Error e -> ToolFailed ("Native parser bootstrap failed: " ++ e)

emitParserIr :: IO (Result String String)
emitParserIr = parserIr

{-# NOINLINE validatedParserProgram #-}
validatedParserProgram :: Result Program String
validatedParserProgram = toolProgram "lib/parser/parser.tersus"

ownedParserProgram :: Result Program String
ownedParserProgram = validatedParserProgram `bindResult` \program ->
    nativeProgram program `bindResult` insertOwnership

runInterpreted :: Program -> String -> Result (String, String, Maybe MirValue) String
runInterpreted program input = case runProgramEnv RunEnv{envArgs = [], envInput = input, envFile = const Nothing} program of
    Error e -> Error ("Evaluation failed: " ++ e)
    Ok outcome -> Ok (outStdout outcome, outStderr outcome, outValue outcome)

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse
