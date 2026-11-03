module TersusParser
    ( parseSource
    , parseSourceParts
    , parseFileWith
    , parseFileNative
    , parseFileInterpreted
    , toolParseSource
    , runParserTool
    , runParserToolInterpreted
    , parserToolInput
    , parserResponse
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Data.List (intercalate, isPrefixOf)
import System.Environment (lookupEnv)
import System.Exit (ExitCode (..))
import System.IO.Unsafe (unsafePerformIO)

import qualified AstData as A
import qualified Compile
import qualified FileParserProtocol as File
import qualified Parse as Oracle
import Hash (fingerprint)
import LlvmRuntime (runtimeSource)
import Mir (Program)
import MirData (writeProgram)
import MirEval (MirValue (..), Outcome (..), RunEnv (..), runProgramEnv)
import MirHousekeeping (cachedEmitter, listLibrary)
import MirLists (lowerLists)
import MirOwnership (expandRefWrites, insertOwnership)
import MirValidate (validateProgram)
import Native (buildExecutable, cachedProgram, runWithInput, runWithInputFull)
import PreludeSource (parserSource)
import Seed (emitterHash)
import Syntax (Statement)
import Utils

-- Compile and the default Modules loader remain the one-way bootstrap/oracle path.
-- Only an explicit haskell setting selects the oracle for user source. Native failures
-- are errors, never a reason to switch parser implementations.
parseSource :: String -> Result [Statement] String
parseSource source = mapResult (\(_, library, body) -> library ++ body) (parseSourceParts True source)

parseSourceParts :: Bool -> String -> Result Compile.SourceParts String
parseSourceParts reserving source = unsafePerformIO $ do
    selected <- parserBackend
    case selected of
        Left e -> pure (Error e)
        Right "haskell" -> pure (Compile.parseSourceParts reserving source)
        Right "interpreted" -> sourcePartsWith parseFileInterpreted reserving source
        Right _ -> sourcePartsWith parseFileNative reserving source

parserBackend :: IO (Either String String)
parserBackend = do
    selected <- lookupEnv "TERSUS_PARSER"
    pure $ case selected of
        Nothing -> Right "native"
        Just name | name `elem` ["native", "interpreted", "haskell"] -> Right name
        Just name -> Left ("Unknown TERSUS_PARSER backend: " ++ name ++ "; expected native, interpreted or haskell")

-- Frozen libraries and their declarations reuse Compile's canonical library cache.
-- Both per-run source readings, including constructor shadowing and the plain probe
-- retry, are performed by the selected Tersus parser, not by the Haskell parser.
sourcePartsWith :: (Oracle.Decls -> String -> IO (Either String (Oracle.ParsedFile, Oracle.Decls))) -> Bool -> String -> IO (Result Compile.SourceParts String)
sourcePartsWith readSourceFile reserving source = do
    seeded <- readSourceFile (Oracle.locating Compile.probeDecls) source
    probed <- case seeded of
        Right parsed -> pure (Right parsed)
        Left e | toolFailure e -> pure (Left e)
        Left e -> do
            plain <- readSourceFile (Oracle.locating Oracle.emptyDecls) source
            pure $ case plain of
                Right parsed -> Right parsed
                Left plainError | toolFailure plainError -> Left plainError
                Left _ -> Left e
    case probed of
        Left e -> pure (Error (stageParseError e))
        Right (probedFile, _) -> do
            let names = map fst (Compile.librariesFor (Oracle.fileBody probedFile))
            case Compile.parsedLibraries names of
                Left e -> pure (Error e)
                Right (library, declarations) -> do
                    parsed <- readSourceFile (Oracle.locating declarations) source
                    pure $ case parsed of
                        Left e -> Error (stageParseError e)
                        Right (Oracle.ParsedFile imports body, _)
                            | not (null imports) -> Error ("imports are not linked yet: " ++ intercalate ", " (map (Oracle.renderPath . Oracle.importPath) imports))
                            | reserving, Just name <- Compile.reservedName body -> Error (Compile.reservedError name)
                            | otherwise -> Ok (names, library, body)
  where
    stageParseError e | toolFailure e = e
                     | otherwise = "Parse error: " ++ e

parseFileWith :: Oracle.Decls -> String -> Either String (Oracle.ParsedFile, Oracle.Decls)
parseFileWith declarations source = unsafePerformIO $ do
    selected <- parserBackend
    case selected of
        Left e -> pure (Left e)
        Right "haskell" -> pure $ either (Left . show) Right (Oracle.parseFileWith declarations source)
        Right "interpreted" -> parseFileInterpreted declarations source
        Right _ -> parseFileNative declarations source

parseFileNative :: Oracle.Decls -> String -> IO (Either String (Oracle.ParsedFile, Oracle.Decls))
parseFileNative = fileWithTool parserTool

parseFileInterpreted :: Oracle.Decls -> String -> IO (Either String (Oracle.ParsedFile, Oracle.Decls))
parseFileInterpreted = fileWithTool interpretedToolOnce

fileWithTool :: IO Tool -> Oracle.Decls -> String -> IO (Either String (Oracle.ParsedFile, Oracle.Decls))
fileWithTool makeTool declarations source = case File.writeFileRequest declarations source of
    Error e -> pure (Left (failure e))
    Ok input -> do
        tool <- makeTool
        answer <- runTool tool input
        pure $ case answer of
            Left e -> Left e
            Right text -> case File.readParsedFile text of
                Error e -> Left (failure ("invalid file reply: " ++ e))
                Ok parsed -> Right parsed

-- An explicitly native full-source parity entry point, independent of the oracle flag.
toolParseSource :: String -> IO (Either String String)
toolParseSource source = do
    parsed <- sourcePartsWith parseFileNative True source
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
failure e = "Parser tool failure: " ++ e

toolFailure :: String -> Bool
toolFailure = isPrefixOf "Parser tool failure:"

data Tool = ToolNative FilePath | ToolInterpreted Program | ToolFailed String

{-# NOINLINE toolBox #-}
toolBox :: MVar (Maybe Tool)
toolBox = unsafePerformIO (newMVar Nothing)

parserTool :: IO Tool
parserTool = modifyMVar toolBox $ \made -> case made of
    Just tool -> pure (made, tool)
    Nothing -> do
        tool <- nativeTool
        pure (Just tool, tool)

{-# NOINLINE interpretedBox #-}
interpretedBox :: MVar (Maybe Tool)
interpretedBox = unsafePerformIO (newMVar Nothing)

interpretedToolOnce :: IO Tool
interpretedToolOnce = modifyMVar interpretedBox $ \made -> case made of
    Just tool -> pure (made, tool)
    Nothing -> let tool = case validatedParserProgram of
                      Error e -> ToolFailed e
                      Ok program -> ToolInterpreted program
               in pure (Just tool, tool)

nativeTool :: IO Tool
nativeTool = do
    made <- cachedProgram "tersus-parser" parserHash "the parser written in Tersus" buildTool
    pure $ case made of
        Ok exe -> ToolNative exe
        Error e -> ToolFailed ("Native parser bootstrap failed: " ++ e)

buildTool :: FilePath -> IO (Result () String)
buildTool output = do
    emitter <- cachedEmitter
    case emitter of
        Error e -> pure (Error e)
        Ok exe -> case ownedParserProgram of
            Error e -> pure (Error e)
            Ok program -> do
                ir <- runWithInput exe (writeProgram program)
                case ir of
                    Error e -> pure (Error e)
                    Ok text -> buildExecutable output text

{-# NOINLINE validatedParserProgram #-}
validatedParserProgram :: Result Program String
validatedParserProgram =
    Compile.lowerSource True parserSource `bindResult` \program ->
        stage "Validation failed: " (validateProgram program) `bindResult` \_ -> Ok program

ownedParserProgram :: Result Program String
ownedParserProgram = validatedParserProgram `bindResult` \program ->
    Ok (insertOwnership (lowerLists listLibrary (expandRefWrites program)))

runInterpreted :: Program -> String -> Result (String, String, Maybe MirValue) String
runInterpreted program input = case runProgramEnv RunEnv{envArgs = [], envInput = input, envFile = const Nothing} program of
    Error e -> Error ("Evaluation failed: " ++ e)
    Ok outcome -> Ok (outStdout outcome, outStderr outcome, outValue outcome)

parserHash :: String
parserHash = fingerprint [emitterHash, parserSource, runtimeSource]

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
