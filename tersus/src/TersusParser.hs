module TersusParser
    ( parseSource
    , runParserTool
    , runParserToolInterpreted
    , parserToolInput
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Exception (finally)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List (isPrefixOf)
import System.Environment (lookupEnv)
import System.IO (hPutStrLn, stderr)
import System.IO.Unsafe (unsafePerformIO)

import qualified AstData as A
import qualified Compile
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
import Syntax (Expression (..), Statement (..), Value (..))
import Types ()
import Utils

-- The production parser is the one written in Tersus (examples/parser.tersus), run by this host as
-- MirHousekeeping runs the checker and the eraser written in Tersus: built with clang from the seed
-- when it can be, and kept in the cache; interpreted by the MIR executor where it cannot. It is given
-- the program as segments (the libraries Compile puts in front, then the program itself) and writes
-- the AST as data (AstData), which this module reads back. The Haskell parser (Compile.parseSource)
-- stays as the oracle: TERSUS_PARSER=haskell selects it directly, and any failure of the tool falls
-- back to it with a note on the standard error. Compile.parseSource itself is unchanged, so the tool
-- is always built by the bootstrap path.

parseSource :: String -> Result [Statement] String
parseSource source = unsafePerformIO (parseSourceIO source)

parseSourceIO :: String -> IO (Result [Statement] String)
parseSourceIO source = do
    flag <- lookupEnv "TERSUS_PARSER"
    if flag == Just "haskell"
        then pure (Compile.parseSource source)
        else do
            tool <- parserTool
            outcome <- case tool of
                ToolFailed e -> pure (Error e)
                ToolNative exe -> do
                    (_, out, errors) <- runWithInputFull exe input
                    pure (verdict out errors)
                ToolInterpreted program -> pure $ case runInterpreted program input of
                    Error e -> Error e
                    Ok (out, errors, value)
                        | value == Just (MInt 1) -> Error (trimEnd errors)
                        | otherwise -> verdict out errors
            case outcome of
                Ok text -> case A.readParsed text of
                    Ok statements -> pure (reservedCheck statements)
                    Error e -> fallback ("the parser written in Tersus wrote what cannot be read back: " ++ e)
                Error e -> fallback ("the parser written in Tersus refused: " ++ e)
  where
    input = parserToolInput True (Compile.librarySourcesFor source ++ [source])
    verdict :: String -> String -> Result String String
    verdict out errors
        | not (null (trim errors)) && null (trim out) = Error (trimEnd errors)
        | take 11 out == "tersus-ast " = Ok out
        | otherwise = Error (trimEnd errors)
    fallback why = do
        hPutStrLn stderr ("tersus: " ++ why ++ "; using the Haskell parser")
        pure (Compile.parseSource source)
    reservedCheck statements = case reservedName statements of
        Just name -> Error ("Type error: " ++ name ++ " is reserved: native code makes a list of the struct StdList and the functions stdList... of lib/lists.tersus, and a Box of the struct StdBox and the functions stdBox... of lib/box.tersus, so a program does not declare names like them")
        Nothing -> Ok statements

-- A name the program declares that native code uses for lists (Compile.reservedName, over the whole
-- program: the libraries Compile puts in front declare no such name)
reservedName :: [Statement] -> Maybe String
reservedName statements = case [name | statement <- statements, name <- declared statement, reserved name] of
    name : _ -> Just name
    [] -> Nothing
  where
    declared statement = case statement of
        Assign name (Val VFunct{}) -> [name]
        StructDef name _ _ _ -> [name]
        EnumDef name _ -> [name]
        TraitDef name _ _ -> [name]
        BoundedDef _ (Assign name _) -> [name]
        _ -> []
    reserved name = name `elem` ["StdList", "StdBox"] || "stdList" `isPrefixOf` name || "stdBox" `isPrefixOf` name

-- The tool's input, exactly as examples/parser.tersus reads it: a header line, the locating flag and
-- the segment count, then for each segment a byte-count line and that many raw bytes.
parserToolInput :: Bool -> [String] -> String
parserToolInput locating segments =
    "tersus-parse 1\n"
        ++ (if locating then "1" else "0")
        ++ " "
        ++ show (length segments)
        ++ "\n"
        ++ concatMap segment segments
  where
    segment text = let bytes = encodeUtf8 text in show (length bytes) ++ "\n" ++ bytes

-- Runs the tool over segments as the pipeline gives them, for the tests: the AST as data, or the
-- tool's own error text.
runParserTool :: Bool -> [String] -> IO (Either String String)
runParserTool locating segments = do
    tool <- parserTool
    case tool of
        ToolFailed e -> pure (Left e)
        ToolNative exe -> do
            (_, out, errors) <- runWithInputFull exe (parserToolInput locating segments)
            pure $ if take 11 out == "tersus-ast " then Right out else Left (trimEnd errors)
        ToolInterpreted program -> pure $ case runInterpreted program (parserToolInput locating segments) of
            Error e -> Left e
            Ok (out, errors, value)
                | value == Just (MInt 1) -> Left (trimEnd errors)
                | otherwise -> Right out

-- Runs the tool interpreted (no native build), for the tests of small programs
runParserToolInterpreted :: Bool -> [String] -> IO (Either String String)
runParserToolInterpreted locating segments = do
    tool <- interpretedToolOnce
    case tool of
        ToolFailed e -> pure (Left e)
        ToolInterpreted program -> pure $ case runInterpreted program (parserToolInput locating segments) of
            Error e -> Left e
            Ok (out, errors, value)
                | value == Just (MInt 1) -> Left (trimEnd errors)
                | otherwise -> Right out
        ToolNative _ -> pure (Left "the interpreted parser tool was not built")

data Tool
    = ToolNative FilePath
    | ToolInterpreted Program
    | ToolFailed String

{-# NOINLINE toolBox #-}
toolBox :: MVar (Maybe Tool)
toolBox = unsafePerformIO (newMVar Nothing)

{-# NOINLINE buildingRef #-}
buildingRef :: IORef Bool
buildingRef = unsafePerformIO (newIORef False)

parserTool :: IO Tool
parserTool = do
    building <- readIORef buildingRef
    if building
        then interpretedToolOnce
        else modifyMVar toolBox $ \made ->
            case made of
                Just tool -> pure (made, tool)
                Nothing -> do
                    writeIORef buildingRef True
                    tool <- nativeTool `finally` writeIORef buildingRef False
                    pure (Just tool, tool)

{-# NOINLINE interpretedBox #-}
interpretedBox :: MVar (Maybe Tool)
interpretedBox = unsafePerformIO (newMVar Nothing)

interpretedToolOnce :: IO Tool
interpretedToolOnce = modifyMVar interpretedBox $ \made ->
    case made of
        Just tool -> pure (made, tool)
        Nothing -> do
            tool <- interpretedTool
            pure (Just tool, tool)

nativeTool :: IO Tool
nativeTool = do
    made <- cachedProgram "tersus-parser" parserHash "the parser written in Tersus" buildTool
    case made of
        Ok exe -> pure (ToolNative exe)
        Error _ -> interpretedToolOnce

interpretedTool :: IO Tool
interpretedTool = pure $ case Compile.lowerSource True parserSource of
    Error e -> ToolFailed e
    Ok program -> case validateProgram program of
        Error e -> ToolFailed e
        Ok _ -> ToolInterpreted program

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

ownedParserProgram :: Result Program String
ownedParserProgram =
    Compile.lowerSource True parserSource `bindResult` \program ->
        stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
            Ok (insertOwnership (lowerLists listLibrary (expandRefWrites program)))

runInterpreted :: Program -> String -> Result (String, String, Maybe MirValue) String
runInterpreted program input = case runProgramEnv RunEnv{envArgs = [], envInput = input, envFile = const Nothing} program of
    Error e -> Error ("Evaluation failed: " ++ e)
    Ok outcome -> Ok (outStdout outcome, outStderr outcome, outValue outcome)

parserHash :: String
parserHash = fingerprint [emitterHash, parserSource, runtimeSource]

trim :: String -> String
trim = reverse . dropWhile (== '\n') . reverse . dropWhile (== '\n')

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
