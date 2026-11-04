module ParserSeed
    ( parseFileWith
    , parseFileNative
    , parseFileWithTool
    , fileResponse
    , responseWithTool
    , parseImportPrefix
    , parseDeclarationNames
    , toolFailure
    , failure
    , stageParseError
    ) where

import System.IO.Unsafe (unsafePerformIO)
import System.Exit (ExitCode (..))
import Data.List (isPrefixOf)
import qualified FileParserProtocol as File
import Native (runWithInputFull)
import ParsedFile (Decls, ParsedFile, Import)
import Seed (cachedParserSeed)
import Utils

{-# NOINLINE parseFileWith #-}
parseFileWith :: Decls -> String -> Either String (ParsedFile, Decls)
parseFileWith declarations source = unsafePerformIO (parseFileNative declarations source)

parseFileNative :: Decls -> String -> IO (Either String (ParsedFile, Decls))
parseFileNative = parseFileWithTool cachedParserSeed

parseFileWithTool :: IO (Result FilePath String) -> Decls -> String -> IO (Either String (ParsedFile, Decls))
parseFileWithTool makeTool declarations source = responseWithTool makeTool fileResponse (File.writeFileRequest declarations source)

{-# NOINLINE parseImportPrefix #-}
parseImportPrefix :: String -> Either String [Import]
parseImportPrefix source = unsafePerformIO (responseWithTool cachedParserSeed (replyResponse "imports" File.readImportPrefix) (File.writeImportPrefixRequest source))

{-# NOINLINE parseDeclarationNames #-}
parseDeclarationNames :: String -> Either String [String]
parseDeclarationNames source = unsafePerformIO (responseWithTool cachedParserSeed (replyResponse "names" File.readDeclarationNames) (File.writeDeclarationNamesRequest source))

responseWithTool :: IO (Result FilePath String) -> (ExitCode -> String -> String -> Either String a) -> Result String String -> IO (Either String a)
responseWithTool makeTool respond request = case request of
    Error e -> pure (Left (failure e))
    Ok input -> do
        tool <- makeTool
        case tool of
            Error e -> pure (Left (failure e))
            Ok exe -> do
                (code, out, errors) <- runWithInputFull exe input
                pure (respond code out errors)

fileResponse :: ExitCode -> String -> String -> Either String (ParsedFile, Decls)
fileResponse = replyResponse "file" File.readParsedFile

replyResponse :: String -> (String -> Result a String) -> ExitCode -> String -> String -> Either String a
replyResponse label readReply code out errors = case code of
    ExitFailure n -> Left (failure ("native parser exited " ++ show n ++ ": " ++ trimEnd (decodeUtf8 errors)))
    ExitSuccess
        | out == "1\n" && not (null errors) -> Left (trimEnd (decodeUtf8 errors))
        | otherwise -> case readReply out of
            Error e -> Left (failure ("invalid " ++ label ++ " reply: " ++ e))
            Ok parsed -> Right parsed

failure :: String -> String
failure e = "Parser tool failure: " ++ e

toolFailure :: String -> Bool
toolFailure = isPrefixOf "Parser tool failure:"

stageParseError :: String -> String
stageParseError e | toolFailure e = e
                  | otherwise = "Parse error: " ++ e

trimEnd :: String -> String
trimEnd = reverse . dropWhile (== '\n') . reverse
