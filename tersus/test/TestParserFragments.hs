module TestParserFragments
    ( parseExpression
    , parseStatement
    , parseStatementBlock
    , parseStatementBlockWith
    , parseFile
    , parseFileWith
    ) where

import System.IO.Unsafe (unsafePerformIO)
import qualified FileParserProtocol as File
import Native (runWithInputFull)
import ParsedFile
import qualified ParserSeed
import Syntax (Expression, Statement (..))
import qualified TersusParser
import Utils (Result (..))

parseFileWith :: Decls -> String -> Either String (ParsedFile, Decls)
parseFileWith = TersusParser.parseFileWith

parseFile :: String -> Either String ParsedFile
parseFile source = fst <$> parseFileWith emptyDecls source

parseStatementBlockWith :: Decls -> String -> Either String ([Statement], Decls)
parseStatementBlockWith declared source = do
    (parsed, final) <- parseFileWith declared source
    if null (fileImports parsed) then Right (fileBody parsed, final)
    else Left "imports are not allowed in a statement fragment"

parseStatementBlock :: String -> Either String [Statement]
parseStatementBlock source = fst <$> parseStatementBlockWith emptyDecls source

parseFragment :: String -> String -> Either String [Statement]
parseFragment kind source = unsafePerformIO $ case File.writeFileRequest emptyDecls source of
    Error e -> pure (Left (ParserSeed.failure e))
    Ok fileInput -> do
        ready <- TersusParser.parserExecutable
        case ready of
            Error e -> pure (Left (ParserSeed.failure e))
            Ok exe -> do
                let input = "tersus-fragment-parse 1\nfragment " ++ kind ++ "\n" ++ drop (length "tersus-file-parse 1\n") fileInput
                (code, out, errors) <- runWithInputFull exe input
                pure (fmap (fileBody . fst) (ParserSeed.fileResponse code out errors))

parseStatement :: String -> Either String Statement
parseStatement source = do
    statements <- parseFragment "statement" source
    case statements of
        [statement] -> Right statement
        _ -> Left (ParserSeed.failure "invalid single-statement reply")

parseExpression :: String -> Either String Expression
parseExpression source = do
    statements <- parseFragment "expression" source
    case statements of
        [Return expression] -> Right expression
        _ -> Left (ParserSeed.failure "invalid expression reply")
