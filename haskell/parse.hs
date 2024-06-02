module Parse where

import Text.Parsec
import Text.Parsec.String (Parser)

import TersusTypes
import Data.Char (isLetter)
import Control.Arrow (Arrow(first))
import Control.Monad (void)

semicolon :: Parser String
semicolon = many $ satisfy (==';')

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

statement :: Parser Statement
statement = do
     whitespace
     statementType <- many $ satisfy isLetter
     whitespace
     s <- case statementType of
        "assign" -> assignStatement
     whitespace
     semicolon
     whitespace
     return s

assignStatement :: Parser Statement
assignStatement = do
    -- TODO: Allow digits in variable names
    var <- many $ satisfy isLetter
    whitespace
    char '='
    whitespace
    expr <- expression
    whitespace
    return (Assign var expr)

expression :: Parser Expression
expression = valExpression <|> varExpression <|> fExpression -- TODO: <|> blockExpression

valExpression :: Parser Expression
valExpression = do
    val <- many1 digit
    whitespace
    -- TODO: Allow other types of values
    return (Val (VInt (read val)))

varExpression :: Parser Expression
varExpression = do
    var <- variable
    whitespace
    return (Var var)

fExpression :: Parser Expression
fExpression = do
    fname <- many1 letter
    let funct = case fname of
         "size" -> Size
         "first" -> First
         "last" -> Last
         _ -> error "Unknown function"
    char '('
    whitespace
    args <- expression `sepBy` char ','
    whitespace
    char ')'
    whitespace
    return (F funct args)

infixExpression :: Parser Expression
infixExpression = do
    arg1 <- expression
    whitespace
    funct <- infixFunct
    whitespace
    arg2 <- expression
    whitespace
    return (F funct [arg1, arg2])

infixFunct :: Parser Funct
infixFunct = arithmeticFunct <|> relationFunct

arithmeticFunct :: Parser Funct
arithmeticFunct = do
    op <- oneOf "+-" -- TODO: Add */
    whitespace
    return (case op of
         '+' -> Plus
         '-' -> Minus
        )

relationFunct :: Parser Funct
relationFunct = do
    relstr <- many1 $ oneOf "=<>"
    whitespace
    let rel = case relstr of
         "=" -> Eq
         "<" -> Lt
         ">" -> Gt
         "<=" -> LtEq
         ">=" -> GtEq
    return (Rel rel)

variable :: Parser String
-- TODO: Allow digits in variable names
variable = many1 letter

-- Function to run the parser
parseStatement :: String -> Either ParseError Statement
parseStatement = parse statement ""

main :: IO ()
main = do
    -- let input = "assign x = 5"
    input <- getLine
    case parseStatement input of
        Left err -> print err
        Right result -> putStrLn $ "Parsed result: " ++ show result
