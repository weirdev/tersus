module Parse where

import Text.Parsec
import Text.Parsec.String (Parser)

import TersusTypes
import Data.Char (isLetter)
import Control.Arrow (Arrow(first))
import Control.Monad (void)

semicolon :: Parser ()
semicolon = do
    void (satisfy (==';'))
    -- Treat multiple semicolons as one
    skipMany (void (satisfy (==';')) <|> requiredWhitespace)
    return ()

requiredWhitespace :: Parser ()
requiredWhitespace = void $ many1 $ oneOf " \n\t"

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

statementBlock :: Parser [Statement]
statementBlock = do
    whitespace
    statements <- statement `sepEndBy` semicolon
    whitespace
    return statements

statement :: Parser Statement
statement = do
     whitespace
     statementType <- many1 $ satisfy isLetter
     whitespace
     s <- case statementType of
        "assign" -> assignStatement
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

-- NOTE: Infix expression must be matched first,
-- otherwise we will parse the lhs of infix expressions 
-- as one of the other expression types,
-- not matching the infix operator and rhs
-- TODO: After the reorder, we loop endlessly
expression :: Parser Expression
expression = try infixExpression <|> nonInfixExpression
-- expression = fExpression <|> valExpression <|> varExpression -- TODO: <|> blockExpression

nonInfixExpression :: Parser Expression
nonInfixExpression = try fExpression <|> valExpression <|> varExpression -- TODO: <|> blockExpression

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
infixExpression = chainl1 nonInfixExpression op
    where
        op = do
            funct <- infixFunct
            whitespace
            return (\lexpr rexpr -> F funct [lexpr, rexpr])

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

withEof :: Parser a -> Parser a
withEof p = do
    result <- p
    eof
    return result

-- Function to run the parser
parseStatement :: String -> Either ParseError Statement
parseStatement = parse (withEof statement) ""

-- Function to run the parser
parseStatementBlock :: String -> Either ParseError [Statement]
parseStatementBlock = parse (withEof statementBlock) ""

main :: IO ()
main = do
    -- let input = "assign x = 5"
    input <- getLine
    case parseStatementBlock input of
        Left err -> print err
        Right result -> putStrLn $ "Parsed result: " ++ show result
