module Parse where

import Text.Parsec
import Text.Parsec.String (Parser)

import Control.Monad (void)
import Data.Char (isLetter)
import TersusTypes

-- https://github.com/JakeWheat/intro_to_parsing/blob/master/VerySimpleExpressions.lhs
-- https://hackage.haskell.org/package/parsec-3.1.17.0/docs/Text-Parsec-Combinator.html

semicolon :: Parser ()
semicolon = do
    void (satisfy (== ';'))
    -- Treat multiple semicolons as one
    skipMany (void (char ';') <|> requiredWhitespace)
    return ()

requiredWhitespace :: Parser ()
requiredWhitespace = void $ many1 $ oneOf " \n\t"

whitespace :: Parser ()
whitespace = void $ many $ oneOf " \n\t"

statementBlock :: Parser [Statement]
statementBlock = do
    statements <- statement `sepEndBy` semicolon
    whitespace
    return statements

statement :: Parser Statement
statement = rewriteStatement <|> assignStatement

assignStatement :: Parser Statement
assignStatement = do
    -- TODO: Allow digits in variable names
    var <- many $ satisfy isLetter
    whitespace
    void (char '=')
    whitespace
    expr <- expression
    whitespace
    return (Assign var expr)

rewriteStatement :: Parser Statement
rewriteStatement = do
    void (string "rewrite")
    whitespace
    rule <- rwRule
    whitespace
    return (Rewrite rule)

rwRule :: Parser RwRule
rwRule = do
    ruleStr <- many1 letter
    whitespace
    -- TODO: Parens and argument list
    mvar <- optionMaybe variable
    whitespace
    return
        ( case (ruleStr, mvar) of
            ("refl", Just var) -> Refl var
            ("eqToLtPlus1", Just var) -> EqToLtPlus1 var
            ("eval", Just var) -> Eval var
            ("evalAll", Nothing) -> EvalAll
            _ -> error "Unknown rule or wrong number of arguments"
        )

-- NOTE: Infix expression must be matched first,
-- otherwise we will parse the lhs of infix expressions
-- as one of the other expression types,
-- not matching the infix operator and rhs
-- TODO: After the reorder, we loop endlessly
expression :: Parser Expression
expression = try infixExpression <|> nonInfixExpression

-- expression = fExpression <|> valExpression <|> varExpression -- TODO: <|> blockExpression

nonInfixExpression :: Parser Expression
nonInfixExpression = try fExpression <|> valExpression <|> varExpression <|> parensExpression -- TODO: <|> blockExpression

parensParse :: Parser a -> Parser a
parensParse innerParser = do
    void (char '(')
    whitespace
    inner <- innerParser
    whitespace
    void (char ')')
    whitespace
    return inner

parensExpression :: Parser Expression
parensExpression = parensParse expression

valExpression :: Parser Expression
valExpression = intExpression <|> listExpression

intExpression :: Parser Expression
intExpression = do
    val <- many1 digit
    whitespace
    return (Val (VInt (read val)))

valToInteger :: Expression -> Integer
valToInteger (Val (VInt i)) = i
valToInteger _ = error "Not an integer"

listExpression :: Parser Expression
listExpression = do
    void (char '[')
    whitespace
    vals <- intExpression `sepBy` char ','
    whitespace
    void (char ']')
    whitespace
    return (Val (VIntList (map valToInteger vals)))

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
    void (char '(')
    whitespace
    args <- expression `sepBy` char ','
    whitespace
    void (char ')')
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
    return
        ( case op of
            '+' -> Plus
            '-' -> Minus
            _ -> error "Unknown operator"
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
            _ -> error "Unknown relation"
    return (Rel rel)

variable :: Parser String
-- TODO: Allow digits in variable names
variable = many1 letter

topLevelWrap :: Parser a -> Parser a
topLevelWrap p = do
    whitespace
    result <- p
    -- whitespace?
    eof -- Ensure we have parsed the whole input
    return result

-- Function to run the parser
parseStatement :: String -> Either ParseError Statement
parseStatement = parse (topLevelWrap statement) ""

-- Function to run the parser
parseStatementBlock :: String -> Either ParseError [Statement]
parseStatementBlock = parse (topLevelWrap statementBlock) ""
