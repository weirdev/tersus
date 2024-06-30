module Parse where

import Text.Parsec
import Text.Parsec.String (Parser)

import Control.Monad (void)
import Data.Char (isDigit, isLetter)
import TersusTypes

-- https://github.com/JakeWheat/intro_to_parsing/blob/master/VerySimpleExpressions.lhs
-- https://hackage.haskell.org/package/parsec-3.1.17.0/docs/Text-Parsec-Combinator.html

-- Utility parsers
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

skipWhitespace :: Parser a -> Parser a
skipWhitespace p = do
    out <- p
    whitespace
    return out

variable :: Parser String
-- TODO: Allow digits in variable names
variable = do
    fl <- satisfy isLetter
    rest <- many $ satisfy isLetter <|> satisfy isDigit
    return (fl : rest)

-- Tersus parsers
statementBlock :: Parser [Statement]
statementBlock = do
    statements <- statement `sepEndBy` semicolon
    whitespace
    return statements

statement :: Parser Statement
statement =
    returnStatement
        <|> validationStatement
        <|> functStatement
        <|> assignStatement
        <|> blockStatement

assignStatement :: Parser Statement
assignStatement = do
    var <- variable
    whitespace
    void (char '=')
    whitespace
    expr <- expression
    whitespace
    return (Assign var expr)

returnStatement :: Parser Statement
returnStatement = do
    try $ void (string "return")
    whitespace
    expr <- expression
    whitespace
    return (Return expr)

functStatement :: Parser Statement
functStatement = do
    void (string "fn")
    whitespace
    var <- variable
    whitespace
    void (char '(')
    whitespace
    argNames <- variable `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    fnBody <- curlyBracesParse statementBlock
    whitespace
    return (Assign var (Val (VFunct argNames [] fnBody [])))

validationStatement :: Parser Statement
validationStatement = ValidationStatement <$> rewriteStatement

rewriteStatement :: Parser ValidationStatement
rewriteStatement = do
    void (string "rewrite")
    whitespace
    rule <- rwRule
    whitespace
    return (Rewrite rule)

blockStatement :: Parser Statement
blockStatement = do
    stmts <- curlyBracesParse statementBlock
    return (Block stmts)

rwRule :: Parser RwRule
rwRule = do
    ruleStr <- variable
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

nonInfixExpression :: Parser Expression
nonInfixExpression =
    try fExpression
        <|> valExpression
        <|> varExpression
        <|> parensExpression

bracketsParse :: Parser o -> Parser c -> Parser a -> Parser a
bracketsParse open close innerParser = do
    void open
    whitespace
    inner <- innerParser
    whitespace
    void close
    whitespace
    return inner

parensParse :: Parser a -> Parser a
parensParse = bracketsParse (char '(') (char ')')

curlyBracesParse :: Parser a -> Parser a
curlyBracesParse = bracketsParse (char '{') (char '}')

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
    vals <- intExpression `sepBy` skipWhitespace (char ',')
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
    fname <- variable
    let builtinFunct = case fname of
            "size" -> Just Size
            "first" -> Just First
            "last" -> Just Last
            _ -> Nothing
    void (char '(')
    whitespace
    args <- expression `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    return
        ( case builtinFunct of
            Just funct -> F funct args
            -- User defined function
            Nothing -> F Call (Var fname : args)
        )

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

-- Function to run the parser
parseExpression :: String -> Either ParseError Expression
parseExpression = parse (topLevelWrap expression) ""
