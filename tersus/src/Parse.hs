module Parse where

import Text.Parsec
import Text.Parsec.String (Parser)

import Control.Monad (void)
import Data.Char (isDigit, isLetter)

import StdLib
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
    return (Assign var (Val (VFunct argNames [] (NativeFunct fnBody) [])))

validationStatement :: Parser Statement
validationStatement =
    ValidationStatement <$> (rewriteStatement <|> proofAssertStatement)

rewriteStatement :: Parser ValidationStatement
rewriteStatement = do
    void (string "rewrite")
    whitespace
    rule <- rwRule
    whitespace
    return (Rewrite rule)

proofAssertStatement :: Parser ValidationStatement
proofAssertStatement = do
    void (string "affirm")
    whitespace
    p <- proof
    whitespace
    return (ProofAssert p)

proof :: Parser VariableProof
proof =
    try
        infixProof
        <|> nonInfixProof

nonInfixProof :: Parser VariableProof
nonInfixProof =
    concreteProof
        <|> parensProof
        <|> try functionProof
        <|> try abstractProof

infixProof :: Parser VariableProof
infixProof = chainl1 nonInfixProof op
  where
    op = do
        funct <- infixFunct
        whitespace
        return (\lproof rproof -> FApp (CTerm (builtinFunct funct)) [lproof, rproof])

parensProof :: Parser VariableProof
parensProof = parensParse proof

functionProof :: Parser VariableProof
functionProof = do
    fname <- variable
    -- TODO: Udf support
    let funct = case fname of
            "size" -> Size
            "first" -> First
            "last" -> Last
            _ -> error "Functions in proofs only support builtins for now"
    void (char '(')
    whitespace
    args <- proof `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    return (FApp (CTerm (builtinFunct funct)) args)

abstractProof :: Parser VariableProof
abstractProof = do
    p <- ATerm <$> variable
    whitespace
    return p

concreteProof :: Parser VariableProof
concreteProof = CTerm <$> value

blockStatement :: Parser Statement
blockStatement = do
    stmts <- curlyBracesParse statementBlock
    return (Block stmts)

rwRule :: Parser RwRule
rwRule = do
    ruleStr <- variable
    whitespace
    case ruleStr of
        "refl" -> Refl <$> proof
        _ -> do
            -- TODO: Parens and argument list
            mvar <- optionMaybe variable
            whitespace
            return
                ( case (ruleStr, mvar) of
                    ("eqToLtPlus1", Just var) -> EqToLtPlus1 var
                    ("eval", Just var) -> Eval var
                    ("evalAll", Nothing) -> EvalAll
                    _ -> error "Unknown rule or wrong number of arguments"
                )

-- NOTE: Infix expression must be matched first,
-- otherwise we will parse the lhs of infix expressions
-- as one of the other expression types,
-- not matching the infix operator and rhs
expression :: Parser Expression
expression = try infixExpression <|> nonInfixExpression

nonInfixExpression :: Parser Expression
nonInfixExpression =
    try fExpression
        <|> (Val <$> value)
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

value :: Parser Value
value = vint <|> vlist

vint :: Parser Value
vint = do
    val <- many1 digit
    whitespace
    return (VInt (read val))

valToInteger :: Value -> Integer
valToInteger (VInt i) = i
valToInteger _ = error "Not an integer"

vlist :: Parser Value
vlist = do
    void (char '[')
    whitespace
    vals <- vint `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ']')
    whitespace
    return (VIntList (map valToInteger vals))

varExpression :: Parser Expression
varExpression = do
    var <- variable
    whitespace
    return (Var var)

fExpression :: Parser Expression
fExpression = do
    fname <- variable
    void (char '(')
    whitespace
    args <- expression `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    return $ F (Var fname) args

infixExpression :: Parser Expression
infixExpression = chainl1 nonInfixExpression op
  where
    op = do
        funct <- infixFunct
        whitespace
        -- TODO: Function should be Var expression like fExpression produces not Val
        return (\lexpr rexpr -> F (Val (builtinFunct funct)) [lexpr, rexpr])

infixFunct :: Parser BuiltinFunct
infixFunct = arithmeticFunct <|> relationFunct

arithmeticFunct :: Parser BuiltinFunct
arithmeticFunct = do
    op <- oneOf "+-" -- TODO: Add */
    whitespace
    return
        ( case op of
            '+' -> Plus
            '-' -> Minus
            _ -> error "Unknown operator"
        )

relationFunct :: Parser BuiltinFunct
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
