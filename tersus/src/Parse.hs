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

identifierChar :: Parser Char
identifierChar = satisfy isLetter <|> satisfy isDigit

keyword :: String -> Parser ()
keyword kw = try $ do
    void (string kw)
    notFollowedBy identifierChar
    return ()

genericStatementBlock :: Parser a -> Parser [a]
genericStatementBlock p = do
    statements <- p `sepEndBy` semicolon
    whitespace
    return statements

-- Tersus parsers
statementBlock :: Parser [Statement]
statementBlock = genericStatementBlock statement

validationStatementBlock :: Parser [ValidationStatement]
validationStatementBlock = genericStatementBlock validationStatement

statement :: Parser Statement
statement =
    returnStatement
        <|> ( ValidationStatement
                <$> validationStatement
            )
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
    keyword "return"
    whitespace
    expr <- expression
    whitespace
    return (Return expr)

functStatement :: Parser Statement
functStatement = do
    keyword "fn"
    whitespace
    var <- variable
    whitespace
    void (char '(')
    whitespace
    argNames <- variable `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    inputReqs <- option [] functContractReqs
    whitespace
    outputReqs <- option [] functContractReqs
    whitespace
    fnBody <- curlyBracesParse statementBlock
    whitespace
    return (Assign var (Val (VFunct argNames inputReqs outputReqs (NativeFunct fnBody) [])))

functContractReqs :: Parser [ValidationStatement]
-- Function contracts are written as `[{ ... }]`: square brackets mark the presence
-- of a contract section and the inner braces hold ordinary validation statements.
functContractReqs = squareBracketsParse (curlyBracesParse validationStatementBlock)

validationStatement :: Parser ValidationStatement
validationStatement =
    rewriteStatement
        <|> proofAssertStatement
        <|> assignProofVarStatement

rewriteStatement :: Parser ValidationStatement
rewriteStatement = do
    keyword "rewrite"
    whitespace
    rule <- rwRule
    whitespace
    return (Rewrite rule)

proofAssertStatement :: Parser ValidationStatement
proofAssertStatement = do
    keyword "affirm"
    whitespace
    p <- proof
    whitespace
    return (ProofAssert p)

assignProofVarStatement :: Parser ValidationStatement
assignProofVarStatement = do
    keyword "define"
    whitespace
    var <- variable
    whitespace
    void (char '=')
    whitespace
    expr <- expression
    whitespace
    return (AssignProofVar var expr)

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
    funct <- case fname of
        "size" -> return Size
        "first" -> return First
        "last" -> return Last
        _ -> fail "Functions in proofs only support builtins for now"
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
        "refl" -> parseReflRule
        "eqToLtPlus1" -> parseUnaryVarRule EqToLtPlus1
        "eqToGtZero" -> parseUnaryVarRule EqToGtZero
        "eval" -> parseUnaryVarRule Eval
        "evalAll" -> parseNullaryRule EvalAll
        _ -> fail "Unknown rule or wrong number of arguments"

parseReflRule :: Parser RwRule
parseReflRule = Refl <$> proof

parseUnaryVarRule :: (Variable -> RwRule) -> Parser RwRule
parseUnaryVarRule ctor = do
    var <- variable
    whitespace
    return (ctor var)

parseNullaryRule :: RwRule -> Parser RwRule
parseNullaryRule = return

-- NOTE: Infix expression must be matched first,
-- otherwise we will parse the lhs of infix expressions
-- as one of the other expression types,
-- not matching the infix operator and rhs
-- All infix operators currently share the same precedence and associate left.
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

squareBracketsParse :: Parser a -> Parser a
squareBracketsParse = bracketsParse (char '[') (char ']')

parensExpression :: Parser Expression
parensExpression = parensParse expression

value :: Parser Value
value = vint <|> vlist

vint :: Parser Value
vint = do
    val <- many1 digit
    whitespace
    return (VInt (read val))

vlist :: Parser Value
vlist = do
    void (char '[')
    whitespace
    vals <- ((\v -> case v of VInt i -> i; _ -> error "unreachable") <$> vint) `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ']')
    whitespace
    return (VIntList vals)

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
    if op == '+'
        then return Plus
        else return Minus

relationFunct :: Parser BuiltinFunct
relationFunct = do
    relstr <- many1 $ oneOf "=<>"
    whitespace
    case relstr of
        "=" -> return (Rel Eq)
        "<" -> return (Rel Lt)
        ">" -> return (Rel Gt)
        "<=" -> return (Rel LtEq)
        ">=" -> return (Rel GtEq)
        _ -> fail "Unknown relation"

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
