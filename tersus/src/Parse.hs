module Parse where

import Text.Parsec
import qualified Data.Map as Map

import Control.Monad (void, when)
import Data.Char (isDigit, isLetter)

import StdLib
import TersusTypes

-- The parser remembers the structs declared so far, which a struct literal needs: the fields of a
-- struct in declaration order. A struct must be declared before it is used.
type Structs = Map.Map Name [Variable]

type Parser = Parsec String Structs

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
requiredWhitespace = void $ many1 whitespaceItem

-- Comments count as whitespace, so they are accepted anywhere whitespace is.
whitespace :: Parser ()
whitespace = void $ many whitespaceItem

whitespaceItem :: Parser ()
whitespaceItem = void (oneOf " \r\n\t") <|> (lineComment <?> "")

-- `//` runs to the end of the line (or the end of the input).
lineComment :: Parser ()
lineComment = do
    void (try (string "//"))
    skipMany (noneOf "\n")

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
        <|> ifStatement
        <|> whileStatement
        <|> axiomStatement
        <|> proofStatement
        <|> ( ValidationStatement
                <$> validationStatement
            )
        <|> structStatement
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

-- `else if` is an else branch holding a single nested `if`.
ifStatement :: Parser Statement
ifStatement = do
    keyword "if"
    whitespace
    cond <- expression
    whitespace
    thenBranch <- curlyBracesParse statementBlock
    elseBranch <- option [] elseBranchParse
    return (If cond thenBranch elseBranch)
  where
    elseBranchParse = do
        keyword "else"
        whitespace
        curlyBracesParse statementBlock <|> ((: []) <$> ifStatement)

-- The loop invariant uses the contract syntax and is optional: `while c [{ affirm ...; }] { ... }`.
whileStatement :: Parser Statement
whileStatement = do
    keyword "while"
    whitespace
    cond <- expression
    whitespace
    invariant <- option [] functContractReqs
    whitespace
    body <- curlyBracesParse statementBlock
    return (While cond invariant body)

structStatement :: Parser Statement
structStatement = do
    keyword "struct"
    whitespace
    name <- variable
    whitespace
    void (char '{')
    whitespace
    fields <- structField `sepEndBy` (char ',' >> whitespace)
    void (char '}')
    whitespace
    when (length (nubFields fields) /= length fields) $ fail ("Struct " ++ name ++ " repeats a field")
    updateState (Map.insert name (map fst fields))
    return (StructDef name fields)
  where
    nubFields = foldr (\(f, t) rest -> if f `elem` map fst rest then rest else (f, t) : rest) []

-- field: Type
structField :: Parser (Variable, Type)
structField = do
    field <- variable
    whitespace
    void (char ':')
    whitespace
    ty <- typeAnnotation
    return (field, ty)

-- Name { field: value, ..., ..base }: every field of the struct, or the ones that change and a base
-- struct to copy the rest from. The result applies the struct's constructor, so it is an ordinary term.
structLiteral :: Parser a -> (Value -> [a] -> a) -> Parser a
structLiteral element apply = do
    (name, declared) <- try $ do
        candidate <- variable
        structs <- getState
        known <- maybe (fail "not a struct") return (Map.lookup candidate structs)
        whitespace
        void (char '{')
        return (candidate, known)
    whitespace
    inits <- many fieldInit
    base <- optionMaybe (string ".." >> whitespace >> element <* whitespace <* optional (char ',' >> whitespace))
    void (char '}')
    whitespace
    mapM_ (\(field, _) -> when (field `notElem` declared) (fail ("Struct " ++ name ++ " has no field " ++ field))) inits
    when (length (map fst inits) /= length (foldr (\f rest -> if f `elem` rest then rest else f : rest) [] (map fst inits))) $
        fail ("Struct " ++ name ++ " literal repeats a field")
    args <- mapM (argument name base inits) declared
    return (apply (builtinFunct (Ctor name declared)) args)
  where
    fieldInit = do
        field <- variable
        whitespace
        void (char ':')
        whitespace
        value' <- element
        whitespace
        optional (char ',' >> whitespace)
        return (field, value')
    argument name base inits field =
        case (lookup field inits, base) of
            (Just given, _) -> return given
            (Nothing, Just from) -> return (apply (builtinFunct (Field field)) [from])
            (Nothing, Nothing) -> fail ("Struct " ++ name ++ " literal lacks field " ++ field)

-- x.field, repeated. A `..` after a term is a range, not a field.
withFields :: (Value -> [a] -> a) -> Parser a -> Parser a
withFields apply term = do
    base <- term
    fields <- many (try (char '.' >> notFollowedBy (char '.') >> variable <* whitespace))
    return (foldl (\acc field -> apply (builtinFunct (Field field)) [acc]) base fields)

expressionApply :: Value -> [Expression] -> Expression
expressionApply funct = F (Val funct)

proofApply :: Value -> [VariableProof] -> VariableProof
proofApply funct = FApp (CTerm funct)

functStatement :: Parser Statement
functStatement = do
    keyword "fn"
    whitespace
    var <- variable
    whitespace
    void (char '(')
    whitespace
    params <- parameter `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    returnType <- string "->" >> whitespace >> typeAnnotation
    whitespace
    inputReqs <- option [] functContractReqs
    whitespace
    outputReqs <- option [] functContractReqs
    whitespace
    fnBody <- curlyBracesParse statementBlock
    whitespace
    return (Assign var (Val (VFunct (map fst params) inputReqs outputReqs (NativeFunct (Signature (map snd params) returnType) fnBody) [])))

-- A parameter is a name and its type: `n: Int`
parameter :: Parser (Variable, Type)
parameter = do
    name <- variable
    whitespace
    void (char ':')
    whitespace
    ty <- typeAnnotation
    return (name, ty)

-- Int, Bool, List<T>, and fn(T, ...) -> T for a function value
typeAnnotation :: Parser Type
typeAnnotation = do
    ty <- try functionType <|> namedType
    whitespace
    return ty
  where
    functionType = do
        keyword "fn"
        whitespace
        void (char '(')
        whitespace
        args <- typeAnnotation `sepBy` skipWhitespace (char ',')
        void (char ')')
        whitespace
        void (string "->")
        whitespace
        TFn args <$> typeAnnotation
    namedType = do
        name <- variable
        case name of
            "Int" -> return TInt
            "Bool" -> return TBool
            "List" -> do
                whitespace
                void (char '<')
                whitespace
                element <- typeAnnotation
                void (char '>')
                return (TList element)
            _ -> return (TNamed name)

functContractReqs :: Parser [ValidationStatement]
-- Function contracts are written as `[{ ... }]`: square brackets mark the presence
-- of a contract section and the inner braces hold ordinary validation statements.
functContractReqs = squareBracketsParse (curlyBracesParse validationStatementBlock)

axiomStatement :: Parser Statement
axiomStatement = do
    keyword "axiom"
    whitespace
    name <- variable
    whitespace
    args <- parensParse (variable `sepBy` skipWhitespace (char ','))
    whitespace
    inputReqs <- functContractReqs
    whitespace
    outputReqs <- functContractReqs
    whitespace
    return (AxiomDef name args inputReqs outputReqs)

proofStatement :: Parser Statement
proofStatement = do
    keyword "proof"
    whitespace
    name <- variable
    whitespace
    args <- parensParse (variable `sepBy` skipWhitespace (char ','))
    whitespace
    inputReqs <- functContractReqs
    whitespace
    outputReqs <- functContractReqs
    whitespace
    body <- curlyBracesParse validationStatementBlock
    whitespace
    return (ProofDef name args inputReqs outputReqs body)

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
    forallProof
        <|> try infixProof
        <|> nonInfixProof

-- forall j where j >= 0, j < i: P
-- forall j in 0..i: P            (shorthand for: forall j where j >= 0, j < i: P)
-- The index is bound in the guards and the body, and forall does not nest.
forallProof :: Parser VariableProof
forallProof = do
    keyword "forall"
    whitespace
    index <- variable
    whitespace
    (guards, body) <- forallRange index <|> forallWhere
    when (any proofHasForall (body : guards)) $ fail "forall does not nest"
    return (Forall index (map (bindIndex index) guards) (bindIndex index body))
  where
    forallWhere = do
        keyword "where"
        whitespace
        guards <- proof `sepBy1` skipWhitespace (char ',')
        body <- forallBody
        return (guards, body)
    forallRange index = do
        keyword "in"
        whitespace
        lower <- proof
        void (string "..")
        whitespace
        upper <- proof
        body <- forallBody
        let geq = FApp (CTerm (builtinFunct (Rel GtEq))) [ATerm index, lower]
            lt = FApp (CTerm (builtinFunct (Rel Lt))) [ATerm index, upper]
        return ([geq, lt], body)
    forallBody = do
        void (char ':')
        whitespace
        proof

-- Occurrences of the index become BVar
bindIndex :: Variable -> VariableProof -> VariableProof
bindIndex index (ATerm var) | var == index = BVar index
bindIndex index (FApp funct args) = FApp (bindIndex index funct) (map (bindIndex index) args)
bindIndex _ other = other

nonInfixProof :: Parser VariableProof
nonInfixProof =
    concreteProof
        <|> withFields proofApply (parensProof <|> structLiteral proof proofApply <|> try functionProof <|> try abstractProof)

infixProof :: Parser VariableProof
infixProof = infixLevels nonInfixProof (\funct lproof rproof -> FApp (CTerm (builtinFunct funct)) [lproof, rproof])

parensProof :: Parser VariableProof
parensProof = parensParse proof

functionProof :: Parser VariableProof
functionProof = do
    fname <- variable
    funct <- case fname of
        "size" -> return Size
        "first" -> return First
        "last" -> return Last
        "get" -> return Get
        "push" -> return Push
        "set" -> return Set
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
        "eval" -> parseUnaryVarRule Eval
        "evalAll" -> parseNullaryRule EvalAll
        "checkGtZero" -> CheckGtZero <$> proof
        "checkRel" -> CheckRel <$> proof
        _ -> UserRewrite ruleStr <$> many proof

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
-- `*` and `/` bind tighter than `+` and `-`, which bind tighter than the relations (see infixLevels).
expression :: Parser Expression
expression = try infixExpression <|> nonInfixExpression

nonInfixExpression :: Parser Expression
nonInfixExpression =
    withFields expressionApply (structLiteral expression expressionApply <|> try fExpression)
        <|> (Val <$> value)
        <|> withFields expressionApply (varExpression <|> parensExpression)

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
value = vbool <|> vint <|> vlist

vbool :: Parser Value
vbool =
    (keyword "true" >> whitespace >> return (VBool True))
        <|> (keyword "false" >> whitespace >> return (VBool False))

vint :: Parser Value
vint = do
    sign <- option id (char '-' >> whitespace >> return negate)
    val <- many1 digit
    whitespace
    return (VInt (sign (read val)))

vlist :: Parser Value
vlist = do
    void (char '[')
    whitespace
    vals <- value `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ']')
    whitespace
    return (VList vals)

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
-- TODO: Function should be Var expression like fExpression produces not Val
infixExpression = infixLevels nonInfixExpression (\funct lexpr rexpr -> F (Val (builtinFunct funct)) [lexpr, rexpr])

-- Infix operators in three levels, tightest first: `*` and `/`, then `+` and `-`, then the relations.
-- Each level associates left, so `a + 1 < b * 2` is `(a + 1) < (b * 2)`.
infixLevels :: Parser a -> (BuiltinFunct -> a -> a -> a) -> Parser a
infixLevels operand combine = relations
  where
    level opParser next = chainl1 next (do funct <- opParser; whitespace; return (combine funct))
    multiplicative = level multiplicativeFunct operand
    additive = level arithmeticFunct multiplicative
    relations = level relationFunct additive

arithmeticFunct :: Parser BuiltinFunct
arithmeticFunct = do
    op <- oneOf "+-"
    whitespace
    if op == '+'
        then return Plus
        else return Minus

multiplicativeFunct :: Parser BuiltinFunct
multiplicativeFunct = (char '*' >> whitespace >> return Times) <|> (char '/' >> whitespace >> return Div)

relationFunct :: Parser BuiltinFunct
relationFunct = do
    relstr <- many1 $ oneOf "=<>!"
    whitespace
    case relstr of
        "=" -> return (Rel Eq)
        "!=" -> return (Rel NotEq)
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
parseStatement = runParser (topLevelWrap statement) Map.empty ""

-- Function to run the parser
parseStatementBlock :: String -> Either ParseError [Statement]
parseStatementBlock = runParser (topLevelWrap statementBlock) Map.empty ""

-- Function to run the parser
parseExpression :: String -> Either ParseError Expression
parseExpression = runParser (topLevelWrap expression) Map.empty ""
