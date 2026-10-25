module Parse
    ( assigns
    , expression
    , parameter
    , parseExpression
    , parseStatement
    , parseStatementBlock
    , proof
    , semicolon
    , statement
    , statements
    , value
    , variable
    ) where

import Text.Parsec
import qualified Data.Map as Map

import Control.Monad (void, when)
import Data.Char (isDigit, isLetter, isUpper)
import Data.List (intercalate, isInfixOf, nub, (\\))
import Data.Maybe (isJust)

import StdLib
import Utils (inIntRange)
import TersusTypes

-- The parser remembers the structs and enums declared so far. A literal needs the fields of a constructor
-- in declaration order (a struct is a constructor named like its type, a variant is Enum::Variant), and a
-- match needs the variants of a type. A type must be declared before it is used.
data Decls = Decls
    { declCtors :: Map.Map Name [Variable]
    , declTypes :: Map.Map Name [Name]
    , declSelf :: Maybe Name -- the type of the impl being read, which `Self` stands for
    , declTypeParams :: [Name] -- the type parameters of the function or the struct being read: a name of these in a type is that parameter
    , declGenerics :: Map.Map Name [Variable] -- the structs with sizes and types, and the parameters of each, in order
    , declImplParams :: [Variable] -- the type and size parameters of the impl being read (`impl<T> Vec<T>`), which each of its functions has
    }

emptyDecls :: Decls
emptyDecls = Decls Map.empty Map.empty Nothing [] Map.empty []

type Parser = Parsec String Decls

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

-- Self is the type of the impl that is being read; in a trait it stays Self, for the type checker to replace
resolveSelf :: Name -> Parser Name
resolveSelf "Self" = maybe "Self" id . declSelf <$> getState
resolveSelf name = return name

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
statementBlock = concat <$> genericStatementBlock statements

-- A match is rewritten as the statements it stands for, so it can be several statements
statements :: Parser [Statement]
statements = matchAssign <|> matchReturn <|> matchStatement <|> forStatement <|> (pure <$> statement)

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
        <|> enumStatement
        <|> traitStatement
        <|> implStatement
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

-- The loop invariant uses the contract syntax and is optional: `while c [{ affirm ...; }] shrinks e { ... }`.
-- What follows is how the loop ends, see terminationClause.
whileStatement :: Parser Statement
whileStatement = do
    keyword "while"
    whitespace
    cond <- expression
    whitespace
    invariant <- option [] functContractReqs
    whitespace
    termination <- terminationClause
    body <- curlyBracesParse statementBlock
    return (While cond invariant termination body)

-- for i in lo..hi [{ invariant }] { body } counts i from lo up to hi, which is read once. It is the statements of the
-- loop below, so it has no rules of its own: i stays in scope and is hi afterwards, the validator is given
-- i >= lo and i <= hi as part of the invariant (the invariant written here is added to those), and the loop
-- ends because hi - i shrinks. lo and hi are kept in variables no program can write, named after i.
--
--   lo<i> = lo; hi<i> = hi; i = lo<i>;
--   while i < hi<i> [{ affirm i >= lo<i>; affirm i <= hi<i>; invariant }] shrinks hi<i> - i { body; i = i + 1; };
--
-- for x in list { body } and for i, x in list { body } go through the elements, as that loop over 0..size(list) with
-- x bound to get(list, i) in each iteration (x is local to the body, i stays in scope as it does for a range). The
-- list is read once, so a body that changes the variable it came from does not change what is looped over. The
-- copy of the list, and the index when there is no i, are variables no program can write, named by where the
-- loop is in the source, so loops that nest or follow each other and use the same names do not share them.
forStatement :: Parser [Statement]
forStatement = do
    position <- getPosition
    keyword "for"
    whitespace
    first <- variable
    whitespace
    second <- optionMaybe (char ',' >> whitespace >> variable <* whitespace)
    keyword "in"
    whitespace
    start <- expression
    whitespace
    end <- optionMaybe (string ".." >> whitespace >> expression <* whitespace)
    invariant <- option [] functContractReqs
    whitespace
    body <- curlyBracesParse statementBlock
    let place = show (sourceLine position) ++ ":" ++ show (sourceColumn position)
    case (second, end) of
        (Nothing, Just hi) -> countingLoop first start hi invariant body
        (Just _, Just _) -> fail "A for loop over a range has one variable, as in for i in 0..n"
        (Nothing, Nothing) -> elementLoop place ("$index " ++ place) first start invariant body
        (Just element, Nothing) -> elementLoop place first element start invariant body

countingLoop :: Variable -> Expression -> Expression -> [ValidationStatement] -> [Statement] -> Parser [Statement]
countingLoop var lo hi invariant body = do
    when (assigns var body) $ fail ("The body of a for loop cannot assign its loop variable " ++ var)
    let loName = "$lo " ++ var
        hiName = "$hi " ++ var
        bound rel name = ProofAssert (FApp (CTerm (builtinFunct (Rel rel))) [ATerm var, ATerm name])
        step = Assign var (builtinApp Plus [Var var, Val (VInt 1)])
        remaining = builtinApp Minus [Var hiName, Var var]
    return
        [ Assign loName lo
        , Assign hiName hi
        , Assign var (Var loName)
        , While (builtinApp (Rel Lt) [Var var, Var hiName]) (bound GtEq loName : bound LtEq hiName : invariant) (Just (Shrinks remaining)) (body ++ [step])
        ]

elementLoop :: String -> Variable -> Variable -> Expression -> [ValidationStatement] -> [Statement] -> Parser [Statement]
elementLoop place index element list invariant body = do
    let listName = "$list " ++ place
        elementOf = Let element (builtinApp Get [Var listName, Var index])
    loop <- countingLoop index (Val (VInt 0)) (builtinApp Size [Var listName]) invariant (elementOf : body)
    return (Assign listName list : loop)

builtinApp :: BuiltinFunct -> [Expression] -> Expression
builtinApp name = F (Val (builtinFunct name))

-- Whether statements assign a variable, in a nested block, branch or loop (a function defined inside has a scope of its own)
assigns :: Variable -> [Statement] -> Bool
assigns var = any assignsIn
  where
    assignsIn (Assign name _) = name == var
    assignsIn (Block stmts) = assigns var stmts
    assignsIn (If _ thenStmts elseStmts) = assigns var thenStmts || assigns var elseStmts
    assignsIn (While _ _ _ stmts) = assigns var stmts
    assignsIn _ = False

-- `shrinks e` or `~`, before the body of a loop or function. Both are optional here, the validator
-- decides whether leaving them out is allowed.
terminationClause :: Parser (Maybe Termination)
terminationClause = optionMaybe (clause <* whitespace)
  where
    clause = (char '~' >> return MayDiverge) <|> (keyword "shrinks" >> whitespace >> Shrinks <$> expression)

-- enum Name { Variant, Variant { field: Type, ... }, ... }
enumStatement :: Parser Statement
enumStatement = do
    keyword "enum"
    whitespace
    name <- variable
    whitespace
    void (char '{')
    whitespace
    variants <- variant name `sepEndBy` (char ',' >> whitespace)
    void (char '}')
    whitespace
    when (name `elem` ["Int", "Bool", "List", "Array", "Box", "Self"]) $ fail (name ++ " is a builtin type and cannot be an enum name")
    when (null variants) $ fail ("Enum " ++ name ++ " has no variants")
    when (length (nub (map fst variants)) /= length variants) $ fail ("Enum " ++ name ++ " repeats a variant")
    modifyState
        ( \d ->
            d
                { declCtors = foldr (\(v, fields) m -> Map.insert v (map fst fields) m) (declCtors d) variants
                , declTypes = Map.insert name (map fst variants) (declTypes d)
                }
        )
    return (EnumDef name variants)
  where
    variant enumName = do
        v <- variable
        whitespace
        fields <- option [] (do void (char '{'); whitespace; fs <- structField `sepEndBy` (char ',' >> whitespace); void (char '}'); whitespace; return fs)
        when (length (nub (map fst fields)) /= length fields) $ fail ("Variant " ++ v ++ " repeats a field")
        return (enumName ++ "::" ++ v, fields)

structStatement :: Parser Statement
structStatement = do
    keyword "struct"
    whitespace
    name <- variable
    whitespace
    -- struct Name<T, n> { ... }: a struct for each list of types and sizes, written Name<Int, 4> (see instanceName). A parameter that starts
    -- with a capital letter is a type, and any other is a size.
    params <- option [] (try (char '<' >> whitespace >> ((variable <* whitespace) `sepBy1` (char ',' >> whitespace)) <* char '>' <* whitespace))
    outerParams <- declTypeParams <$> getState
    -- (the struct may hold itself, as Name<T, n>, in a Box)
    modifyState (\d -> d{declTypeParams = filter isTypeParameter params, declGenerics = if null params then declGenerics d else Map.insert name params (declGenerics d)})
    void (char '{')
    whitespace
    fields <- structField `sepEndBy` (char ',' >> whitespace)
    void (char '}')
    whitespace
    modifyState (\d -> d{declTypeParams = outerParams})
    when (length (nubFields fields) /= length fields) $ fail ("Struct " ++ name ++ " repeats a field")
    when (name `elem` ["Int", "Bool", "List", "Array", "Box", "Self"]) $ fail (name ++ " is a builtin type and cannot be a struct name")
    modifyState (\d -> d{declCtors = Map.insert name (map fst fields) (declCtors d), declTypes = Map.insert name [name] (declTypes d)})
    return (StructDef name params fields)
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
        base <- qualifiedName
        ctors <- declCtors <$> getState
        known <- maybe (fail "not a struct or variant") return (Map.lookup base ctors)
        -- (a struct with sizes and types is written with them: Packet<4> { ... }, Vec<Int, 3> { ... })
        generics <- declGenerics <$> getState
        args <- case Map.lookup base generics of
            Just params | not (isVariant base) -> optionMaybe (try (whitespace >> genericArguments params))
            _ -> return Nothing
        let candidate = maybe base (instanceName base) args
        if null known && isVariant candidate
            then return (candidate, known)
            else do
                whitespace
                void (char '{')
                return (candidate, known)
    if null declared && isVariant name then whitespace >> return (apply (builtinFunct (Ctor name [])) []) else structFields element apply name declared
  where
    isVariant = ("::" `isInfixOf`)

-- The braces of a struct or variant literal, after its name and the opening brace
structFields :: Parser a -> (Value -> [a] -> a) -> Name -> [Variable] -> Parser a
structFields element apply name declared = do
    whitespace
    inits <- many fieldInit
    base <- optionMaybe (string ".." >> whitespace >> element <* whitespace <* optional (char ',' >> whitespace))
    void (char '}')
    whitespace
    mapM_ (\(field, _) -> when (field `notElem` declared) (fail ("Struct " ++ name ++ " has no field " ++ field))) inits
    when (length (map fst inits) /= length (foldr (\f rest -> if f `elem` rest then rest else f : rest) [] (map fst inits))) $
        fail ("Struct " ++ name ++ " literal repeats a field")
    when (isJust base && all (`elem` map fst inits) declared) $
        fail ("Struct " ++ name ++ " literal gives every field, so ..base copies nothing")
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
            (Nothing, Just from)
                | "::" `isInfixOf` name -> return (apply (builtinFunct (Field Nothing field)) [apply (builtinFunct (Cast name)) [from]])
                | otherwise -> return (apply (builtinFunct (Field (Just name) field)) [from])
            (Nothing, Nothing) -> fail ("Struct " ++ name ++ " literal lacks field " ++ field)

-- Name or Enum::Variant
qualifiedName :: Parser Name
qualifiedName = do
    first <- variable
    second <- optionMaybe (try (string "::" >> variable))
    -- (`Self::f` and `Self::Variant` name the struct or enum itself, and `Self { ... }` the struct with the types of the impl)
    case second of
        Just name -> (\owner -> owner ++ "::" ++ name) . selfBase <$> resolveSelf first
        Nothing -> resolveSelf first

-- The struct or enum that a type names, without the types it is given: Vec for Vec<'T>
selfBase :: Name -> Name
selfBase name = maybe name fst (instanceOf name)

-- A struct or variant that has been declared, with its fields
declaredCtor :: Parser (Name, [Variable])
declaredCtor = do
    name <- qualifiedName
    ctors <- declCtors <$> getState
    maybe (fail ("Unknown struct or variant " ++ name)) (\fields -> return (name, fields)) (Map.lookup name ctors)

-- match scrutinee { Pattern => body, ... } where a pattern is a variant and the fields it binds:
-- `Shape::Circle { radius: r }`. The body is a block in a statement and an expression after `=` or `return`.
matchArms :: Parser body -> Parser (Expression, [(Name, [(Variable, Variable)], body)])
matchArms bodyParser = do
    keyword "match"
    whitespace
    scrutinee <- expression
    whitespace
    void (char '{')
    whitespace
    arms <- many arm
    void (char '}')
    whitespace
    return (scrutinee, arms)
  where
    arm = do
        (name, declared) <- declaredCtor
        whitespace
        binds <- option [] (do void (char '{'); whitespace; bs <- bind `sepEndBy` (char ',' >> whitespace); void (char '}'); whitespace; return bs)
        mapM_ (\(field, _) -> when (field `notElem` declared) (fail ("Variant " ++ name ++ " has no field " ++ field))) binds
        when (length (nub (map fst binds)) /= length binds) $ fail ("Pattern " ++ name ++ " repeats a field")
        void (string "=>")
        whitespace
        body <- bodyParser
        whitespace
        optional (char ',' >> whitespace)
        return (name, binds, body)
    bind = do
        field <- variable
        whitespace
        void (char ':')
        whitespace
        var <- variable
        whitespace
        return (field, var)

-- The statements a match stands for: a test of each variant but the last, in order, and the last
-- variant in the final else, since the arms must cover the type. A pattern's fields are read from the
-- scrutinee at the start of its arm.
desugarMatch :: Expression -> [(Name, [(Variable, Variable)], [Statement])] -> Parser [Statement]
desugarMatch _ [] = fail "A match needs at least one arm"
desugarMatch scrutinee arms@((first, _, _) : _) = do
    types <- declTypes <$> getState
    (typeName, variants) <- case [(t, vs) | (t, vs) <- Map.toList types, first `elem` vs] of
        found : _ -> return found
        [] -> fail ("Unknown variant " ++ first)
    let names = [name | (name, _, _) <- arms]
    when (any (`notElem` variants) names) $ fail ("A match over " ++ typeName ++ " has an arm of another type")
    when (length (nub names) /= length names) $ fail ("A match over " ++ typeName ++ " repeats a variant")
    when (not (null (variants \\ names))) $ fail ("A match over " ++ typeName ++ " does not cover " ++ unwords (variants \\ names))
    -- The scrutinee is evaluated once into a name no program can write. Each arm is a branch, whose own scope
    -- holds what it binds and first assigns; a match with one arm has no branch, so it gets a block to do so.
    return $ case arms of
        [(name, binds, body)] -> [Block (Let hidden scrutinee : bindings name binds ++ body)]
        _ -> Let hidden scrutinee : chain arms
  where
    hidden = "$match"
    subject = Var hidden
    chain [] = []
    chain [(name, binds, body)] = bindings name binds ++ body
    chain ((name, binds, body) : rest) =
        [If (F (Val (builtinFunct (Is name))) [subject]) (bindings name binds ++ body) (chain rest)]
    -- Binding hides a variable of the same name outside the match instead of assigning it
    bindings name binds = [Let var (F (Val (builtinFunct (Project name field))) [subject]) | (field, var) <- binds]

-- match scrutinee { Pattern => { statements }, ... }
matchStatement :: Parser [Statement]
matchStatement = do
    (scrutinee, arms) <- matchArms (curlyBracesParse statementBlock)
    desugarMatch scrutinee arms

-- var = match scrutinee { Pattern => expression, ... }: the variable must already exist, since a variable first
-- assigned in a branch is local to it
matchAssign :: Parser [Statement]
matchAssign = do
    var <- try (do v <- variable; whitespace; void (char '='); whitespace; lookAhead (keyword "match"); return v)
    (scrutinee, arms) <- matchArms expression
    desugarMatch scrutinee [(name, binds, [Assign var body]) | (name, binds, body) <- arms]

-- return match scrutinee { Pattern => expression, ... }
matchReturn :: Parser [Statement]
matchReturn = do
    try (keyword "return" >> whitespace >> lookAhead (keyword "match"))
    (scrutinee, arms) <- matchArms expression
    desugarMatch scrutinee [(name, binds, [Return body]) | (name, binds, body) <- arms]

-- x.field and x as Enum::Variant, repeated. A `..` after a term is a range, not a field. A field of an enum value
-- is read after a cast to the variant that has it: (s as Shape::Circle).radius
--
-- In an expression a field read followed by arguments, x.f(a, b), is a call of the function f that belongs to the type of x.
-- Which function that is depends on the type of x, so the checker decides: it is F (Var ".f") (x : arguments) until then.
withFields :: (Value -> [a] -> a) -> Maybe (Parser a, Variable -> a -> [a] -> a) -> Parser a -> Parser a
withFields apply methods term = do
    base <- term
    suffixes <- many (try fieldSuffix <|> castSuffix)
    return (foldl (flip ($)) base suffixes)
  where
    fieldSuffix = do
        void (char '.')
        notFollowedBy (char '.')
        field <- variable
        arguments <- case methods of
            Just (element, _) -> optionMaybe (char '(' >> whitespace >> element `sepBy` skipWhitespace (char ',') <* whitespace <* char ')')
            Nothing -> return Nothing
        whitespace
        return $ case (arguments, methods) of
            (Just args, Just (_, call)) -> \receiver -> call field receiver args
            _ -> \acc -> apply (builtinFunct (Field Nothing field)) [acc]
    castSuffix = do
        keyword "as"
        whitespace
        (variant, _) <- declaredCtor
        whitespace
        return (\acc -> apply (builtinFunct (Cast variant)) [acc])

-- x.f(arguments) in an expression, before the checker has said which function f is
methodCall :: Variable -> Expression -> [Expression] -> Expression
methodCall name receiver args = F (Var ('.' : name)) (receiver : args)

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
    -- fn f<T, n>(...): what a call gives. A name that starts with a capital letter is a type (`T`, which the function knows nothing of);
    -- any other is a size, which is one of the last parameters of the function (an Int that the body and the contracts can read).
    -- Neither is written in a call.
    generics <- option [] (char '<' >> whitespace >> ((variable <* whitespace) `sepBy1` (char ',' >> whitespace)) <* char '>' <* whitespace)
    let typeParams = filter isTypeParam generics
        sizes = filter (not . isTypeParam) generics
    -- (a function of `impl<T> Vec<T>` has the parameters of the impl after its own)
    implParams <- declImplParams <$> getState
    let allTypes = typeParams ++ filter isTypeParam implParams
        allSizes = sizes ++ filter (not . isTypeParam) implParams
    outerParams <- declTypeParams <$> getState
    modifyState (\d -> d{declTypeParams = allTypes})
    (params, returnType, inputReqs, outputReqs) <- functHeader
    termination <- terminationClause
    fnBody <- curlyBracesParse statementBlock
    whitespace
    modifyState (\d -> d{declTypeParams = outerParams})
    let allParams = params ++ [(size, TInt) | size <- allSizes]
    return (Assign var (Val (VFunct (map fst allParams) inputReqs outputReqs (NativeFunct (Signature (map snd allParams) returnType allSizes allTypes) termination fnBody) [])))
  where
    isTypeParam name = case name of
        c : _ -> isUpper c
        [] -> False

-- (parameters) -> Type [{ input contract }] [{ output contract }], the part of a function before its termination clause
functHeader :: Parser ([(Variable, Type)], Type, [ValidationStatement], [ValidationStatement])
functHeader = do
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
    return (params, returnType, inputReqs, outputReqs)

-- trait Name { fn f(params) -> Type [{ input contract }] [{ output contract }]; ... }: what a type has to provide to
-- implement the trait. Self is the implementing type. The contracts are met by every implementation: it may ask for less
-- and promise more, which the validator checks (see TypeCheck.implementation).
traitStatement :: Parser Statement
traitStatement = do
    keyword "trait"
    whitespace
    name <- variable
    whitespace
    when (name `elem` ["Int", "Bool", "List", "Array", "Box", "Self"]) $ fail (name ++ " is a builtin type and cannot be a trait name")
    functions <- curlyBracesParse (genericStatementBlock traitFunction)
    whitespace
    when (length (nub (map traitFnName functions)) /= length functions) $ fail ("Trait " ++ name ++ " repeats a function")
    return (TraitDef name functions)
  where
    traitFunction = do
        keyword "fn"
        whitespace
        fname <- variable
        whitespace
        (params, returnType, inputReqs, outputReqs) <- functHeader
        return (TraitFn fname (map fst params) (Signature (map snd params) returnType [] []) inputReqs outputReqs)

-- impl Type { fn f ... } or impl Trait for Type { fn f ... }: the functions are named <Type>::f and <Type as Trait>::f (see
-- implFunctionName), and the checker resolves Type::f and x.f(...) to the one that is meant. Self stands for Type in them.
implStatement :: Parser Statement
implStatement = do
    keyword "impl"
    whitespace
    -- impl<T> Vec<T> { ... }: the functions are for any T. Each has the parameters of the impl, and Self is Vec<T>.
    implParams <- option [] (char '<' >> whitespace >> ((variable <* whitespace) `sepBy1` (char ',' >> whitespace)) <* char '>' <* whitespace)
    first <- variable
    whitespace
    (trait, typeName) <- option (Nothing, first) (keyword "for" >> whitespace >> variable >>= \t -> whitespace >> return (Just first, t))
    types <- declTypes <$> getState
    when (not (Map.member typeName types)) $ fail ("impl for " ++ typeName ++ ", which is not a struct or enum declared before")
    generics <- declGenerics <$> getState
    selfName <- case Map.lookup typeName generics of
        Just params -> do
            when (null implParams) $ fail ("impl for " ++ typeName ++ ", which has parameters <" ++ intercalate ", " params ++ ">: write impl<" ++ intercalate ", " params ++ "> " ++ typeName ++ "<" ++ intercalate ", " params ++ ">")
            -- (the impl names the parameters its own way: impl<U> Vec<U>)
            outerParams <- declTypeParams <$> getState
            modifyState (\d -> d{declTypeParams = filter isTypeParameter implParams})
            args <- genericArguments params
            modifyState (\d -> d{declTypeParams = outerParams})
            whitespace
            return (instanceName typeName args)
        Nothing -> do
            when (not (null implParams)) $ fail ("impl<" ++ intercalate ", " implParams ++ "> for " ++ typeName ++ ", which has no parameters")
            return typeName
    ctors <- declCtors <$> getState
    -- (`Self { ... }` is a literal of the struct with the types of the impl)
    modifyState (\d -> d{declSelf = Just selfName, declImplParams = implParams, declCtors = maybe (declCtors d) (\fields -> Map.insert selfName fields (declCtors d)) (Map.lookup typeName ctors)})
    functions <- curlyBracesParse (genericStatementBlock (implFunction typeName trait))
    modifyState (\d -> d{declSelf = Nothing, declImplParams = [], declCtors = if selfName == typeName then declCtors d else Map.delete selfName (declCtors d)})
    whitespace
    return (ImplDef trait typeName functions)
  where
    implFunction typeName trait = do
        definition <- functStatement
        case definition of
            Assign var fn -> do
                ctors <- declCtors <$> getState
                when (Map.member (typeName ++ "::" ++ var) ctors) $ fail (typeName ++ "::" ++ var ++ " is a variant, and cannot also be a function")
                return (Assign (implFunctionName typeName trait var) fn)
            other -> return other

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
    ty <- borrowed <|> try functionType <|> namedType
    whitespace
    return ty
  where
    -- &T: a parameter that is only read
    borrowed = char '&' >> whitespace >> (TRef <$> namedOrFunction)
    namedOrFunction = try functionType <|> namedType
    typeArgument = do
        whitespace
        void (char '<')
        whitespace
        element <- typeAnnotation
        void (char '>')
        return element
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
        name <- variable >>= resolveSelf
        typeParams <- declTypeParams <$> getState
        case name of
            _ | name `elem` typeParams -> return (TParam name)
            "Int" -> return TInt
            "Bool" -> return TBool
            "List" -> TList <$> typeArgument
            "Box" -> TBox <$> typeArgument
            "Array" -> do
                whitespace
                void (char '<')
                whitespace
                element <- typeAnnotation
                -- a size is a number, `?`, or a size parameter of the function, and one that is left out is `?`
                size <- option SizeAny (char ',' >> whitespace >> sizeArgument)
                whitespace
                void (char '>')
                return (TArrayOf element size)
            _ -> do
                variant <- optionMaybe (try (string "::" >> variable))
                -- a struct with sizes and types is written with them, as Packet<4> and Vec<Int, 3>
                generics <- declGenerics <$> getState
                args <- case Map.lookup name generics of
                    Just params | not (isJust variant) -> optionMaybe (try (genericArguments params))
                    _ -> return Nothing
                return (maybe (TNamed (maybe name (instanceName name) args)) (\v -> TVariant (name ++ "::" ++ v)) variant)

-- A size is a number, `?`, or a size parameter of the function
sizeArgument :: Parser Size
sizeArgument = (SizeConst . read <$> many1 digit) <|> (SizeAny <$ char '?') <|> (SizeParam <$> variable)

-- <Int, 4, n>: what a struct with sizes and types is given, a type where it has a type and a size where it has a size
genericArguments :: [Variable] -> Parser [Arg]
genericArguments params = do
    void (char '<')
    whitespace
    args <- argumentsFor params
    void (char '>')
    return args
  where
    argumentsFor [] = return []
    argumentsFor [p] = (: []) <$> argumentFor p
    argumentsFor (p : rest) = do
        a <- argumentFor p
        void (char ',')
        whitespace
        (a :) <$> argumentsFor rest
    argumentFor p
        | isTypeParameter p = ArgType <$> typeAnnotation
        | otherwise = (ArgSize <$> sizeArgument) <* whitespace

isTypeParameter :: Variable -> Bool
isTypeParameter = isTypeName

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
        <|> withFields proofApply Nothing (parensProof <|> structLiteral proof proofApply <|> try functionProof <|> try abstractProof)

infixProof :: Parser VariableProof
infixProof = infixLevels nonInfixProof (\funct lproof rproof -> FApp (CTerm (builtinFunct funct)) [lproof, rproof]) (\funct proof' -> FApp (CTerm (builtinFunct funct)) [proof'])

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
        "array" -> return NewArray
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
concreteProof = arrayLiteral (\items -> FApp (CTerm (builtinFunct ArrayFrom)) [CTerm items]) <|> (CTerm <$> value)

-- #[1, 2, 3]: an array of constants, which is the list of them read as an array
arrayLiteral :: (Value -> a) -> Parser a
arrayLiteral build = char '#' >> (build <$> vlist)

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
    withFields expressionApply methods (structLiteral expression expressionApply <|> try fExpression <|> qualifiedCall)
        <|> arrayLiteral (\items -> F (Val (builtinFunct ArrayFrom)) [Val items])
        <|> (Val <$> value)
        <|> withFields expressionApply methods (varExpression <|> parensExpression)
  where
    methods = Just (expression, methodCall)

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
    let n = sign (read val)
    when (not (inIntRange n)) $ fail "Integer literal out of range (Int is 64 bits)"
    return (VInt n)

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

-- <Type>::f(args) and <Type as Trait>::f(args): the function that an impl defines, named in full. This is how a call is written
-- when Type::f(args) is ambiguous, or when the trait function has no Self argument to tell the type by.
qualifiedCall :: Parser Expression
qualifiedCall = do
    void (char '<')
    whitespace
    owner <- selfBase <$> (variable >>= resolveSelf)
    whitespace
    trait <- optionMaybe (keyword "as" >> whitespace >> variable <* whitespace)
    void (char '>')
    void (string "::")
    function <- variable
    void (char '(')
    whitespace
    args <- expression `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    return (F (Var (implFunctionName owner trait function)) args)

fExpression :: Parser Expression
fExpression = do
    fname <- qualifiedName
    void (char '(')
    whitespace
    args <- expression `sepBy` skipWhitespace (char ',')
    whitespace
    void (char ')')
    whitespace
    return $ F (Var fname) args

infixExpression :: Parser Expression
-- TODO: Function should be Var expression like fExpression produces not Val
infixExpression = infixLevels nonInfixExpression (\funct lexpr rexpr -> F (Val (builtinFunct funct)) [lexpr, rexpr]) (\funct expr -> F (Val (builtinFunct funct)) [expr])

-- Infix operators in three levels, tightest first: `*` and `/`, then `+` and `-`, then the relations.
-- Each level associates left, so `a + 1 < b * 2` is `(a + 1) < (b * 2)`.
infixLevels :: Parser a -> (BuiltinFunct -> a -> a -> a) -> (BuiltinFunct -> a -> a) -> Parser a
infixLevels operand combine testVariant = relations
  where
    level opParser next = chainl1 next (do funct <- opParser; whitespace; return (combine funct))
    multiplicative = level multiplicativeFunct operand
    additive = level arithmeticFunct multiplicative
    relations = do
        compared <- level relationFunct additive
        option compared (do keyword "is"; whitespace; (variant, _) <- declaredCtor; whitespace; return (testVariant (Is variant) compared))

arithmeticFunct :: Parser BuiltinFunct
arithmeticFunct = do
    op <- oneOf "+-"
    whitespace
    if op == '+'
        then return Plus
        else return Minus

multiplicativeFunct :: Parser BuiltinFunct
multiplicativeFunct = (char '*' >> whitespace >> return Times) <|> (char '/' >> whitespace >> return Div) <|> (char '%' >> whitespace >> return Mod)

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
parseStatement = runParser (topLevelWrap statement) emptyDecls ""

-- Function to run the parser
parseStatementBlock :: String -> Either ParseError [Statement]
parseStatementBlock = runParser (topLevelWrap statementBlock) emptyDecls ""

-- Function to run the parser
parseExpression :: String -> Either ParseError Expression
parseExpression = runParser (topLevelWrap expression) emptyDecls ""
