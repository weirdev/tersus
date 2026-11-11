{-# LANGUAGE PatternSynonyms #-}
module SourceParse
    ( SourceParts, parseSourcePartsWith, parseWithEqualityWith
    , parsedLibraries, probeDecls
    , librariesFor, reservedName, reservedError, declaredNames, definedFunctionNames
    ) where

import Data.Char (isAlphaNum)
import Data.List (intercalate)
import System.IO.Unsafe (unsafePerformIO)
import Seed (cachedParserSeed)
import ParsedFile
import qualified ParserSeed
import LibParsed (declsForLibModules, libModules, libParsed, statementsForLibModules)
import PreludeSource (cloneSource, eqSource, mapSource, preludeSource, setSource, stringSource, typesSource)
import Syntax
import Types
import Utils

type SourceParts = ([String], [Statement], [Statement])
type FileParser = Decls -> String -> Either String (ParsedFile, Decls)

libraryNames :: [String] -> Either String [String]
libraryNames displays =
    let names = [name | display <- displays, (name, shown, _) <- libModules, display == shown]
     in if length names /= length displays then Left ("Unknown implicit library selection: " ++ show displays) else Right names

parsedLibraries :: [String] -> Either String ([Statement], Decls)
parsedLibraries names = do
    parsed <- libParsed
    Right (statementsForLibModules parsed names, declsForLibModules parsed names)

probeDecls :: Either String Decls
probeDecls = do
    parsed <- libParsed
    Right (declsForLibModules parsed ["prelude", "string", "map", "set"])

probeFile :: FileParser -> Decls -> String -> Either String (ParsedFile, Decls)
probeFile parser seeded source = case parser seeded source of
    Right parsed -> Right parsed
    Left e | ParserSeed.toolFailure e -> Left e
    Left e -> case parser (emptyDecls{declLocate = declLocate seeded}) source of
        Right parsed -> Right parsed
        Left plainError | ParserSeed.toolFailure plainError -> Left plainError
        Left _ -> Left e

-- Do not force immutable library CAFs after a transient seed failure.
{-# NOINLINE parseSourcePartsWith #-}
parseSourcePartsWith :: FileParser -> Bool -> Bool -> String -> Result SourceParts String
parseSourcePartsWith parser reserving noPrelude source = unsafePerformIO $ do
    seed <- cachedParserSeed
    pure $ case seed of
        Error e -> Error (ParserSeed.failure e)
        Ok _ -> readSource
  where
    readSource
        | noPrelude = case parser (locating emptyDecls) source of
            Left e -> Error (ParserSeed.stageParseError e)
            Right (ParsedFile imports body, _)
                | not (null imports) -> Error ("imports are not linked yet: " ++ intercalate ", " (map (renderPath . importPath) imports))
                | reserving, Just name <- reservedName body -> Error (reservedError name)
                | otherwise -> Ok ([], [], body)
        | otherwise = case probeDecls >>= (\declared -> probeFile parser (locating declared) source) of
            Left e -> Error (ParserSeed.stageParseError e)
            Right (probedFile, _) -> case libraryNames (map fst (librariesFor (fileBody probedFile))) of
                Left e -> Error e
                Right names -> case parsedLibraries names of
                    Left e -> Error e
                    Right (library, declared) -> case parser (locating declared) source of
                        Left e -> Error (ParserSeed.stageParseError e)
                        Right (ParsedFile imports body, _)
                            | not (null imports) -> Error ("imports are not linked yet: " ++ intercalate ", " (map (renderPath . importPath) imports))
                            | reserving, Just name <- reservedName body -> Error (reservedError name)
                            | otherwise -> Ok (names, library, body)

{-# NOINLINE parseWithEqualityWith #-}
parseWithEqualityWith :: FileParser -> String -> Either String [Statement]
parseWithEqualityWith parser source = unsafePerformIO $ do
    seed <- cachedParserSeed
    pure $ case seed of
        Error e -> Left (ParserSeed.failure e)
        Ok _ -> readSource
  where
    readSource = do
        declared <- probeDecls
        (probed, _) <- probeFile parser declared source
        names <- libraryNames (map fst (librariesFor (fileBody probed)))
        (library, seed) <- parsedLibraries [name | name <- names, name `elem` ["types", "clone", "eq"]]
        (parsed, _) <- parser seed source
        if null (fileImports parsed) then Right (library ++ fileBody parsed) else Left "import statements must come before any declaration in a file"

reservedError :: String -> String
reservedError name = "Type error: " ++ name ++ " is reserved: native code makes a list of the struct List and the functions list... of lib/lists.tersus, and a Box of the struct Box and the functions box... of lib/box.tersus, so a program does not declare names like them"

-- A name the program declares that native code uses for lists (see MirLists)
reservedName :: [Statement] -> Maybe String
reservedName = reservedAmong (["List", "Box"] ++ nativeHelperNames)

nativeHelperNames :: [String]
nativeHelperNames = ["listNew", "listLen", "listGet", "listFirst", "listLast", "listPop", "listSet", "listPush", "listFilled", "boxNew", "boxUnbox"]

reservedAmong :: [String] -> [Statement] -> Maybe String
reservedAmong names stmts = case [name | stmt <- stmts, name <- declared stmt, name `elem` names] of
    name : _ -> Just name
    [] -> Nothing
  where
    declared stmt = case stmt of
        Assign name (Val VFunct{}) -> [name]
        StructDef name _ _ _ -> [name]
        EnumDef name _ -> [name]
        TraitDef name _ _ -> [name]
        BoundedDef _ (Assign name _) -> [name]
        _ -> []

-- The libraries that a program has in front of it, in order, unless it declares their names itself, so a program that has a `Vec` of its own is
-- unchanged: lib/eq.tersus (the trait `Eq` that `=` calls, whose impls are made only for the types a program compares) unless it declares a trait `Eq`, lib/prelude.tersus (the traits `Sequence`, `Growable`, `Clone`, `Copy`, `Drop`, `Deref` and `Hash`, with `hashCombine`) if it mentions any of them (or
-- `hashCombine`), lib/string.tersus (the struct `String` that a string literal is a value of, which needs the traits) if it mentions `String` or
-- has a literal, lib/map.tersus (the struct `HashMap`) if it mentions `HashMap`, and lib/set.tersus (the struct `HashSet`,
-- which is made of a map) if it mentions `HashSet`.
-- The decision is made from the program as it was read (see parseSourceWith): the names it declares and the names it mentions are the
-- ones in its statements, so a name written in a comment or in the text of a literal, which is not in the program that was read, decides nothing.
librariesFor :: [Statement] -> [(String, String)]
librariesFor stmts = [("the list and Box types", typesSource) | not (declares ["List"]) && not (declares ["Box"])] ++ [("the clone library", cloneSource) | not (declares ["Clone"])] ++ [("the equality library", eqSource) | not (declares ["Eq"])] ++ [("the prelude", preludeSource) | prelude] ++ [("the string library", stringSource) | strings] ++ [("the map library", mapSource) | maps] ++ [("the set library", setSource) | sets]
  where
    declared = concatMap declaredNames stmts
    mentioned = concatMap statementNames stmts
    declares candidates = any (`elem` declared) candidates
    preludeFree = not (declares preludeTraits)
    strings = preludeFree && not (declares ["String"]) && ("String" `elem` mentioned || hasStringLiteral stmts)
    maps = preludeFree && not (declares ["HashMap"]) && ("HashMap" `elem` mentioned || sets)
    sets = preludeFree && not (declares ["HashSet"]) && "HashSet" `elem` mentioned
    prelude = preludeFree && (strings || maps || sets || any (`elem` mentioned) (preludeTraits ++ ["hashCombine"]))
    preludeTraits = ["Sequence", "Growable", "Clone", "Copy", "Drop", "Deref", "Hash"]

-- The names a program declares as a struct, an enum or a trait, wherever it declares them
declaredNames :: Statement -> [String]
declaredNames stmt = case stmt of
    StructDef name _ _ _ -> [name]
    EnumDef name _ -> [name]
    TraitDef name _ _ -> [name]
    Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> concatMap declaredNames body
    Block body -> concatMap declaredNames body
    If _ yes no -> concatMap declaredNames (yes ++ no)
    While _ _ _ body -> concatMap declaredNames body
    ImplDef _ _ _ _ _ body -> concatMap declaredNames body
    BoundedDef _ inner -> declaredNames inner
    _ -> []

-- Whether the program as it was read has a string literal in it: the application of the builtin that
-- only the reading of a literal writes, in code or in a proof
definedFunctionNames :: Statement -> [String]
definedFunctionNames stmt = case stmt of
    Assign name (Val VFunct{}) -> [name]
    ImplDef _ _ _ _ _ body -> concatMap definedFunctionNames body
    BoundedDef _ inner -> definedFunctionNames inner
    _ -> []

hasStringLiteral :: [Statement] -> Bool
hasStringLiteral = any statementLiteral
  where
    statementLiteral stmt = case stmt of
        Assign _ e -> expressionLiteral e
        AssignDeref lhs e -> expressionLiteral lhs || expressionLiteral e
        Let _ e -> expressionLiteral e
        Return e -> expressionLiteral e
        ValidationStatement v -> validationLiteral v
        StructDef _ _ _ invariant -> any validationLiteral invariant
        AxiomDef _ _ ins outs -> any validationLiteral (ins ++ outs)
        ProofDef _ _ ins outs body -> any validationLiteral (ins ++ outs ++ body)
        Block body -> any statementLiteral body
        If c yes no -> expressionLiteral c || any statementLiteral (yes ++ no)
        While c invariant _ body -> expressionLiteral c || any validationLiteral invariant || any statementLiteral body
        TraitDef _ _ fns -> any traitFnLiteral fns
        ImplDef _ _ _ _ _ body -> any statementLiteral body
        BoundedDef _ inner -> statementLiteral inner
        _ -> False
    traitFnLiteral fn = any validationLiteral (traitFnRequires fn ++ traitFnEnsures fn)
    validationLiteral v = case v of
        Rewrite rule -> ruleLiteral rule
        ProofAssert p -> proofLiteral p
        AssignProofVar _ e -> expressionLiteral e
        Assume p -> proofLiteral p
    ruleLiteral rule = case rule of
        Refl p -> proofLiteral p
        CheckGtZero p -> proofLiteral p
        CheckRel p -> proofLiteral p
        UserRewrite _ ps -> any proofLiteral ps
        _ -> False
    expressionLiteral e = case e of
        Val v -> valueLiteral v
        F f args -> expressionLiteral f || any expressionLiteral args
        _ -> False
    valueLiteral v = case v of
        VList vs -> any valueLiteral vs
        VData _ fields -> any (valueLiteral . snd) fields
        VFunct _ ins outs body _ -> any validationLiteral (ins ++ outs) || functBodyLiteral body
        _ -> False
    functBodyLiteral body = case body of
        NativeFunct _ _ stmts -> any statementLiteral stmts
        BuiltinFunct b -> b == BytesFrom
    proofLiteral p = case p of
        FApp f args -> proofLiteral f || any proofLiteral args
        CTerm v -> valueLiteral v
        Forall _ guards body -> any proofLiteral guards || proofLiteral body
        _ -> False

-- Every name a statement mentions, in the places the program that was read has one: a type, a variable or a
-- function it calls, a field, the name of a declaration itself. A name in the program may be written in full
-- (`String::fromInt`, `<Vec as Sequence>::size`, `Vec<Int>`), so the names it is made of are the parts of it.
statementNames :: Statement -> [String]
statementNames stmt = case stmt of
    Assign name e -> nameParts name ++ expressionNames e
    AssignDeref lhs e -> expressionNames lhs ++ expressionNames e
    Let name e -> nameParts name ++ expressionNames e
    Return e -> expressionNames e
    ValidationStatement v -> validationNames v
    StructDef name params fields invariant -> nameParts name ++ params ++ concatMap field fields ++ concatMap validationNames invariant
      where field (f, t) = nameParts f ++ typeNames t
    EnumDef name variants -> nameParts name ++ concatMap variant variants
      where variant (v, fields) = nameParts v ++ concatMap field fields
            field (f, t) = nameParts f ++ typeNames t
    AxiomDef name args ins outs -> nameParts name ++ args ++ concatMap validationNames (ins ++ outs)
    ProofDef name args ins outs body -> nameParts name ++ args ++ concatMap validationNames (ins ++ outs ++ body)
    Block body -> concatMap statementNames body
    If c yes no -> expressionNames c ++ concatMap statementNames (yes ++ no)
    While c invariant term body -> expressionNames c ++ concatMap validationNames invariant ++ terminationNames term ++ concatMap statementNames body
    TraitDef name params fns -> nameParts name ++ params ++ concatMap traitFnNames fns
    ImplDef trait args owner selfType _bounds body -> maybe [] nameParts trait ++ concatMap argNames args ++ nameParts owner ++ typeNames selfType ++ concatMap statementNames body
    BoundedDef bounds inner -> concatMap bound bounds ++ statementNames inner
      where bound (p, t, ts) = nameParts p ++ nameParts t ++ concatMap typeNames ts
    CopyDef name -> nameParts name
    LinearDef name -> nameParts name
    ExternDef name -> nameParts name
    DropDef name -> nameParts name
    Dissolve name -> nameParts name
    Mark _ _ -> []

traitFnNames :: TraitFn -> [String]
traitFnNames fn = nameParts (traitFnName fn) ++ traitFnParams fn ++ signatureNames (traitFnSignature fn) ++ concatMap validationNames (traitFnRequires fn ++ traitFnEnsures fn)

signatureNames :: Signature -> [String]
signatureNames (Signature params result sizes types writes fromNames) = concatMap typeNames (result : params) ++ sizes ++ types ++ writes ++ fromNames

terminationNames :: Maybe Termination -> [String]
terminationNames term = case term of
    Just (Shrinks e) -> expressionNames e
    Just (Counting e) -> expressionNames e
    Just (Parts e) -> expressionNames e
    Just (Recursing inner) -> terminationNames inner
    _ -> []

validationNames :: ValidationStatement -> [String]
validationNames v = case v of
    Rewrite rule -> ruleNames rule
    ProofAssert p -> proofNames p
    AssignProofVar name e -> nameParts name ++ expressionNames e
    Assume p -> proofNames p

ruleNames :: RwRule -> [String]
ruleNames rule = case rule of
    Refl p -> proofNames p
    Eval name -> nameParts name
    CheckGtZero p -> proofNames p
    CheckRel p -> proofNames p
    UserRewrite name ps -> nameParts name ++ concatMap proofNames ps
    EvalAll -> []

expressionNames :: Expression -> [String]
expressionNames e = case e of
    Val v -> valueNames v
    Var name -> nameParts name
    F f args -> expressionNames f ++ concatMap expressionNames args

valueNames :: Value -> [String]
valueNames v = case v of
    VList vs -> concatMap valueNames vs
    VData name fields -> nameParts name ++ concatMap field fields
      where field (f, x) = nameParts f ++ valueNames x
    VFunct params ins outs body exported -> params ++ concatMap validationNames (ins ++ outs) ++ functBodyNames body ++ concatMap proofNames exported
    VFnRef name -> nameParts name
    _ -> []

functBodyNames :: FunctBody -> [String]
functBodyNames body = case body of
    NativeFunct sig term stmts -> signatureNames sig ++ terminationNames term ++ concatMap statementNames stmts
    BuiltinFunct b -> builtinNames b

builtinNames :: BuiltinFunct -> [String]
builtinNames b = case b of
    Ctor name args fields -> nameParts name ++ concatMap argNames args ++ fields
    Field owner field -> maybe [] nameParts owner ++ [field]
    Is name -> nameParts name
    Project name field -> nameParts name ++ [field]
    Cast name -> nameParts name
    _ -> []

proofNames :: Proof String -> [String]
proofNames p = case p of
    FApp f args -> proofNames f ++ concatMap proofNames args
    ATerm name -> nameParts name
    CTerm v -> valueNames v
    Forall name guards body -> nameParts name ++ concatMap proofNames guards ++ proofNames body
    BVar name -> nameParts name

typeNames :: Type -> [String]
typeNames t = case t of
    TList inner -> typeNames inner
    TArrayOf inner size -> typeNames inner ++ sizeNames size
    TBox inner -> typeNames inner
    TFn params result -> concatMap typeNames (result : params)
    TNamed name args -> nameParts name ++ concatMap argNames args
    TVariant name -> nameParts name
    TParam name -> [name]
    TAddr inner -> typeNames inner
    TBlock inner -> typeNames inner
    TUninit inner -> typeNames inner
    TRef inner -> typeNames inner
    TMutRef inner -> typeNames inner
    TForall sizes types inner -> sizes ++ types ++ typeNames inner
    _ -> []

argNames :: Arg -> [String]
argNames arg = case arg of
    ArgSize size -> sizeNames size
    ArgType t -> typeNames t

sizeNames :: Size -> [String]
sizeNames size = case size of
    SizeParam name -> [name]
    _ -> []

-- The names a name as it is written in a program is made of: the parts of a qualified or rendered name
nameParts :: String -> [String]
nameParts name = case dropWhile (not . isNameChar) name of
    "" -> []
    rest -> let (part, more) = span isNameChar rest in part : nameParts more
  where

    isNameChar c = isAlphaNum c || c == '_'
