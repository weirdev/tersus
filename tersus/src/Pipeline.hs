module Pipeline
    ( parseSource
    , compileSource
    , ownedSource
    , nativeProgram
    , validateStatements
    , runStatements
    , assumptionsOf
    ) where

import qualified Mir as M
import MirOwnership (insertOwnership)
import MirVerify (verifyProgram)
import MirEval (MirValue, runProgram)
import MirGhost (eraseGhosts, withoutUninit)
import MirLower (lowerElaborated, lowerLibrary)
import MirValidate (Validated, validateProgram)
import Data.Char (isAlphaNum)
import Parse (Decls, emptyDecls, locating, parseStatementBlockWith)
import MirLists (lowerLists)
import PreludeSource (boxSource, listsSource, preludeSource, stringSource)
import Pretty (renderVarProof)
import Syntax (Expression (..), FunctBody (..), Proof (..), RwRule (..), Statement (..), Termination (..), TraitFn (..), ValidationStatement (..), Value (..), exprToProof)
import TypeCheck (elaborate)
import Types (Arg (..), BuiltinFunct (..), Signature (..), Size (..), Type (..))
import Utils

-- The stages a program goes through, each built on the one before and each giving back what the next needs:
--
--   source -> AST (parseSource) -> checked AST with the type of every expression (elaborate: types checked,
--          each `shrinks` resolved) -> MIR (lowerElaborated) -> validated MIR (validateProgram) -> executed (runProgram)
--                                                                    or -> owned MIR (ownedSource) -> LLVM IR (the emitter written in Tersus, see Bootstrap)
--
-- The validated MIR has its permissions (ghost values, POINTERS.md) taken out by `eraseGhosts` before anything runs it or makes native code of it.
--
-- The program is type checked once, by `elaborate`; the lowering takes its result (the statements and the
-- expression types, so it infers nothing itself) and the validator the MIR. Errors name
-- the stage that refused the program, as the command line prints them.

parseSource :: String -> Result [Statement] String
parseSource source = parseSourceWith True source

-- A program is first read with no library in front of it but the declarations the prelude and the
-- string library make known to it (probeDecls), so that what in it needs a library can be read at
-- all: a string literal needs the shape of the library `String`, and an impl of a trait of the
-- prelude needs the types of that trait. Which libraries it has is decided from that reading
-- (librariesFor), and the program is then read again exactly as it was before, with the
-- declarations of the libraries it has in front of it or with none. A program that declares one
-- of those names itself declares it as it is read, over the library's, so its reading is the one
-- that decides, and the second reading is the one that refuses what the library would have allowed.
-- (the library of lists is the one program that may use the names that a program may not)
parseSourceWith :: Bool -> String -> Result [Statement] String
parseSourceWith reserving source = case parseStatementBlockWith (locating probeDecls) source of
    Left err -> Error ("Parse error: " ++ show err)
    Right (probed, _) -> finish (librariesFor probed)
  where
    finish [] = case parseStatementBlockWith (locating emptyDecls) source of
        Left err -> Error ("Parse error: " ++ show err)
        Right (stmts, _) -> checked stmts
    finish texts = case readLibraries texts emptyDecls of
        Left err -> Error err
        Right (library, declared) -> case parseStatementBlockWith (locating declared) source of
            Left err -> Error ("Parse error: " ++ show err)
            Right (stmts, _) -> checked stmts `bindResult` \stmts' -> Ok (library ++ stmts')
    checked stmts = if reserving then maybe (Ok stmts) (\name -> Error ("Type error: " ++ name ++ " is reserved: native code makes a list of the struct StdList and the functions stdList... of lib/lists.tersus, and a Box of the struct StdBox and the functions stdBox... of lib/box.tersus, so a program does not declare names like them")) (reservedName stmts) else Ok stmts

readLibraries :: [(String, String)] -> Decls -> Either String ([Statement], Decls)
readLibraries [] declared = Right ([], declared)
readLibraries ((name, text) : more) declared = case parseStatementBlockWith declared text of
    Left err -> Left ("Parse error in " ++ name ++ ": " ++ show err)
    Right (stmts, declared') -> fmap (\(rest, final) -> (stmts ++ rest, final)) (readLibraries more declared')

-- The declarations the prelude and the string library make, which a program is first read with (see parseSourceWith)
probeDecls :: Decls
probeDecls = case readLibraries [("the prelude", preludeSource), ("the string library", stringSource)] emptyDecls of
    Right (_, declared) -> declared
    Left _ -> emptyDecls

-- A name the program declares that native code uses for lists (see MirLists)
reservedName :: [Statement] -> Maybe String
reservedName stmts = case [name | stmt <- stmts, name <- declared stmt, reserved name] of
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
    reserved name = name `elem` ["StdList", "StdBox"] || take 7 name == "stdList" || take 6 name == "stdBox"

-- The libraries that a program has in front of it, in order, unless it declares their names itself, so a program that has a `Vec` of its own is
-- unchanged: lib/prelude.tersus (the traits `Sequence`, `Growable`, `Clone`, `Copy`, `Drop` and `Deref`) if it mentions any of them, and
-- lib/string.tersus (the struct `String` that a string literal is a value of, which needs the traits) if it mentions `String` or has a literal.
-- The decision is made from the program as it was read (see parseSourceWith): the names it declares and the names it mentions are the
-- ones in its statements, so a name written in a comment or in the text of a literal, which is not in the program that was read, decides nothing.
librariesFor :: [Statement] -> [(String, String)]
librariesFor stmts = [("the prelude", preludeSource) | prelude] ++ [("the string library", stringSource) | strings]
  where
    declared = concatMap declaredNames stmts
    mentioned = concatMap statementNames stmts
    declares candidates = any (`elem` declared) candidates
    preludeFree = not (declares preludeTraits)
    strings = preludeFree && not (declares ["String"]) && ("String" `elem` mentioned || hasStringLiteral stmts)
    prelude = preludeFree && (strings || any (`elem` mentioned) preludeTraits)
    preludeTraits = ["Sequence", "Growable", "Clone", "Copy", "Drop", "Deref"]

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
    ImplDef _ _ _ _ body -> concatMap declaredNames body
    BoundedDef _ inner -> declaredNames inner
    _ -> []

-- Whether the program as it was read has a string literal in it: the application of the builtin that
-- only the reading of a literal writes (Parse.stringLiteralOf), in code or in a proof
hasStringLiteral :: [Statement] -> Bool
hasStringLiteral = any statementLiteral
  where
    statementLiteral stmt = case stmt of
        Assign _ e -> expressionLiteral e
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
        ImplDef _ _ _ _ body -> any statementLiteral body
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
    ImplDef trait args owner selfType body -> maybe [] nameParts trait ++ concatMap argNames args ++ nameParts owner ++ typeNames selfType ++ concatMap statementNames body
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
signatureNames (Signature params result sizes types) = concatMap typeNames (result : params) ++ sizes ++ types

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

-- What a program takes on trust (POINTERS.md, Assumptions): each `assume e;`, each `Block::assume(p, n)` (the permission to memory it did not
-- allocate), each `extern fn` (whose contract is assumed) and each `axiom`, in the program and the libraries in front of it, with the place it is written at (a library's have none). The
-- validator proves everything else, so this is the list to read to know what a program's proofs rest on.
assumptionsOf :: String -> Result [String] String
assumptionsOf source = mapResult (snd . statements Nothing) (parseSource source)
  where
    statements place = foldl (\(p, found) stmt -> let (p', more) = statement p stmt in (p', found ++ more)) (place, [])
    statement place stmt = case stmt of
        Mark line column -> (Just (line, column), [])
        ValidationStatement (Assume p) -> (place, [at place ("assume " ++ renderVarProof p)])
        AxiomDef name args _ _ -> (place, [at place ("axiom " ++ name ++ "(" ++ commas args ++ ")")])
        ExternDef name -> (place, [at place ("extern fn " ++ name)])
        Assign _ (Val (VFunct _ _ _ (NativeFunct _ _ body) _)) -> (place, snd (statements place body))
        Assign _ e -> (place, expression place e)
        Let _ e -> (place, expression place e)
        Return e -> (place, expression place e)
        Block body -> (place, snd (statements place body))
        If c yes no -> (place, expression place c ++ snd (statements place yes) ++ snd (statements place no))
        While c _ _ body -> (place, expression place c ++ snd (statements place body))
        ImplDef _ _ _ _ body -> (place, snd (statements place body))
        BoundedDef _ s -> (place, snd (statement place s))
        _ -> (place, [])
    expression place e = case e of
        F (Var "Block::assume") args -> at place (renderVarProof (exprToProof e)) : concatMap (expression place) args
        F f args -> concatMap (expression place) (f : args)
        _ -> []
    at place text = maybe "in a library: " (\(line, column) -> "line " ++ show line ++ ":" ++ show column ++ ": ") place ++ text
    commas = foldr1' (\a b -> a ++ ", " ++ b)
    foldr1' _ [] = ""
    foldr1' f xs = foldr1 f xs

-- The MIR of a program that passes every check
compileSource :: String -> Result M.Program String
compileSource = compileWith True

compileWith :: Bool -> String -> Result M.Program String
compileWith reserving source =
    parseSourceWith reserving source `bindResult` \stmts ->
        stage "Validation failed: " (elaborate stmts) `bindResult` \elaborated ->
            stage "Lowering failed: " ((if reserving then lowerElaborated else lowerLibrary) elaborated) `bindResult` \program ->
                stage "Validation failed: " (validateProgram program) `bindResult` \_ ->
                    eraseGhosts program

-- The MIR of a program that passes every check, with who owns each value made explicit (MirOwnership), for native code
ownedSource :: String -> Result M.Program String
ownedSource source =
    compileSource source `bindResult` \program ->
        let owned = insertOwnership (nativeProgram program)
         in stage "Ownership failed: " (verifyProgram owned) `bindResult` \_ -> Ok owned

-- The program that native code is made of: a validated program with each list and Box made of the library's structs (see MirLists), and each
-- Uninit<T> a T (it is laid out as one: an empty one is the words of a T cleared, which own nothing)
nativeProgram :: M.Program -> M.Program
nativeProgram = lowerLists listLibrary . withoutUninit

-- The library of lists and Boxes (lib/lists.tersus and lib/box.tersus), compiled and validated once
listLibrary :: M.Program
listLibrary = case compileWith False (listsSource ++ "\n" ++ boxSource) of
    Ok program -> program
    Error e -> error ("lib/lists.tersus and lib/box.tersus do not compile: " ++ e)

-- Checks and validates a program given as statements
validateStatements :: [Statement] -> Result Validated String
validateStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` validateProgram

-- Runs a program given as statements, once it type checks, without validating it
runStatements :: [Statement] -> Result (Maybe MirValue) String
runStatements stmts =
    elaborate stmts `bindResult` \elaborated ->
        lowerElaborated elaborated `bindResult` eraseGhosts `bindResult` runProgram

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
