{-# LANGUAGE PatternSynonyms #-}
module Compile
    ( SourceParts, parseSource, parseSourceParts, parseSourcePartsNoPrelude, parseWithEquality, parseWithEqualityUsing
    , lowerSource, lowerSourceNoPrelude, lowerSourceUsing
    , lowerStatements, lowerStatementsWith, elaborateStatements, completeSpecEnvs
    , sourceRequest, ownNames
    ) where

import qualified Mir as M
import Lowering (finishProgram, lowerAccepted)
import MirMoves (finishLowered)
import LibPackage (libCatalog, libPackage, libSelection, stripDeclaredFromUnits, withoutReplacedEq)
import Link (linkPrograms, completeSpecEnvs)
import PackageData (ModuleId (..), LoadOptions (..), Resolver (..), defaultLoadOptions, resolverFromFiles)
import Syntax (Elaborated (..), pattern Elaborated, Expression (..), FunctBody (..), Statement (..), Value (..))
import ElaborateRequest (Elaborator, Extraction (..), Library, LoadKind (..), LoadRequest (..), LoadResponse (..), Request (..), Response (..), acceptedElaboration)
import ElaboratorTool (Loader, sourceElaborator, sourceLoader)
import Modules (librarySources)
import Utils

-- A program as read: the compiler libraries it is read with (in front of it), their statements, and its own
type SourceParts = ([String], [Statement], [Statement])

-- A single file the loader written in Tersus reads (and checks, for a program): no package, the libraries' sources, and
-- the compiled libraries the elaborator selects among
sourceRequest :: LoadKind -> Bool -> Bool -> [Library] -> String -> LoadRequest
sourceRequest kind noPrelude' reserving catalog source =
    LoadRequest kind reserving ((resolverFromFiles [("<source>", source)]) {resolverOptions = defaultLoadOptions {noPrelude = noPrelude'}}) (Just ("<source>", True))
        librarySources catalog

parseSource :: String -> Result [Statement] String
parseSource source = mapResult (\(_, library, body) -> library ++ body) (parseSourceParts True source)

parseSourceParts :: Bool -> String -> Result SourceParts String
parseSourceParts = parseSourcePartsNoPrelude False

parseSourcePartsNoPrelude :: Bool -> Bool -> String -> Result SourceParts String
parseSourcePartsNoPrelude noPrelude' reserving source = case sourceLoader (sourceRequest LoadParse noPrelude' reserving [] source) of
    ParsedSource names library body -> Ok (names, library, body)
    Unparsed e -> Error e
    NotLoaded e -> Error e
    _ -> Error "internal: the loader did not answer with the program as read"

-- The program with the type, clone and equality libraries it calls for in front of it
parseWithEquality :: String -> Either String [Statement]
parseWithEquality = parseWithEqualityUsing sourceLoader

parseWithEqualityUsing :: Loader -> String -> Either String [Statement]
parseWithEqualityUsing loader source = case loader (sourceRequest LoadEquality False False [] source) of
    ParsedSource _ library body -> Right (library ++ body)
    Unparsed e -> Left e
    NotLoaded e -> Left e
    _ -> Left "internal: the loader did not answer with the program as read"

lowerSource :: Bool -> String -> Result M.Program String
lowerSource = lowerSourceNoPrelude False

lowerSourceNoPrelude :: Bool -> Bool -> String -> Result M.Program String
lowerSourceNoPrelude = lowerSourceUsing sourceLoader

-- A program read and checked by the loader, lowered with the libraries the elaborator selected, which are linked
lowerSourceUsing :: Loader -> Bool -> Bool -> String -> Result M.Program String
lowerSourceUsing loader noPrelude' reserving source = catalog `bindResult` \libraries -> case loader (sourceRequest LoadProgram noPrelude' reserving libraries source) of
    Unparsed e -> Error e
    NotLoaded e -> Error e
    LoadedProgram (Unresolved err) -> Error err
    LoadedProgram response ->
        stage "Validation failed: " (acceptedElaboration response) `bindResult` \(Elaborated stmts _) ->
            selection (selectedOf response) `bindResult` \(ifaces, units) ->
                stage "Lowering failed: " (lowerAccepted (withoutReplacedEq stmts ifaces) response `bindResult` finishLowered) `bindResult` \entryProgram ->
                    linkPrograms (stripDeclaredFromUnits (ownNames stmts) units ++ [(mainModule, entryProgram)])
    _ -> Error "internal: the loader did not answer with the program's elaboration"
  where
    selectedOf response = case response of
        Accepted _ _ selected -> selected
        _ -> []
    selection [] = Ok ([], [])
    selection selected = mapResult (`libSelection` selected) libPackage
    catalog = if noPrelude' then Ok [] else mapResult libCatalog libPackage

-- The functions an elaborated program defines at the top, those with bounds and the functions of its impls included
elaboratedFunctions :: Elaborated -> [String]
elaboratedFunctions (Elaborated stmts _) = concatMap defined stmts
  where
    defined stmt = case stmt of
        Assign name (Val VFunct{}) -> [name]
        BoundedDef _ inner -> defined inner
        _ -> []

-- The names a single file declares, which the library units linked with it do not declare again
ownNames :: [Statement] -> [String]
ownNames stmts = concatMap declaredNames stmts ++ concatMap definedFunctionNames stmts

mainModule :: ModuleId
mainModule = ModuleId "main" Nothing

lowerStatements :: [Statement] -> Result M.Program String
lowerStatements = lowerStatementsWith sourceElaborator

-- A program as given, with no libraries in front of it
lowerStatementsWith :: Elaborator -> [Statement] -> Result M.Program String
lowerStatementsWith elaborator stmts = lowerAccepted [] (elaborator (statementsRequest stmts)) `bindResult` finishProgram

elaborateStatements :: [Statement] -> Result Elaborated String
elaborateStatements stmts = acceptedElaboration (sourceElaborator (statementsRequest stmts))

statementsRequest :: [Statement] -> Request
statementsRequest stmts = Request mainModule False False NoInterface [] [] [] [stmts]

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)

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

-- The functions a program defines at its top, in its impls included
definedFunctionNames :: Statement -> [String]
definedFunctionNames stmt = case stmt of
    Assign name (Val VFunct{}) -> [name]
    ImplDef _ _ _ _ _ body -> concatMap definedFunctionNames body
    BoundedDef _ inner -> definedFunctionNames inner
    _ -> []

