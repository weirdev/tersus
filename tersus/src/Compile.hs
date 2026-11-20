module Compile
    ( SourceParts, parseSource, parseSourceParts, parseSourcePartsNoPrelude, parseWithEquality, parseWithEqualityUsing
    , lowerSource, lowerSourceNoPrelude, lowerSourceUsing
    , lowerStatements, lowerStatementsWith, elaborateStatements, completeSpecEnvs
    , sourceRequest
    ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Mir as M
import Lowering (finishProgram, finishProgramWith, lowerAccepted)
import MirMoves (finishLowered)
import LibPackage (LibPackage, libCatalog, libPackage, libUnit, libraryBoundedNames, stripDeclaredFromUnits)
import Link (linkPrograms, completeSpecEnvs)
import PackageData (ModuleId (..), LoadOptions (..), Resolver (..), defaultLoadOptions, resolverFromFiles)
import Syntax (Statement)
import ElaborateRequest (Elaborator, Extraction (..), Library, LoadKind (..), LoadRequest (..), LoadResponse (..), MirAnswer (..), Request (..), Response (..), acceptedResponse)
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
lowerSourceNoPrelude = lowerSourceUsing sourceLoader libPackage

-- A program read and checked by the loader, lowered against the supplied compiled catalog.
lowerSourceUsing :: Loader -> Result LibPackage String -> Bool -> Bool -> String -> Result M.Program String
lowerSourceUsing loader libraries noPrelude' reserving source = catalog `bindResult` \available -> case loader (sourceRequest LoadProgramAssembly noPrelude' reserving available source) of
    Unparsed e -> Error e
    NotLoaded e -> Error e
    LoadedProgram (Unresolved err) -> Error err
    LoadedProgram response ->
        stage "Validation failed: " (acceptedResponse response) `bindResult` \_ -> case response of
            Accepted _ _ (MirRefused err) -> Error ("Lowering failed: " ++ err)
            _ -> Error "internal: the loader did not answer with the program's assembly"
    AssembledProgram names response ->
        stage "Validation failed: " (acceptedResponse response) `bindResult` \_ ->
            stage "Lowering failed: " (lowerAccepted response `bindResult` \lowered -> mapResult ((,) lowered) (finishLowered lowered)) `bindResult` \(lowered, entryProgram) ->
                units names `bindResult` \selected -> linkPrograms (stripDeclaredFromUnits (ownNames lowered) selected ++ [(mainModule, entryProgram)])
    _ -> Error "internal: the loader did not answer with the program's elaboration"
  where
    units [] = Ok []
    units _ | noPrelude' = Error "internal: the loader selected assembly libraries without a catalog"
    units names = libraries `bindResult` \pkg -> flatResultMap (libUnit pkg) names
    catalog = if noPrelude' then Ok [] else mapResult libCatalog libraries

-- The names a single file declares, wherever it declares them, which the library units linked with it do not declare
-- again
ownNames :: M.Lowered -> [String]
ownNames lowered = Set.toList (Set.union (M.lowDeclared lowered) (M.lowNested lowered))

mainModule :: ModuleId
mainModule = ModuleId "main" Nothing

lowerStatements :: [Statement] -> Result M.Program String
lowerStatements = lowerStatementsWith sourceElaborator

-- A program as given, with no libraries in front of it
lowerStatementsWith :: Elaborator -> [Statement] -> Result M.Program String
lowerStatementsWith elaborator stmts = lowerAccepted (elaborator (statementsRequest stmts)) `bindResult` finishProgramWith (libraryBoundedNames (length stmts))

-- The unit the elaborator lowers a program given as statements to, not finished
elaborateStatements :: [Statement] -> Result M.Lowered String
elaborateStatements stmts = lowerAccepted (sourceElaborator (statementsRequest stmts))

statementsRequest :: [Statement] -> Request
statementsRequest stmts = Request mainModule False False NoInterface [] [] [] [stmts]

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
