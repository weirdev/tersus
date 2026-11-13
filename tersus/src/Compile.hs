module Compile
    ( SourceParts, parseSource, parseSourceParts, parseSourcePartsNoPrelude, parseWithEquality, parseWithEqualityUsing
    , lowerSource, lowerSourceNoPrelude, lowerSourceUsing
    , lowerStatements, lowerStatementsWith, elaborateStatements, completeSpecEnvs
    , sourceRequest
    ) where

import qualified Data.Set as Set
import qualified Mir as M
import Lowering (finishProgram, lowerAccepted)
import MirMoves (finishLowered)
import LibPackage (libCatalog, libPackage, libSelection, stripDeclaredFromUnits)
import Link (linkPrograms, completeSpecEnvs)
import PackageData (ModuleId (..), LoadOptions (..), Resolver (..), defaultLoadOptions, resolverFromFiles)
import Syntax (Statement)
import ElaborateRequest (Elaborator, Extraction (..), Library, LoadKind (..), LoadRequest (..), LoadResponse (..), Request (..), Response (..), acceptedResponse)
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
        stage "Validation failed: " (acceptedResponse response) `bindResult` \_ ->
            selection (selectedOf response) `bindResult` \units ->
                stage "Lowering failed: " (lowerAccepted response `bindResult` \lowered -> mapResult ((,) lowered) (finishLowered lowered)) `bindResult` \(lowered, entryProgram) ->
                    linkPrograms (stripDeclaredFromUnits (ownNames lowered) units ++ [(mainModule, entryProgram)])
    _ -> Error "internal: the loader did not answer with the program's elaboration"
  where
    selectedOf response = case response of
        Accepted _ selected _ -> selected
        _ -> []
    selection [] = Ok []
    selection selected = mapResult (`libSelection` selected) libPackage
    catalog = if noPrelude' then Ok [] else mapResult libCatalog libPackage

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
lowerStatementsWith elaborator stmts = lowerAccepted (elaborator (statementsRequest stmts)) `bindResult` finishProgram

-- The unit the elaborator lowers a program given as statements to, not finished
elaborateStatements :: [Statement] -> Result M.Lowered String
elaborateStatements stmts = lowerAccepted (sourceElaborator (statementsRequest stmts))

statementsRequest :: [Statement] -> Request
statementsRequest stmts = Request mainModule False False NoInterface [] [] [] [stmts]

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
