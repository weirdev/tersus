module Compile
    ( SourceParts, parseSource, parseSourceParts, parseSourcePartsNoPrelude, parseWithEquality, parseWithEqualityUsing
    , parseWithEqualityParts, parseWithEqualityPartsUsing
    , lowerSource, lowerSourceNoPrelude, lowerSourceUsing
    , lowerStatements, lowerStatementsWith, elaborateStatements, completeSpecEnvs
    , lowerParts, lowerPartsWith, elaborateParts
    , sourceRequest
    ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Mir as M
import Lowering (finishProgram, finishProgramWith, lowerAccepted)
import MirMoves (finishLowered)
import LibPackage (LibPackage, libCatalog, libPackage, libUnit, libraryBoundedNames, stripDeclaredFromUnits)
import Link (completeSpecEnvs, linkWithLibraries)
import PackageData (ModuleId (..), LoadOptions (..), Resolver (..), defaultLoadOptions, resolverFromFiles)
import Syntax (Statement)
import ElaborateRequest (Elaborator, Extraction (..), Library (..), LoadKind (..), LoadRequest (..), LoadResponse (..), MirAnswer (..), Request (..), Response (..), acceptedResponse)
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
parseWithEqualityUsing loader source = (\(_, library, body) -> library ++ body) <$> parseWithEqualityPartsUsing loader source

-- The same program with the libraries it was read with kept apart from it (lowerParts)
parseWithEqualityParts :: String -> Either String SourceParts
parseWithEqualityParts = parseWithEqualityPartsUsing sourceLoader

parseWithEqualityPartsUsing :: Loader -> String -> Either String SourceParts
parseWithEqualityPartsUsing loader source = case loader (sourceRequest LoadEquality False False [] source) of
    ParsedSource names library body -> Right (names, library, body)
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
                units names `bindResult` \selected -> linkWithLibraries (stripDeclaredFromUnits (ownNames lowered) selected) [(mainModule, entryProgram)]
    _ -> Error "internal: the loader did not answer with the program's elaboration"
  where
    units [] = Ok []
    units _ | noPrelude' = Error "internal: the loader selected assembly libraries without a catalog"
    units names = libraries `bindResult` \pkg -> flatResultMap (libUnit pkg) names
    catalog = if noPrelude' then Ok [] else mapResult libCatalog libraries

-- An accepted elaboration of the entry module lowered and linked with the compiler libraries it selected
linkSelected :: Response -> Result M.Program String
linkSelected response =
    selection (selectedOf response) `bindResult` \units ->
        stage "Lowering failed: " (lowerAccepted response `bindResult` \lowered -> mapResult ((,) lowered) (finishLowered lowered)) `bindResult` \(lowered, entryProgram) ->
            linkWithLibraries (stripDeclaredFromUnits (ownNames lowered) units) [(mainModule, entryProgram)]
  where
    selection [] = Ok []
    selection selected = libPackage `bindResult` \pkg -> flatResultMap (libUnit pkg) selected

selectedOf :: Response -> [String]
selectedOf response = case response of
    Accepted _ selected _ -> selected
    _ -> []

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

-- A program read with compiler libraries (its parts, SourceParts): its own statements, elaborated with the checked
-- interfaces of the libraries it was read with and those they import, and linked with their units, as a program read
-- from source is. The libraries' statements as read are not given again; the elaborator may select only among those
-- libraries, and libraries that are not the compiler's are refused.
lowerParts :: SourceParts -> Result M.Program String
lowerParts = lowerPartsWith sourceElaborator

lowerPartsWith :: Elaborator -> SourceParts -> Result M.Program String
lowerPartsWith elaborator parts =
    partsRequest parts `bindResult` \(admitted, request) ->
        let response = elaborator request
         in case [n | n <- selectedOf response, n `notElem` admitted] of
                [] -> linkSelected response
                extra -> Error ("internal: the elaborator selected libraries the program was not read with: " ++ unwords extra)

-- The unit the elaborator lowers such a program's own statements to, not finished
elaborateParts :: SourceParts -> Result M.Lowered String
elaborateParts parts = partsRequest parts `bindResult` \(_, request) -> lowerAccepted (sourceElaborator request)

partsRequest :: SourceParts -> Result ([String], Request) String
partsRequest (names, _, body) =
    libPackage `bindResult` \pkg ->
        let catalog = libCatalog pkg
            known = map libraryName catalog
            importsOf n = concat [libraryImports l | l <- catalog, libraryName l == n]
            closure seen [] = seen
            closure seen (n : rest)
                | n `elem` seen = closure seen rest
                | otherwise = closure (seen ++ [n]) (importsOf n ++ rest)
            admitted = closure [] names
         in case [n | n <- names, n `notElem` known] of
                [] -> Ok (admitted, Request mainModule False False NoInterface [] [] [l | l <- catalog, libraryName l `elem` admitted] [body])
                unknown -> Error ("the libraries a program was read with are not the compiler's: " ++ unwords unknown)

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
