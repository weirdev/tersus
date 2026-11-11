module Compile
    ( parseSource, SourceParts, parseSourceParts, parsedLibraries, probeDecls
    , lowerSourceParts, lowerSourcePartsWith, parseWithEquality, librariesFor, lowerSource
    , lowerStatements, lowerStatementsWith, elaborateStatements, reservedName, reservedError, completeSpecEnvs
    ) where

import qualified Mir as M
import MirLower (lowerElaborated, lowerModuleWith)
import LibPackage (libCatalog, libPackage, libSelection, stripDeclaredFromUnits, withoutReplacedEq)
import Link (linkPrograms, completeSpecEnvs)
import Modules (ModuleId (..))
import qualified ParserSeed
import SourceParse (SourceParts, parsedLibraries, probeDecls, librariesFor, reservedName, reservedError, declaredNames, definedFunctionNames)
import qualified SourceParse
import Syntax (Elaborated, Statement)
import ElaborateRequest (Elaborator, Extraction (..), Request (..), Response (..), acceptedElaboration)
import ElaboratorTool (sourceElaborator)
import Utils

parseSource :: String -> Result [Statement] String
parseSource source = mapResult (\(_, library, body) -> library ++ body) (parseSourceParts True source)

parseSourceParts :: Bool -> String -> Result SourceParts String
parseSourceParts reserving = SourceParse.parseSourcePartsWith ParserSeed.parseFileWith reserving False

parseWithEquality :: String -> Either String [Statement]
parseWithEquality = SourceParse.parseWithEqualityWith ParserSeed.parseFileWith

lowerSource :: Bool -> String -> Result M.Program String
lowerSource reserving source =
    parseSourceParts reserving source `bindResult` lowerSourceParts reserving

lowerSourceParts :: Bool -> SourceParts -> Result M.Program String
lowerSourceParts = lowerSourcePartsWith sourceElaborator

-- A program with the compiler libraries for the elaborator to select among, unless its parse called for none (with no
-- prelude, or declaring what every library declares); the libraries the elaborator selected are linked
lowerSourcePartsWith :: Elaborator -> Bool -> SourceParts -> Result M.Program String
lowerSourcePartsWith elaborator _reserving (names, _library, stmts) =
    catalog `bindResult` \libraries ->
        case elaborator (Request mainModule False False NoInterface [] [] libraries Nothing [stmts]) of
            Unresolved err -> Error err
            response ->
                stage "Validation failed: " (acceptedElaboration response) `bindResult` \elaborated ->
                    sameSelection (selectedOf response) `bindResult` \selected ->
                    selection selected `bindResult` \(ifaces, units) ->
                        stage "Lowering failed: " (lowerModuleWith (withoutReplacedEq stmts ifaces) elaborated) `bindResult` \entryProgram ->
                            linkPrograms (stripDeclaredFromUnits own units ++ [(mainModule, entryProgram)])
  where
    catalog = if null names then Ok [] else mapResult libCatalog libPackage
    selectedOf response = case response of
        Accepted _ _ selected -> selected
        _ -> []
    sameSelection selected
        | selected == names = Ok selected
        | otherwise = Error ("internal: the elaborator selected the libraries " ++ show selected ++ " for a program parsed with " ++ show names)
    selection [] = Ok ([], [])
    selection selected = mapResult (`libSelection` selected) libPackage
    own = concatMap declaredNames stmts ++ concatMap definedFunctionNames stmts

mainModule :: ModuleId
mainModule = ModuleId "main" Nothing

lowerStatements :: [Statement] -> Result M.Program String
lowerStatements = lowerStatementsWith sourceElaborator

-- A program as given, with no libraries in front of it
lowerStatementsWith :: Elaborator -> [Statement] -> Result M.Program String
lowerStatementsWith elaborator stmts = elaborateWith elaborator stmts `bindResult` lowerElaborated

elaborateStatements :: [Statement] -> Result Elaborated String
elaborateStatements = elaborateWith sourceElaborator

elaborateWith :: Elaborator -> [Statement] -> Result Elaborated String
elaborateWith elaborator stmts = acceptedElaboration (elaborator (Request mainModule False False NoInterface [] [] [] Nothing [stmts]))

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
