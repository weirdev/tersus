module Compile
    ( parseSource, SourceParts, parseSourceParts, parsedLibraries, probeDecls
    , lowerSourceParts, lowerSourcePartsWith, parseWithEquality, librariesFor, lowerSource
    , lowerStatements, lowerStatementsWith, elaborateStatements, reservedName, reservedHelperName, reservedError, completeSpecEnvs
    ) where

import qualified Mir as M
import MirLower (lowerElaborated, lowerModuleWith)
import Interface (withoutDeclaredNames)
import LibPackage (libModuleOfDisplay, libPackage, libDefinitionContexts, libSelectionFor, stripDeclaredFromUnits)
import Link (linkPrograms, completeSpecEnvs)
import Modules (ModuleId (..))
import qualified ParserSeed
import SourceParse (SourceParts, parsedLibraries, probeDecls, librariesFor, reservedName, reservedHelperName, reservedError, declaredNames, definedFunctionNames)
import qualified SourceParse
import Syntax (Elaborated, Statement)
import ElaborateRequest (Elaborator, Extraction (..), Request (..), acceptedElaboration)
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

lowerSourcePartsWith :: Elaborator -> Bool -> SourceParts -> Result M.Program String
lowerSourcePartsWith elaborator _reserving ([], _library, stmts) =
    stage "Validation failed: " (acceptedElaboration (elaborator (Request (ModuleId "main" Nothing) False False NoInterface [] [] stmts))) `bindResult` \elaborated ->
        stage "Lowering failed: " (lowerModuleWith [] elaborated) `bindResult` \entryProgram ->
        linkPrograms [(ModuleId "main" Nothing, entryProgram)]
lowerSourcePartsWith elaborator _reserving (names, _library, stmts) =
    case libPackage of
        Error err -> Error err
        Ok pkg ->
            let selected = [name | display <- names, Just name <- [libModuleOfDisplay display]]
             in case libSelectionFor pkg selected stmts of
                    Left err -> Error err
                    Right (selectedIfaces, units) ->
                        let own = concatMap declaredNames stmts ++ concatMap definedFunctionNames stmts
                            ifaces = map (withoutDeclaredNames own) selectedIfaces
                         in stage "Validation failed: " (acceptedElaboration (elaborator (Request (ModuleId "main" Nothing) False False NoInterface ifaces (libDefinitionContexts pkg selected) stmts))) `bindResult` \elaborated ->
                                stage "Lowering failed: " (lowerModuleWith ifaces elaborated) `bindResult` \entryProgram ->
                                    linkPrograms (stripDeclaredFromUnits own units ++ [(ModuleId "main" Nothing, entryProgram)])

lowerStatements :: [Statement] -> Result M.Program String
lowerStatements = lowerStatementsWith sourceElaborator

-- A program as given, with no libraries in front of it
lowerStatementsWith :: Elaborator -> [Statement] -> Result M.Program String
lowerStatementsWith elaborator stmts = elaborateWith elaborator stmts `bindResult` lowerElaborated

elaborateStatements :: [Statement] -> Result Elaborated String
elaborateStatements = elaborateWith sourceElaborator

elaborateWith :: Elaborator -> [Statement] -> Result Elaborated String
elaborateWith elaborator stmts = acceptedElaboration (elaborator (Request (ModuleId "main" Nothing) False False NoInterface [] [] stmts))

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
