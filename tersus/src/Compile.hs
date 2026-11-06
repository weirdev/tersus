module Compile
    ( parseSource, SourceParts, parseSourceParts, parsedLibraries, probeDecls
    , lowerSourceParts, parseWithEquality, librariesFor, lowerSource
    , lowerStatements, reservedName, reservedHelperName, reservedError, completeSpecEnvs
    ) where

import qualified Data.Map as Map
import qualified Mir as M
import MirLower (lowerElaborated, lowerModuleWith)
import Interface (mergeInterfacesImportEnv, withoutDeclaredNames)
import LibPackage (libModuleOfDisplay, libPackage, libSelectionFor, stripDeclaredFromUnits)
import Link (linkPrograms)
import Modules (ModuleId (..))
import qualified ParserSeed
import SourceParse (SourceParts, parsedLibraries, probeDecls, librariesFor, reservedName, reservedHelperName, reservedError, declaredNames, definedFunctionNames)
import qualified SourceParse
import Syntax (Statement)
import TypeCheck (elaborate, elaborateWith)
import Utils

parseSource :: String -> Result [Statement] String
parseSource source = mapResult (\(_, library, body) -> library ++ body) (parseSourceParts True source)

parseSourceParts :: Bool -> String -> Result SourceParts String
parseSourceParts = SourceParse.parseSourcePartsWith ParserSeed.parseFileWith

parseWithEquality :: String -> Either String [Statement]
parseWithEquality = SourceParse.parseWithEqualityWith ParserSeed.parseFileWith

lowerSource :: Bool -> String -> Result M.Program String
lowerSource reserving source =
    parseSourceParts reserving source `bindResult` lowerSourceParts reserving

lowerSourceParts :: Bool -> SourceParts -> Result M.Program String
lowerSourceParts _reserving (names, _library, stmts) =
    case libPackage of
        Error err -> Error err
        Ok pkg ->
            let selected = [name | display <- names, Just name <- [libModuleOfDisplay display]]
             in case libSelectionFor pkg selected stmts of
                    Left err -> Error err
                    Right (selectedIfaces, units) ->
                        let own = concatMap declaredNames stmts ++ concatMap definedFunctionNames stmts
                            ifaces = map (withoutDeclaredNames own) selectedIfaces
                            importEnv = mergeInterfacesImportEnv ifaces
                         in stage "Validation failed: " (mapResult fst (elaborateWith importEnv stmts)) `bindResult` \elaborated ->
                                stage "Lowering failed: " (lowerModuleWith importEnv ifaces elaborated) `bindResult` \entryProgram ->
                                    mapResult completeSpecEnvs (linkPrograms (stripDeclaredFromUnits own units ++ [(ModuleId "main" Nothing, entryProgram)]))

-- Linked functions need the complete program's ghost environment, not only the unit's.
completeSpecEnvs :: M.Program -> M.Program
completeSpecEnvs program = program{M.progFunctions = Map.map completeFunction (M.progFunctions program), M.progMain = completeGhosts (M.progMain program)}
  where
    functionEnv = Map.fromList [(name, M.Const (M.CFn name)) | name <- Map.keys (M.progFunctions program)]
    completeFunction fn = completeGhosts fn{M.fnSpec = completeSpec (M.fnSpec fn)}
    completeGhosts fn = fn{M.fnBlocks = Map.map completeBlock (M.fnBlocks fn)}
    completeBlock (M.BasicBlock statements term) = M.BasicBlock (map completeStatement statements) term
    completeStatement (M.Ghost env ghost) = M.Ghost (completeEnv env) ghost
    completeStatement other = other
    completeSpec spec = spec{M.specEnv = completeEnv (M.specEnv spec), M.specLoops = Map.map (\loop -> loop{M.loopEnv = completeEnv (M.loopEnv loop)}) (M.specLoops spec)}
    completeEnv env = Map.union env functionEnv

lowerStatements :: [Statement] -> Result M.Program String
lowerStatements stmts = elaborate stmts `bindResult` lowerElaborated

stage :: String -> Result a String -> Result a String
stage _ (Ok a) = Ok a
stage prefix (Error e) = Error (prefix ++ e)
