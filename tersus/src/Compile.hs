module Compile
    ( lowerSource, lowerSourceNoPrelude, lowerSourceUsing
    , lowerStatements, lowerStatementsWith, elaborateStatements, completeSpecEnvs
    ) where

import qualified Mir as M
import ElaborateRequest (Elaborator, Extraction (..), Request (..))
import ElaboratorTool (Loader, sourceElaborator, sourceLoader)
import LibPackage (LibPackage, libPackage, libraryBoundedNames)
import Link (completeSpecEnvs)
import Lowering (finishProgramWith, lowerAccepted)
import qualified Modules as Mod
import PackageCompile (compileModulesUsing, lowerCompiledPackage)
import PackageData (LoadOptions (..), ModuleId (..), defaultLoadOptions)
import Syntax (Statement)
import Utils

lowerSource :: Bool -> String -> Result M.Program String
lowerSource = lowerSourceNoPrelude False

lowerSourceNoPrelude :: Bool -> Bool -> String -> Result M.Program String
lowerSourceNoPrelude = lowerSourceUsing sourceLoader libPackage

-- A standalone program compiles through the same ordinary package/std loader and linker as every package.
lowerSourceUsing :: Loader -> Result LibPackage String -> Bool -> Bool -> String -> Result M.Program String
lowerSourceUsing loader libraries noPrelude' _ source =
    compileModulesUsing loader libraries (Mod.sourceSnapshot defaultLoadOptions{noPrelude = noPrelude'} source)
        `bindResult` lowerCompiledPackage

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
