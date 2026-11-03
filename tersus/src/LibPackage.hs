module LibPackage
    ( LibPackage (..)
    , libPackage
    , libModuleNames
    , libModuleId
    , libModuleOfDisplay
    , libSelection
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import qualified Data.Map.Strict as Map
import System.IO.Unsafe (unsafePerformIO)

import Interface (ModuleInterface, extractLibInterface, mergeInterfacesImportEnv, predeclareOwnEnv)
import qualified Mir as M
import MirLower (lowerModuleWith)
import Modules (LoadResult (..), LoadedFile (..), LoadedModule (..), LoadedPackage (..), ModuleId (..), loadFromEntry, renderModuleId, resolverFromFiles)
import Parse (ParsedFile (..))
import PreludeSource (cloneSource, eqSource, mapSource, preludeSource, setSource, stringSource)
import TypeCheck (Elaborated (..), elaborateWith)
import Utils (Result (..))

-- The six libraries of Compile.librariesFor as a synthetic package: one
-- module per lib file, built in memory from the PreludeSource texts (the
-- import lines below exist only in these in-memory copies, so the embedded
-- texts, and with them emitterHash, are unchanged). A library module's
-- declarations keep their bare names, as the entry module's do: the
-- checker, the parser, MIR and the emitter all match those names as
-- strings. The package is compiled once per process; until the single-file
-- path consumed it, nothing here changed what any program means.

libModuleNames :: [String]
libModuleNames = ["eq", "clone", "prelude", "string", "map", "set"]

-- The display names Compile.librariesFor selects by.
libModuleOfDisplay :: String -> Maybe String
libModuleOfDisplay display = lookup display [(shown, name) | (name, shown, _, _) <- libModules]

libDependencies :: String -> [String]
libDependencies name = case [deps | (candidate, _, _, deps) <- libModules, candidate == name] of
    deps : _ -> deps
    [] -> []

libModules :: [(String, String, String, [String])]
libModules =
    [ ("eq", "the equality library", eqSource, [])
    , ("clone", "the clone library", cloneSource, [])
    , ("prelude", "the prelude", preludeSource, ["clone"])
    , ("string", "the string library", stringSource, ["prelude", "eq", "clone"])
    , ("map", "the map library", mapSource, ["prelude", "eq", "clone"])
    , ("set", "the set library", setSource, ["map", "prelude", "eq", "clone"])
    ]

libModuleId :: String -> ModuleId
libModuleId name = ModuleId "tersuslib" (Just name)

-- The imports share the first line of the text (a comment in every lib
-- file), so the positions of the library's own statements, which the
-- lowering names temporaries by, are the ones of the text itself.
libSourceWithImports :: (String, String, String, [String]) -> String
libSourceWithImports (_, _, text, deps) = concat ["import tersuslib::" ++ dep ++ "; " | dep <- deps] ++ text

libPackageFiles :: [(FilePath, String)]
libPackageFiles =
    ("tersuslib/package.tersus", "")
        : ("tersuslib/tersuslib.tersus", concat ["import tersuslib::" ++ name ++ ";\n" | name <- libModuleNames])
        : [("tersuslib/" ++ name ++ "/" ++ name ++ ".tersus", libSourceWithImports modu) | modu@(name, _, _, _) <- libModules]

data LibPackage = LibPackage
    { libInterfaces :: Map.Map String ModuleInterface
    , libPrograms :: Map.Map String M.Program
    , libOrder :: [String]
    }
    deriving (Show)

compileLibPackage :: Result LibPackage String
compileLibPackage = case loadFromEntry (resolverFromFiles libPackageFiles) "tersuslib/tersuslib.tersus" of
    Left err -> Error ("the lib package does not load: " ++ err)
    Right (StandaloneResult _ _) -> Error "the lib package does not load: it loaded as a standalone program"
    Right (PackageResult pkg) -> go (packageModules pkg) Map.empty Map.empty []
  where
    go [] ifaces programs done = Ok (LibPackage ifaces programs (reverse done))
    go (modu : rest) ifaces programs done = case moduleName (loadedModuleId modu) of
        Just name | name `elem` libModuleNames -> case compileOne ifaces modu of
            Error err -> Error err
            Ok (iface, program) -> go rest (Map.insert name iface ifaces) (Map.insert name program programs) (name : done)
        _ -> go rest ifaces programs done
    compileOne ifaces modu =
        let moduId = loadedModuleId modu
            depIfaces = [ifaces Map.! depName | dep <- loadedDependencies modu, Just depName <- [moduleName dep], Map.member depName ifaces]
            importEnv = mergeInterfacesImportEnv depIfaces
            env = predeclareOwnEnv importEnv
            statements = concatMap (fileBody . loadedParsed) (loadedModuleFiles modu)
         in case elaborateWith env statements of
                Error err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
                Ok (elaborated@(Elaborated elaboratedStatements _), state) -> case extractLibInterface moduId statements elaboratedStatements state of
                    Error err -> Error err
                    Ok iface -> case lowerModuleWith importEnv depIfaces elaborated of
                        Error err -> Error ("in lib module " ++ renderModuleId moduId ++ ": " ++ err)
                        Ok program -> Ok (iface, program)

{-# NOINLINE libPackageCache #-}
libPackageCache :: MVar (Maybe (Result LibPackage String))
libPackageCache = unsafePerformIO (newMVar Nothing)

-- The lib package, compiled on first use and kept for the process.
libPackage :: Result LibPackage String
libPackage = unsafePerformIO $ modifyMVar libPackageCache $ \cached -> case cached of
    Just result -> pure (cached, result)
    Nothing ->
        let result = compileLibPackage
            forced = case result of
                Ok pkg -> Map.size (libInterfaces pkg) `seq` result
                Error _ -> result
         in pure (Just forced, forced)

-- The interfaces and lowered units of the named library modules, closed
-- over their dependencies. The units are in the order librariesFor puts
-- the libraries in front of a program, as the linked program's ghost
-- statements follow that order.
libSelection :: LibPackage -> [String] -> ([ModuleInterface], [(ModuleId, M.Program)])
libSelection pkg names =
    let wanted = closure names
        ordered = [name | name <- ["clone", "eq", "prelude", "string", "map", "set"], name `elem` wanted]
     in ( [libInterfaces pkg Map.! name | name <- ordered]
        , [(libModuleId name, libPrograms pkg Map.! name) | name <- ordered]
        )
  where
    closure pending = go pending []
    go [] done = done
    go (name : rest) done
        | name `elem` done = go rest done
        | otherwise = go (libDependencies name ++ rest) (done ++ [name])
