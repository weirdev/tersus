{-# LANGUAGE TemplateHaskell #-}

module PreludeSource
    ( ownershipSource
    , typesSource
    , preludeSource
    , eqSource
    , cloneSource
    , listsSource
    , boxSource
    , stringSource
    , mapSource
    , setSource
    , threadSource
    , libModules
    , nativeStorageModules
    , nativeHelperName
    , stdName
    , libModuleOf
    , libPackageFiles
    , stdPackageSource
    , mirPackageFiles
    , elaboratePackageFiles
    , parserPackageFiles
    , parserUnicodeSource
    , astReaderPackageFiles
    , toolPackageFiles
    , stdlibSource
    , compilerSourceHash
    , compilerSourceFiles
    , emitterSourceFiles
    , emitterSeedConstruction
    , emitterConstructionOf
    , validationPackageFiles
    , seedSha256
    , parserSeedSha256
    , frontendSeedSha256
    , frontendSeedSources
    ) where

import Data.List (isSuffixOf, sort)
import Hash (fingerprint)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
import System.Directory (listDirectory)
import System.FilePath (takeFileName)

compilerSourceHash :: String
compilerSourceHash = fingerprint (concatMap (\(path, contents) -> [takeFileName path, contents]) compilerSourceFiles)

compilerSourceFiles :: [(FilePath, String)]
compilerSourceFiles =
    $( do
        addDependentFile "tersus.cabal"
        files <- runIO (sort . filter (\file -> any (`isSuffixOf` file) [".hs", ".hsc", ".hs-boot"]) <$> listDirectory "src")
        inputs <- mapM (\file -> do
            let path = "src/" ++ file
            addDependentFile path
            contents <- runIO (readFile path)
            pure (path, contents)) files
        lift inputs
     )

emitterSourceFiles :: [(FilePath, String)]
emitterSourceFiles = compilerSourceFiles ++ toolPackageFiles ++ validationPackageFiles ++ elaboratePackageFiles
    ++ [("lib/" ++ path, text) | (path, text) <- libPackageFiles]
    ++ [("lib/stdlib.tersus", stdlibSource)]
    ++ $(do
        let paths = ["dev/emitter-seed/Main.hs", "package.yaml", "tersus.cabal"]
        files <- mapM (\path -> do addDependentFile path; body <- runIO (readFile path); pure (path, body)) paths
        lift files)

libModules :: [(String, String, String)]
libModules =
    [ ("core/ownership", "the ownership protocols", ownershipSource)
    , ("core/types", "the list and Box types", typesSource)
    , ("core/clone", "the clone library", cloneSource)
    , ("eq", "the equality library", eqSource)
    , ("prelude", "the prelude", preludeSource)
    , ("string", "the string library", stringSource)
    , ("map", "the map library", mapSource)
    , ("set", "the set library", setSource)
    , ("thread", "the thread library", threadSource)
    , ("lists", "the native list helpers", listsSource)
    , ("box", "the native Box helpers", boxSource)
    ]

nativeStorageModules :: [String]
nativeStorageModules = ["lists", "box"]

-- The canonical name of a function of the native storage helpers that native list and Box operations call (`boxNew` and
-- `boxUnbox` are of box, the others of lists), as the std package names a declaration of a module's one file
nativeHelperName :: String -> String
nativeHelperName local = stdName (if take 3 local == "box" then "box" else "lists") local

-- The canonical name of a declaration of a std library (`stdName "map" "HashMap"`, `stdName "core/types" "List"`), as the std
-- package names a declaration of a module's file
stdName :: String -> String -> String
stdName lib local = case break (== '/') lib of
    (modu, '/' : file) -> "std$" ++ modu ++ "$" ++ file ++ "$" ++ local
    _ -> "std$" ++ lib ++ "$" ++ lib ++ "$" ++ local

libPackageFiles :: [(FilePath, String)]
libPackageFiles = ("std/package.tersus", stdPackageSource) : [("std/" ++ libFilePath name ++ ".tersus", text) | (name, _, text) <- libModules]
  where
    libFilePath name = case break (== '/') name of
        (modu, '/' : file) -> modu ++ "/" ++ file
        _ -> name ++ "/" ++ name

-- The module of the std package a library source is a file of (`core/types` is a file of `core`)
libModuleOf :: String -> String
libModuleOf = takeWhile (/= '/')

stdPackageSource :: String
stdPackageSource =
    $( do
        addDependentFile "lib/std/package.tersus"
        contents <- runIO (readFile "lib/std/package.tersus")
        lift contents
     )

-- The text of lib/std/core/ownership.tersus: the traits Clone, Copy, Drop and Deref
ownershipSource :: String
ownershipSource =
    $( do
        addDependentFile "lib/std/core/ownership.tersus"
        contents <- runIO (readFile "lib/std/core/ownership.tersus")
        lift contents
     )

-- The text of lib/std/core/types.tersus: the structs List and Box, which every program has
typesSource :: String
typesSource =
    $( do
        addDependentFile "lib/std/core/types.tersus"
        contents <- runIO (readFile "lib/std/core/types.tersus")
        lift contents
     )

-- The text of lib/std/prelude/prelude.tersus, read when this module is compiled
preludeSource :: String
preludeSource =
    $( do
        addDependentFile "lib/std/prelude/prelude.tersus"
        contents <- runIO (readFile "lib/std/prelude/prelude.tersus")
        lift contents
     )

-- The text of lib/std/eq/eq.tersus: the trait Eq, which `=` and `!=` call, and its impls for lists, arrays and Boxes
eqSource :: String
eqSource =
    $( do
        addDependentFile "lib/std/eq/eq.tersus"
        contents <- runIO (readFile "lib/std/eq/eq.tersus")
        lift contents
     )

-- The text of lib/std/core/clone.tersus: the trait Clone, which clone calls, and its impls for lists, arrays and Boxes
cloneSource :: String
cloneSource =
    $( do
        addDependentFile "lib/std/core/clone.tersus"
        contents <- runIO (readFile "lib/std/core/clone.tersus")
        lift contents
     )

-- The text of lib/stdlib.tersus: the standard library written in Tersus (see StdLibDefs)
stdlibSource :: String
stdlibSource =
    $( do
        addDependentFile "lib/stdlib.tersus"
        contents <- runIO (readFile "lib/stdlib.tersus")
        lift contents
     )

-- The text of lib/std/lists/lists.tersus: the list that native code is made of (see MirLists)
listsSource :: String
listsSource =
    $( do
        addDependentFile "lib/std/lists/lists.tersus"
        contents <- runIO (readFile "lib/std/lists/lists.tersus")
        lift contents
     )

-- The text of lib/std/box/box.tersus: the Box that native code is made of (see MirLists)
boxSource :: String
boxSource =
    $( do
        addDependentFile "lib/std/box/box.tersus"
        contents <- runIO (readFile "lib/std/box/box.tersus")
        lift contents
     )

-- The text of lib/std/string/string.tersus: the struct `String` that a string literal is a value of
stringSource :: String
stringSource =
    $( do
        addDependentFile "lib/std/string/string.tersus"
        contents <- runIO (readFile "lib/std/string/string.tersus")
        lift contents
     )

-- The text of lib/std/map/map.tersus: the HashMap a program has when it mentions one
mapSource :: String
mapSource =
    $( do
        addDependentFile "lib/std/map/map.tersus"
        contents <- runIO (readFile "lib/std/map/map.tersus")
        lift contents
     )

-- The text of lib/std/set/set.tersus: the HashSet a program has when it mentions one
setSource :: String
setSource =
    $( do
        addDependentFile "lib/std/set/set.tersus"
        contents <- runIO (readFile "lib/std/set/set.tersus")
        lift contents
     )

-- The text of lib/std/thread/thread.tersus: the Thread a program has when it mentions one
threadSource :: String
threadSource =
    $( do
        addDependentFile "lib/std/thread/thread.tersus"
        contents <- runIO (readFile "lib/std/thread/thread.tersus")
        lift contents
     )

-- The files of the mir package and its shared data dependencies, embedded
-- so the host uses the same module resolver and compiler as filesystem packages.
mirPackageFiles :: [(FilePath, String)]
mirPackageFiles = dataPackageFiles ++
    $( do
        let paths =
                [ "lib/mir/package.tersus"
                , "lib/mir/reader/reader.tersus"
                , "lib/mir/support/support.tersus"
                , "lib/mir/full/full.tersus"
                , "lib/mir/full/tokens.tersus"
                , "lib/mir/full/records.tersus"
                , "lib/mir/full/read.tersus"
                , "lib/mir/full/write.tersus"
                , "lib/mir/full/equality.tersus"
                , "lib/mir/full/environments.tersus"
                , "lib/mir/copies/calls.tersus"
                , "lib/mir/copies/finish.tersus"
                , "lib/mir/copies/finishPack.tersus"
                , "lib/mir/copies/finishPackProofs.tersus"
                , "lib/mir/copies/finishProofs.tersus"
                , "lib/mir/copies/frame.tersus"
                , "lib/mir/copies/keys.tersus"
                , "lib/mir/copies/proofs.tersus"
                , "lib/mir/copies/transform.tersus"
                , "lib/mir/copies/types.tersus"
                , "lib/mir/copies/worklist.tersus"
                , "lib/mir/pack/body.tersus"
                , "lib/mir/pack/expand.tersus"
                , "lib/mir/pack/numbers.tersus"
                , "lib/mir/pack/proofs.tersus"
                , "lib/mir/instances/complete.tersus"
                , "lib/mir/instances/names.tersus"
                , "lib/mir/link/fused.tersus"
                , "lib/mir/link/profile.tersus"
                , "lib/mir/link/link.tersus"
                , "lib/mir/link/merge.tersus"
                , "lib/mir/reachability/prune.tersus"
                , "lib/mir/emit/emit.tersus"
                , "lib/mir/emit/types.tersus"
                , "lib/mir/emit/values.tersus"
                , "lib/mir/emit/operations.tersus"
                , "lib/mir/emit/functions.tersus"
                , "lib/mir/emit/helpers.tersus"
                , "lib/mir/mir_reader/mir_reader.tersus"
                , "lib/mir/writer/writer.tersus"
                , "lib/mir/mono/mono.tersus"
                , "lib/mir/mono/tokens.tersus"
                , "lib/mir/mono/functions.tersus"
                , "lib/mir/mono/types.tersus"
                , "lib/mir/validationmono/mono.tersus"
                , "lib/mir/validationmono/request.tersus"
                , "lib/mir/validationmono/types.tersus"
                , "lib/mir/ownership/ownership.tersus"
                , "lib/mir/ownership/mono.tersus"
                , "lib/mir/ownership/common.tersus"
                , "lib/mir/ownership/analysis.tersus"
                , "lib/mir/ownership/rewrite.tersus"
                , "lib/mir/ownership/refwrites.tersus"
                , "lib/mir/ownership/drops.tersus"
                , "lib/mir/mir_verify/mir_verify.tersus"
                , "lib/mir/mir_erase/mir_erase.tersus"
                ]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

validationPackageFiles :: [(FilePath, String)]
validationPackageFiles =
    $( do
        let paths = ["lib/validation/package.tersus", "lib/validation/driver.tersus",
                "lib/validation/context.tersus", "lib/validation/differences.tersus",
                "lib/validation/evaluation.tersus", "lib/validation/execution.tersus",
                "lib/validation/flow.tersus", "lib/validation/joins.tersus",
                "lib/validation/linear.tersus", "lib/validation/loopInference.tersus",
                "lib/validation/model.tersus", "lib/validation/relations.tersus", "lib/validation/saturation.tersus",
                "lib/validation/sequenceFacts.tersus", "lib/validation/state.tersus",
                "lib/validation/validation.tersus"]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

-- The SHA-256 pinned in bootstrap/emitter.sha256: the seed IR itself is a GitHub release asset (see Bootstrap), so only this digest is kept in the repository
emitterSeedPin :: String
emitterSeedPin = $(do
    addDependentFile "bootstrap/emitter.sha256"
    contents <- runIO (readFile "bootstrap/emitter.sha256")
    lift contents)

seedSha256 :: String
seedSha256 = head (words emitterSeedPin)

emitterSeedConstruction :: String
emitterSeedConstruction = emitterConstructionOf emitterSeedPin

emitterConstructionOf :: String -> String
emitterConstructionOf record = case words record of
    [_, construction] -> construction
    _ -> ""

parserSeedSha256 :: String
parserSeedSha256 =
    $( do
        addDependentFile "bootstrap/parser.sha256"
        contents <- runIO (readFile "bootstrap/parser.sha256")
        lift (head (words contents))
     )

-- (the second word of bootstrap/frontend.sha256 is the fingerprint of what the seed elaborates as: ElaboratorTool)
frontendSeedSources :: String
frontendSeedSources =
    $( do
        addDependentFile "bootstrap/frontend.sha256"
        contents <- runIO (readFile "bootstrap/frontend.sha256")
        lift (concat (take 1 (drop 1 (words contents))))
     )

frontendSeedSha256 :: String
frontendSeedSha256 =
    $( do
        addDependentFile "bootstrap/frontend.sha256"
        contents <- runIO (readFile "bootstrap/frontend.sha256")
        lift (head (words contents))
     )

dataPackageFiles :: [(FilePath, String)]
dataPackageFiles =
    $( do
        let paths = ["lib/data/package.tersus", "lib/data/unicode/unicode.tersus", "lib/data/codec/codec.tersus", "lib/data/ast/ast.tersus", "lib/data/reader/reader.tersus", "lib/data/arena/arena.tersus"]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

-- The parser's classifiers of code points from 128 up, pinned to one Unicode version (dev/parser-unicode/generate.py)
parserUnicodeSource :: String
parserUnicodeSource =
    $( do
        let path = "lib/data/unicode/unicode.tersus"
        addDependentFile path
        contents <- runIO (readFile path)
        lift contents
     )

parserPackageFiles :: [(FilePath, String)]
parserPackageFiles = dataPackageFiles ++
    $( do
        let paths = ["lib/parser/package.tersus", "lib/parser/parser.tersus", "lib/parser/syntax/syntax.tersus"]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

astReaderPackageFiles :: [(FilePath, String)]
astReaderPackageFiles = dataPackageFiles ++
    $( do
        let paths = ["lib/ast_reader/package.tersus", "lib/ast_reader/ast_reader.tersus"]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

-- The elaborator written in Tersus (REPLACING_HASKELL.md), the compiler's type checker
elaboratePackageFiles :: [(FilePath, String)]
elaboratePackageFiles = dataPackageFiles ++
    $( do
        let paths = ["lib/parser/package.tersus", "lib/parser/syntax/syntax.tersus", "lib/elaborate/package.tersus", "lib/elaborate/builtins.tersus", "lib/elaborate/calls.tersus", "lib/elaborate/check.tersus", "lib/elaborate/core.tersus", "lib/elaborate/decls.tersus", "lib/elaborate/elaborate.tersus", "lib/elaborate/expr.tersus", "lib/elaborate/exports.tersus", "lib/elaborate/libraries.tersus", "lib/elaborate/load.tersus", "lib/elaborate/lower.tersus", "lib/elaborate/lowerbuild.tersus", "lib/elaborate/lowerexpr.tersus", "lib/elaborate/loweriface.tersus", "lib/elaborate/lowerout.tersus", "lib/elaborate/lowerplace.tersus", "lib/elaborate/lowerstate.tersus", "lib/elaborate/out.tersus", "lib/elaborate/proofs.tersus", "lib/elaborate/records.tersus", "lib/elaborate/refs.tersus", "lib/elaborate/resolve.tersus", "lib/elaborate/rewrite.tersus", "lib/elaborate/snapshot.tersus", "lib/elaborate/state.tersus", "lib/elaborate/traits.tersus", "lib/elaborate/units.tersus", "lib/elaborate/wire.tersus"]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

toolPackageFiles :: [(FilePath, String)]
toolPackageFiles = mirPackageFiles ++ parserPackageFiles ++ astReaderPackageFiles
