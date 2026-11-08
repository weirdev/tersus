{-# LANGUAGE TemplateHaskell #-}

module PreludeSource
    ( typesSource
    , preludeSource
    , eqSource
    , cloneSource
    , listsSource
    , boxSource
    , stringSource
    , mapSource
    , setSource
    , libModules
    , nativeStorageModules
    , libPackageFiles
    , mirPackageFiles
    , elaboratePackageFiles
    , parserPackageFiles
    , astReaderPackageFiles
    , toolPackageFiles
    , stdlibSource
    , compilerSourceHash
    , validationPackageFiles
    , seedSha256
    , parserSeedSha256
    ) where

import Data.List (isSuffixOf, sort)
import Hash (fingerprint)
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
import System.Directory (listDirectory)
import ParserUnicodeSource (parserUnicodeSource)

compilerSourceHash :: String
compilerSourceHash =
    $( do
        addDependentFile "tersus.cabal"
        files <- runIO (sort . filter (\file -> any (`isSuffixOf` file) [".hs", ".hsc"]) <$> listDirectory "src")
        inputs <- mapM (\file -> do
            let path = "src/" ++ file
            addDependentFile path
            contents <- runIO (readFile path)
            pure [file, contents]) files
        lift (fingerprint (concat inputs))
     )

libModules :: [(String, String, String)]
libModules =
    [ ("types", "the list and Box types", typesSource)
    , ("clone", "the clone library", cloneSource)
    , ("eq", "the equality library", eqSource)
    , ("prelude", "the prelude", preludeSource)
    , ("string", "the string library", stringSource)
    , ("map", "the map library", mapSource)
    , ("set", "the set library", setSource)
    , ("lists", "the native list helpers", listsSource)
    , ("box", "the native Box helpers", boxSource)
    ]

nativeStorageModules :: [String]
nativeStorageModules = ["lists", "box"]

libPackageFiles :: [(FilePath, String)]
libPackageFiles = ("tersuslib/package.tersus", "") : [("tersuslib/" ++ name ++ "/" ++ name ++ ".tersus", text) | (name, _, text) <- libModules]

-- The text of lib/types.tersus: the structs List and Box, which every program has
typesSource :: String
typesSource =
    $( do
        addDependentFile "lib/types.tersus"
        contents <- runIO (readFile "lib/types.tersus")
        lift contents
     )

-- The text of lib/prelude.tersus, read when this module is compiled
preludeSource :: String
preludeSource =
    $( do
        addDependentFile "lib/prelude.tersus"
        contents <- runIO (readFile "lib/prelude.tersus")
        lift contents
     )

-- The text of lib/eq.tersus: the trait Eq, which `=` and `!=` call, and its impls for lists, arrays and Boxes
eqSource :: String
eqSource =
    $( do
        addDependentFile "lib/eq.tersus"
        contents <- runIO (readFile "lib/eq.tersus")
        lift contents
     )

-- The text of lib/clone.tersus: the trait Clone, which clone calls, and its impls for lists, arrays and Boxes
cloneSource :: String
cloneSource =
    $( do
        addDependentFile "lib/clone.tersus"
        contents <- runIO (readFile "lib/clone.tersus")
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

-- The text of lib/lists.tersus: the list that native code is made of (see MirLists)
listsSource :: String
listsSource =
    $( do
        addDependentFile "lib/lists.tersus"
        contents <- runIO (readFile "lib/lists.tersus")
        lift contents
     )

-- The text of lib/box.tersus: the Box that native code is made of (see MirLists)
boxSource :: String
boxSource =
    $( do
        addDependentFile "lib/box.tersus"
        contents <- runIO (readFile "lib/box.tersus")
        lift contents
     )

-- The text of lib/string.tersus: the struct `String` that a string literal is a value of
stringSource :: String
stringSource =
    $( do
        addDependentFile "lib/string.tersus"
        contents <- runIO (readFile "lib/string.tersus")
        lift contents
     )

-- The text of lib/map.tersus: the HashMap a program has when it mentions one
mapSource :: String
mapSource =
    $( do
        addDependentFile "lib/map.tersus"
        contents <- runIO (readFile "lib/map.tersus")
        lift contents
     )

-- The text of lib/set.tersus: the HashSet a program has when it mentions one
setSource :: String
setSource =
    $( do
        addDependentFile "lib/set.tersus"
        contents <- runIO (readFile "lib/set.tersus")
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
                , "lib/mir/emit/emit.tersus"
                , "lib/mir/emit/types.tersus"
                , "lib/mir/emit/values.tersus"
                , "lib/mir/emit/operations.tersus"
                , "lib/mir/emit/functions.tersus"
                , "lib/mir/emit/helpers.tersus"
                , "lib/mir/mir_reader/mir_reader.tersus"
                , "lib/mir/writer/writer.tersus"
                , "lib/mir/ownership/ownership.tersus"
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
seedSha256 :: String
seedSha256 =
    $( do
        addDependentFile "bootstrap/emitter.sha256"
        contents <- runIO (readFile "bootstrap/emitter.sha256")
        lift (head (words contents))
     )

parserSeedSha256 :: String
parserSeedSha256 =
    $( do
        addDependentFile "bootstrap/parser.sha256"
        contents <- runIO (readFile "bootstrap/parser.sha256")
        lift (head (words contents))
     )

dataPackageFiles :: [(FilePath, String)]
dataPackageFiles =
    $( do
        let paths = ["lib/data/package.tersus", "lib/data/codec/codec.tersus", "lib/data/ast/ast.tersus", "lib/data/reader/reader.tersus", "lib/data/arena/arena.tersus"]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

parserPackageFiles :: [(FilePath, String)]
parserPackageFiles = dataPackageFiles ++ [("lib/parser/unicode.tersus", parserUnicodeSource)] ++
    $( do
        let paths = ["lib/parser/package.tersus", "lib/parser/parser.tersus"]
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

-- The elaborator written in Tersus (REPLACING_HASKELL.md), which only the tests and frontend-diff build and run
elaboratePackageFiles :: [(FilePath, String)]
elaboratePackageFiles = dataPackageFiles ++
    $( do
        let paths = ["lib/elaborate/package.tersus", "lib/elaborate/builtins.tersus", "lib/elaborate/calls.tersus", "lib/elaborate/check.tersus", "lib/elaborate/core.tersus", "lib/elaborate/elaborate.tersus", "lib/elaborate/expr.tersus", "lib/elaborate/exports.tersus", "lib/elaborate/out.tersus", "lib/elaborate/proofs.tersus", "lib/elaborate/records.tersus", "lib/elaborate/refs.tersus", "lib/elaborate/state.tersus", "lib/elaborate/traits.tersus"]
        files <- mapM (\path -> do addDependentFile path; contents <- runIO (readFile path); pure (path, contents)) paths
        lift files
     )

toolPackageFiles :: [(FilePath, String)]
toolPackageFiles = mirPackageFiles ++ parserPackageFiles ++ astReaderPackageFiles
