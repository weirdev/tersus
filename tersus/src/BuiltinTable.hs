-- The builtins as data, `tersus-ast 1 builtins` (AST_DATA.md): what the checker needs of each builtin of
-- BuiltinRegistry, for an elaborator that is not written in Haskell. lib/data/builtins.ast is this table,
-- and TestAstData checks that it still is.
module BuiltinTable (builtinTable, builtinTableText, builtinTableLines) where

import AstData (BuiltinRecord (..), writeBuiltinTableLines)
import BuiltinRegistry (BuiltinEntry (..), builtinRegistry)
import StdLib (builtinFunct)
import Utils

builtinTable :: [BuiltinRecord]
builtinTable =
    [ BuiltinRecord b [(space, n) | (space, n, b') <- entrySurface entry, b' == b] (entrySignature entry b) (builtinFunct b)
    | entry <- builtinRegistry
    , b <- entryInstances entry
    ]

builtinTableText :: Result String String
builtinTableText = mapResult unlines builtinTableLines

builtinTableLines :: Result [String] String
builtinTableLines = writeBuiltinTableLines builtinTable
