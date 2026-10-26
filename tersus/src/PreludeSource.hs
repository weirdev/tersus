{-# LANGUAGE TemplateHaskell #-}

module PreludeSource
    ( preludeSource
    , listsSource
    , stringSource
    , emitterSource
    ) where

import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

-- The text of lib/prelude.tersus, read when this module is compiled
preludeSource :: String
preludeSource =
    $( do
        addDependentFile "lib/prelude.tersus"
        contents <- runIO (readFile "lib/prelude.tersus")
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

-- The text of lib/string.tersus: the struct `String` that a string literal is a value of
stringSource :: String
stringSource =
    $( do
        addDependentFile "lib/string.tersus"
        contents <- runIO (readFile "lib/string.tersus")
        lift contents
     )

-- The text of examples/emit.tersus: the lowering to LLVM IR written in Tersus (see Bootstrap)
emitterSource :: String
emitterSource =
    $( do
        addDependentFile "examples/emit.tersus"
        contents <- runIO (readFile "examples/emit.tersus")
        lift contents
     )
