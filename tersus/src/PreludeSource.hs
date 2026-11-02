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
    , emitterSource
    , mirVerifySource
    , mirEraseSource
    , stdlibSource
    , seedSha256
    ) where

import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

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

-- The text of examples/emit.tersus: the lowering to LLVM IR written in Tersus (see Bootstrap)
emitterSource :: String
emitterSource =
    $( do
        addDependentFile "examples/emit.tersus"
        contents <- runIO (readFile "examples/emit.tersus")
        lift contents
     )

-- The SHA-256 pinned in bootstrap/emitter.sha256: the seed IR itself is a GitHub release asset (see Bootstrap), so only this digest is kept in the repository
seedSha256 :: String
seedSha256 =
    $( do
        addDependentFile "bootstrap/emitter.sha256"
        contents <- runIO (readFile "bootstrap/emitter.sha256")
        lift (head (words contents))
     )

-- The text of examples/mir_verify.tersus: the check of the MIR written in Tersus (see MirHousekeeping)
mirVerifySource :: String
mirVerifySource =
    $( do
        addDependentFile "examples/mir_verify.tersus"
        contents <- runIO (readFile "examples/mir_verify.tersus")
        lift contents
     )

-- The text of examples/mir_erase.tersus: the erasure of the ghosts of a program, written in Tersus (see MirHousekeeping)
mirEraseSource :: String
mirEraseSource =
    $( do
        addDependentFile "examples/mir_erase.tersus"
        contents <- runIO (readFile "examples/mir_erase.tersus")
        lift contents
     )
