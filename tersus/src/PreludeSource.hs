{-# LANGUAGE TemplateHaskell #-}

module PreludeSource
    ( preludeSource
    , eqSource
    , listsSource
    , boxSource
    , stringSource
    , mapSource
    , setSource
    , emitterSource
    , stdlibSource
    , validationSource
    , validationDriverSource
    , seedSha256
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

-- The text of lib/eq.tersus: the trait Eq, which `=` and `!=` call, and its impls for lists, arrays and Boxes
eqSource :: String
eqSource =
    $( do
        addDependentFile "lib/eq.tersus"
        contents <- runIO (readFile "lib/eq.tersus")
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

-- The text of lib/validation.tersus: the validator written in Tersus, which is
-- what validates every program (see SelfHostedMir.validateByTersus)
validationSource :: String
validationSource =
    $( do
        addDependentFile "lib/validation.tersus"
        contents <- runIO (readFile "lib/validation.tersus")
        lift contents
     )

-- The text of lib/validation_driver.tersus: the main program of the
-- validator compiled to native code, put after validation.tersus for that
-- build only (see ValidatorNative)
validationDriverSource :: String
validationDriverSource =
    $( do
        addDependentFile "lib/validation_driver.tersus"
        contents <- runIO (readFile "lib/validation_driver.tersus")
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
