{-# LANGUAGE TemplateHaskell #-}

module PreludeSource
    ( preludeSource
    , listsSource
    , stringSource
    , emitterSource
    , seedSource
    , seedFingerprint
    ) where

import Hash (fingerprint)
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

-- The text of bootstrap/emitter.ll: the LLVM IR of an emitter written in Tersus (an old one: see Bootstrap), which is what the emitter is first built from
seedSource :: String
seedSource =
    $( do
        addDependentFile "bootstrap/emitter.ll"
        contents <- runIO (readFile "bootstrap/emitter.ll")
        lift contents
     )

-- A hash of the seed, made when this module is compiled, so that it is not made of 9 million characters each time the compiler runs
seedFingerprint :: String
seedFingerprint =
    $( do
        addDependentFile "bootstrap/emitter.ll"
        contents <- runIO (readFile "bootstrap/emitter.ll")
        lift (fingerprint [contents])
     )
