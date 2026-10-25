{-# LANGUAGE TemplateHaskell #-}

module PreludeSource
    ( preludeSource
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
