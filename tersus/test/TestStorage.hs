{-# LANGUAGE PatternSynonyms #-}

-- The std package's list and Box, as the compiler's programs name them, for tests that write MIR types by hand
module TestStorage
    ( pattern TList
    , pattern TBox
    , stdStorage
    , stdProtocols
    ) where

import qualified Data.Map.Strict as Map

import Types (Arg (..), Name, Storage (..), Type (..))

pattern TList :: Type -> Type
pattern TList t = TNamed "std$core$types$List" [ArgType t]

pattern TBox :: Type -> Type
pattern TBox t = TNamed "std$core$types$Box" [ArgType t]

stdStorage :: Storage
stdStorage = Storage "std$core$types$List" "std$core$types$Box"

stdProtocols :: Map.Map Name Name
stdProtocols = Map.fromList [("List", storageList stdStorage), ("Box", storageBox stdStorage)]
