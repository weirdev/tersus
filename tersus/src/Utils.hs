module Utils where

import Data.Maybe (mapMaybe)

-- Int is a 64-bit signed integer. Arithmetic that leaves this range stops the program (see LANGUAGE.md, Integers).
intMin, intMax :: Integer
intMin = negate (2 ^ (63 :: Int))
intMax = 2 ^ (63 :: Int) - 1

inIntRange :: Integer -> Bool
inIntRange n = intMin <= n && n <= intMax

data Result a e = Ok a | Error e deriving (Eq, Show)

bindResult :: Result a e -> (a -> Result b e) -> Result b e
bindResult (Ok a) f = f a
bindResult (Error e) _ = Error e

collectMaybes :: (a -> Maybe b) -> [a] -> Maybe [b]
collectMaybes f as =
    let bs = mapMaybe f as
     in if length bs == length as
            then Just bs
            else Nothing

flatResultMap :: (a -> Result b e) -> [a] -> Result [b] e
flatResultMap _ [] = Ok []
flatResultMap f (a : as) =
    case f a of
        Ok b ->
            case flatResultMap f as of
                Ok bs -> Ok (b : bs)
                Error e -> Error e
        Error e -> Error e

mapResult :: (a -> b) -> Result a e -> Result b e
mapResult fn (Ok a) = Ok $ fn a
mapResult _ (Error e) = Error e
