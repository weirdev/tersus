module Utils where

import Data.Maybe (mapMaybe)

data Result a e = Ok a | Error e deriving (Eq, Show)

-- Map elementwise two lists with a function,
-- returning the result list and the second list trimmed to the length of the first
zipMap :: [a] -> [b] -> (a -> b -> c) -> ([c], [b])
zipMap [] _ _ = ([], [])
zipMap (ah : at) (bh : bt) f =
    let (atr, btr) = zipMap at bt f in (f ah bh : atr, bh : btr)
zipMap (_ : _) [] _ = error "Second list must be at least length of first"

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

unwrapOrThrow :: String -> Maybe a -> a
unwrapOrThrow _ (Just a) = a
unwrapOrThrow err Nothing = error err

-- doTrace print passthrough = trace print passthrough
doTrace :: a -> b -> b
doTrace _ passthrough = passthrough

-- doTrace2 = trace
doTrace2 :: a -> b -> b
doTrace2 = doTrace

-- doTrace3 = trace
doTrace3 :: a -> b -> b
doTrace3 = doTrace2

-- Flip this to `trace` locally when debugging.
doTrace4 :: a -> b -> b
doTrace4 = doTrace3

doTraceStatements :: a -> b -> b
doTraceStatements = doTrace
