module Utils where
    
import Debug.Trace (trace)

data Result a e = Ok a | Error e deriving (Eq)

-- Map elementwise two lists with a function,
-- returning the result list and the second list trimmed to the length of the first
zipMap :: [a] -> [b] -> (a -> b -> c) -> ([c], [b])
zipMap [] _ _ = ([], [])
zipMap (ah : at) (bh : bt) f =
    let (atr, btr) = zipMap at bt f in (f ah bh : atr, bh : btr)
zipMap (_ : _) [] _ = error "Second list must be at least length of first"

flatMap :: (a -> Either b c) -> [a] -> Either [b] c
flatMap _ [] = Left []
flatMap f (ah : at) = case f ah of
    Left b -> case flatMap f at of
        Left bt -> Left (b : bt)
        Right c -> Right c
    Right c -> Right c

flatMaybeMap :: (a -> Maybe b) -> [a] -> Maybe [b]
flatMaybeMap f as = case flatMap
    ( \a -> case f a of
        Just b -> Left b
        Nothing -> Right ()
    )
    as of
    Left bs -> Just bs
    Right _ -> Nothing

flatResultMap :: (a -> Result b e) -> [a] -> Result [b] e
flatResultMap f as = case flatMap (\a -> case f a of Ok b -> Left b; Error e -> Right e) as of
    Left bs -> Ok bs
    Right e -> Error e

unwrapOrThrow :: String -> Maybe a -> a
unwrapOrThrow _ (Just a) = a
unwrapOrThrow err Nothing = error err

-- doTrace print passthrough = trace print passthrough
doTrace print passthrough = passthrough

-- doTrace2 = trace
doTrace2 = doTrace