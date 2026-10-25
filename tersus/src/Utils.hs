module Utils where

import Data.Maybe (mapMaybe)

-- Int is a 64-bit signed integer. Arithmetic that leaves this range stops the program (see LANGUAGE.md, Integers).
intMin, intMax :: Integer
intMin = negate (2 ^ (63 :: Int))
intMax = 2 ^ (63 :: Int) - 1

inIntRange :: Integer -> Bool
inIntRange n = intMin <= n && n <= intMax

-- The bytes of the UTF-8 encoding of a character
utf8Bytes :: Char -> [Int]
utf8Bytes c
    | n < 0x80 = [n]
    | n < 0x800 = [0xC0 + n `div` 64, continuation n]
    | n < 0x10000 = [0xE0 + n `div` 4096, continuation (n `div` 64), continuation n]
    | otherwise = [0xF0 + n `div` 262144, continuation (n `div` 4096), continuation (n `div` 64), continuation n]
  where
    n = fromEnum c
    continuation m = 0x80 + m `mod` 64

-- The characters that bytes (as characters from 0 to 255) are the UTF-8 encoding of, with U+FFFD for bytes that are not
decodeUtf8 :: String -> String
decodeUtf8 [] = []
decodeUtf8 (c : rest)
    | n < 0x80 = c : decodeUtf8 rest
    | n >= 0xC0 && n < 0xE0 = multi 1 (n - 0xC0) 0x80
    | n >= 0xE0 && n < 0xF0 = multi 2 (n - 0xE0) 0x800
    | n >= 0xF0 && n < 0xF5 = multi 3 (n - 0xF0) 0x10000
    | otherwise = '\xFFFD' : decodeUtf8 rest
  where
    n = fromEnum c
    multi count lead least =
        let (continuation, more) = splitAt count rest
            ok = length continuation == count && all (\b -> fromEnum b >= 0x80 && fromEnum b < 0xC0) continuation
            point = foldl (\acc b -> acc * 64 + (fromEnum b - 0x80)) lead continuation
         in if ok && point >= least && point <= 0x10FFFF && not (point >= 0xD800 && point < 0xE000) then toEnum point : decodeUtf8 more else '\xFFFD' : decodeUtf8 rest

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
