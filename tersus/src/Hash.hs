module Hash (fingerprint) where

import Data.Bits (xor)
import Data.Char (ord)
import Data.List (foldl')
import Data.Word (Word64)
import Numeric (showHex)

-- A hash (FNV-1a, 64 bits, as 16 hexadecimal digits) of texts: the parts are told apart, so moving text from one to the next changes it. It names things in a cache,
-- and is not made to resist anyone.
fingerprint :: [String] -> String
fingerprint parts = replicate (16 - length digits) '0' ++ digits
  where
    digits = showHex (foldl' step 14695981039346656037 (concatMap (++ "\0") parts)) ""
    step :: Word64 -> Char -> Word64
    step h c = (h `xor` fromIntegral (ord c)) * 1099511628211
