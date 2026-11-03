module ParserUnicodeSource (parserUnicodeSource) where

import Data.Char (chr, isLetter, isUpper, isLower, isAlphaNum)

-- Generate native predicates from the same Unicode categories as the serving oracle.
-- Balanced comparisons allocate no per-character table and follow the compiler's version.
parserUnicodeSource :: String
parserUnicodeSource = predicate "parserUnicodeLetter" isLetter ++ predicate "parserUnicodeUpper" isUpper ++ predicate "parserUnicodeLower" isLower ++ predicate "parserUnicodeAlphaNum" isAlphaNum
  where
    predicate name classify = "fn " ++ name ++ "(cp: Int) -> Bool ~ {\n" ++ branch (ranges classify) ++ "\n};\n"
    ranges classify = collect 128
      where
        collect n
            | n > 0x10ffff = []
            | classify (chr n) = let end = lastOf n in (n, end) : collect (end + 1)
            | otherwise = collect (n + 1)
        lastOf n
            | n < 0x10ffff && classify (chr (n + 1)) = lastOf (n + 1)
            | otherwise = n
    branch [] = "return false;"
    branch [(lo, hi)] = "return cp >= " ++ show lo ++ " && cp <= " ++ show hi ++ ";"
    branch intervals =
        let (left, right) = splitAt (length intervals `div` 2) intervals
            boundary = fst (head right)
         in "if cp < " ++ show boundary ++ " {\n" ++ branch left ++ "\n} else {\n" ++ branch right ++ "\n};"
