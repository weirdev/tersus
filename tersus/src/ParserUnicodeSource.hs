module ParserUnicodeSource (parserUnicodeSource) where

import Data.Char (chr, isLetter, isUpper, isLower, isAlphaNum)

-- Generate native predicates from the same Unicode categories as the serving oracle.
-- Balanced comparisons allocate no per-character table and follow the compiler's version.
parserUnicodeSource :: String
parserUnicodeSource = predicate "parserUnicodeLetter" isLetter ++ predicate "parserUnicodeUpper" isUpper ++ predicate "parserUnicodeLower" isLower ++ predicate "parserUnicodeAlphaNum" isAlphaNum
  where
    predicate name classify =
        let (body, parts) = split name (ranges classify)
         in concat parts ++ "fn " ++ name ++ "(cp: Int) -> Bool ~ {\n" ++ body ++ "\n};\n"
    -- Subtrees of at most partSize intervals are functions of their own, so
    -- that no function is too large for the validator.
    partSize = 32 :: Int
    split name intervals
        | length intervals <= partSize =
            let part = name ++ "Part" ++ show (fst (head intervals))
             in ("return " ++ part ++ "(cp);", ["fn " ++ part ++ "(cp: Int) -> Bool ~ {\n" ++ branch intervals ++ "\n};\n"])
        | otherwise =
            let (left, right) = splitAt (length intervals `div` 2) intervals
                (leftBody, leftParts) = split name left
                (rightBody, rightParts) = split name right
             in ("if cp < " ++ show (fst (head right)) ++ " {\n" ++ leftBody ++ "\n} else {\n" ++ rightBody ++ "\n};", leftParts ++ rightParts)
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
