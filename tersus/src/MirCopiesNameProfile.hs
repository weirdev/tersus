module MirCopiesNameProfile (nameProfilePrefix) where

import Data.Char (chr, digitToInt, isAlphaNum, isHexDigit, isLower, isUpper, ord)
import qualified Data.IntSet as IntSet
import Data.List (foldl')

import Utils (decodeUtf8)

nameProfilePrefix :: [String] -> String
nameProfilePrefix payloads = case classRows points of
    [] -> ""
    rows -> unlines (("name-classes " ++ show (length rows)) : rows)
  where
    points = IntSet.toAscList (foldl' collectPoints IntSet.empty payloads)
    classRows [] = []
    classRows (lo : rest) = unwords [show lo, show hi, show mask] : classRows after
      where
        mask = classMask lo
        (hi, after) = extend lo rest
        extend prev (n : ns) | n == prev + 1 && classMask n == mask = extend n ns
        extend prev ns = (prev, ns)

classMask :: Int -> Int
classMask point = fromEnum (isUpper c) + 2 * fromEnum (isLower c) + 4 * fromEnum (isAlphaNum c)
  where
    c = chr point

-- MIR3 and its AST arena share quote: even a literal backslash is escaped, and
-- each non-ASCII UTF-8 sequence is contiguous, so no record parsing is needed.
collectPoints :: IntSet.IntSet -> String -> IntSet.IntSet
collectPoints points = go points
  where
    go acc text = case dropWhile (/= '\\') text of
        [] -> acc
        escaped@(_ : rest) -> case highBytes escaped of
            ([], _) -> go acc rest
            (bytes, after) ->
                let next = foldl' (\seen c -> IntSet.insert (ord c) seen) acc (decodeUtf8 bytes)
                 in next `seq` go next after

highBytes :: String -> (String, String)
highBytes ('\\' : 'x' : h : l : after)
    | isHexDigit h && isHexDigit l && high >= 8 =
        let (bytes, rest) = highBytes after
         in (chr (16 * high + digitToInt l) : bytes, rest)
  where
    high = digitToInt h
highBytes text = ([], text)
