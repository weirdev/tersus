module DataCodec
    ( Token (..), P (..), quote, tokenize, strictTokenize, strictTokenizeBytes, parseLine
    , word, name, expect, integer, int, failP, typeTokens, sizeTokens, argTokens
    , typeP, sizeP, argP, decimal
    ) where

import Control.Monad (replicateM)
import qualified Data.ByteString.Char8 as B
import Data.List (foldl')
import Types
import Utils

typeTokens :: Type -> [String]
typeTokens ty = case ty of
    TInt -> ["int"]
    TByte -> ["byte"]
    TWord signed bits -> [(if signed then "i" else "u") ++ show bits]
    TBool -> ["bool"]
    -- (a list and a Box are named types, in the data as in the checker, so the programs that read the data see
    -- the struct a native list or Box is; the `list` and `box` tokens are only read, for data written before)
    TNamed base args -> ["named", quote base, show (length args)] ++ concatMap argTokens args
    TArrayOf t s -> "array" : typeTokens t ++ sizeTokens s
    TAddr t -> "addr" : typeTokens t
    TUninit t -> "uninit" : typeTokens t
    TBlock t -> "block" : typeTokens t
    TFn args ret -> ["fn", show (length args)] ++ concatMap typeTokens (args ++ [ret])
    TVariant n -> ["variant", quote n]
    TVar i -> ["var", show i]
    TForall sizes types t -> ["forall", show (length sizes)] ++ map quote sizes ++ [show (length types)] ++ map quote types ++ typeTokens t
    TParam n -> ["param", quote n]
    TRef t -> "ref" : typeTokens t
    TMutRef t -> "mutref" : typeTokens t

argTokens :: Arg -> [String]
argTokens (ArgSize s) = "size" : sizeTokens s
argTokens (ArgType ty) = "type" : typeTokens ty

sizeTokens :: Size -> [String]
sizeTokens s = case s of
    SizeConst n -> ["c", show n]
    SizeAny -> ["any"]
    SizeParam n -> ["p", quote n]
    SizeVar i -> ["v", show i]


quote :: String -> String
quote name = '"' : concatMap byteText (encodeUtf8 name) ++ "\""
  where
    byteText c
        | n >= 32 && n < 127 && c /= '"' && c /= '\\' = [c]
        | otherwise = ['\\', 'x', hexDigit (n `div` 16), hexDigit (n `mod` 16)]
      where
        n = fromEnum c
    hexDigit d = "0123456789ABCDEF" !! d

-- Reading

data Token = Word String | Str String
    deriving (Eq, Show)

tokenize :: String -> Result [Token] String
tokenize text = case text of
    [] -> Ok []
    ' ' : rest -> tokenize rest
    '"' : rest -> quoted rest [] `bindResult` \(name, more) -> mapResult (Str (decodeUtf8 name) :) (tokenize more)
    _ ->
        let (w, more) = break (== ' ') text
         in mapResult (Word w :) (tokenize more)
  where
    quoted s acc = case s of
        '"' : more -> Ok (reverse acc, more)
        '\\' : 'x' : h : l : more | Just a <- hexValue h, Just b <- hexValue l -> quoted more (toEnum (16 * a + b) : acc)
        '\\' : _ -> Error "a bad escape in a name"
        c : more -> quoted more (c : acc)
        [] -> Error "a name that is not closed"

-- A parser of the tokens of a line
newtype P a = P {runP :: [Token] -> Result (a, [Token]) String}

instance Functor P where
    fmap f (P g) = P (\ts -> mapResult (\(a, rest) -> (f a, rest)) (g ts))

instance Applicative P where
    pure a = P (\ts -> Ok (a, ts))
    P f <*> P g = P (\ts -> f ts `bindResult` \(h, rest) -> mapResult (\(a, rest') -> (h a, rest')) (g rest))

instance Monad P where
    P g >>= f = P (\ts -> g ts `bindResult` \(a, rest) -> runP (f a) rest)

failP :: String -> P a
failP e = P (\_ -> Error e)

word :: P String
word = P (\ts -> case ts of
    Word w : rest -> Ok (w, rest)
    _ -> Error "a word was expected")

name :: P String
name = P (\ts -> case ts of
    Str s : rest -> Ok (s, rest)
    _ -> Error "a name was expected")

expect :: String -> P ()
expect w = word >>= \found -> if found == w then pure () else failP ("expected " ++ w ++ ", found " ++ found)

integer :: P Integer
integer = word >>= \w -> case decimal w of
    Just n -> pure n
    Nothing -> failP ("a number was expected, found " ++ w)

int :: P Int
int = fromInteger <$> integer

-- A line parsed whole
parseLine :: P a -> [Token] -> Result a String
parseLine p ts = runP p ts `bindResult` \(a, rest) -> if null rest then Ok a else Error "a line has more in it than it should"


typeP :: P Type
typeP = word >>= \w -> case w of
    "int" -> pure TInt
    "byte" -> pure TByte
    "i8" -> pure (TWord True 8)
    "i16" -> pure (TWord True 16)
    "i32" -> pure (TWord True 32)
    "u16" -> pure (TWord False 16)
    "u32" -> pure (TWord False 32)
    "bool" -> pure TBool
    "list" -> TList <$> typeP
    "array" -> TArrayOf <$> typeP <*> sizeP
    "box" -> TBox <$> typeP
    "addr" -> TAddr <$> typeP
    "uninit" -> TUninit <$> typeP
    "block" -> TBlock <$> typeP
    "fn" -> int >>= \n -> replicateM n typeP >>= \args -> TFn args <$> typeP
    "named" -> name >>= \base -> int >>= \n -> TNamed base <$> replicateM n argP
    "variant" -> TVariant <$> name
    "var" -> TVar <$> int
    "forall" -> do
        sizes <- int >>= \n -> replicateM n name
        types <- int >>= \n -> replicateM n name
        TForall sizes types <$> typeP
    "param" -> TParam <$> name
    "ref" -> TRef <$> typeP
    "mutref" -> TMutRef <$> typeP
    _ -> failP ("not a type: " ++ w)

argP :: P Arg
argP = word >>= \w -> case w of
    "size" -> ArgSize <$> sizeP
    "type" -> ArgType <$> typeP
    _ -> failP ("not an argument: " ++ w)

sizeP :: P Size
sizeP = word >>= \w -> case w of
    "c" -> SizeConst <$> integer
    "any" -> pure SizeAny
    "p" -> SizeParam <$> name
    "v" -> SizeVar <$> int
    _ -> failP ("not a size: " ++ w)


decimal :: String -> Maybe Integer
decimal s = case s of
    '-' : ds | digits ds -> Just (negate (value ds))
    ds | digits ds -> Just (value ds)
    _ -> Nothing
  where
    digits ds = not (null ds) && all (\c -> c >= '0' && c <= '9') ds
    value = foldl' (\n c -> 10 * n + toInteger (fromEnum c - fromEnum '0')) 0

strictTokenize :: String -> Result [Token] String
strictTokenize line
    | any (\c -> c < ' ' || c > '~') line = Error "non-ASCII record"
    | otherwise = scan line `bindResult` \(ts, allValid) ->
        if allValid then Ok ts else Error "invalid UTF-8 or numeric token"
  where
    -- (a malformed token anywhere in the line is reported before an invalid word, as a whole-line scan would)
    scan [] = Ok ([], True)
    scan (' ' : xs) = scan xs
    scan ('"' : xs) = quotedStrict xs [] `bindResult` \(bytes, rest) ->
        strictName bytes (case rest of { [] -> Nothing; c : _ -> Just c }) (scan rest)
    scan xs =
        let (w, rest) = break (== ' ') xs
         in if '"' `elem` w || '\\' `elem` w
                then Error "malformed word"
                else mapResult (\(ts, ok) -> (Word w : ts, ok && validWord w)) (scan rest)
    quotedStrict [] _ = Error "unclosed name"
    quotedStrict ('"' : xs) acc = Ok (reverse acc, xs)
    quotedStrict ('\\' : 'x' : h : l : xs) acc
        | Just a <- hexValue h, Just b <- hexValue l = quotedStrict xs (toEnum (16 * a + b) : acc)
    quotedStrict ('\\' : _) _ = Error "malformed escape"
    quotedStrict (c : xs) acc = quotedStrict xs (c : acc)

strictTokenizeBytes :: B.ByteString -> Result [Token] String
strictTokenizeBytes line
    | B.any (\c -> c < ' ' || c > '~') line = Error "non-ASCII record"
    | otherwise = scan line `bindResult` \(ts, allValid) ->
        if allValid then Ok ts else Error "invalid UTF-8 or numeric token"
  where
    scan s = case B.uncons s of
        Nothing -> Ok ([], True)
        Just (' ', rest) -> scan rest
        Just ('"', rest) -> quotedStrict rest [] `bindResult` \(bytes, after) ->
            strictName bytes (fst <$> B.uncons after) (scan after)
        Just _ ->
            let (w, rest) = B.break (== ' ') s
             in if B.elem '"' w || B.elem '\\' w
                    then Error "malformed word"
                    else let text = B.unpack w in mapResult (\(ts, ok) -> (Word text : ts, ok && validWord text)) (scan rest)
    quotedStrict s acc = case B.uncons s of
        Nothing -> Error "unclosed name"
        Just ('"', xs) -> Ok (reverse acc, xs)
        Just ('\\', xs) -> case B.unpack (B.take 3 xs) of
            ['x', h, l] | Just a <- hexValue h, Just b <- hexValue l -> quotedStrict (B.drop 3 xs) (toEnum (16 * a + b) : acc)
            _ -> Error "malformed escape"
        Just (c, xs) -> quotedStrict xs (c : acc)

-- A quoted name's bytes, which have to be UTF-8 and followed by a space or the end of the record, and the tokens
-- after it
strictName :: String -> Maybe Char -> Result ([Token], Bool) String -> Result ([Token], Bool) String
strictName bytes next rest =
    let text = decodeUtf8 bytes
     in if encodeUtf8 text /= bytes
            then Error "invalid UTF-8"
            else case next of
                Nothing -> Ok ([Str text], True)
                Just ' ' -> mapResult (\(ts, ok) -> (Str text : ts, ok)) rest
                Just _ -> Error "missing token separator"

-- A word is a number that fits an Int or a letter followed by letters and digits
validWord :: String -> Bool
validWord w = case decimal w of
    Just n -> n >= -9223372036854775808 && n <= 9223372036854775807
    Nothing -> case w of
        c : rest -> alpha c && all (\x -> alpha x || (x >= '0' && x <= '9')) rest
        [] -> False
  where
    alpha c = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')

hexValue :: Char -> Maybe Int
hexValue c
    | c >= '0' && c <= '9' = Just (fromEnum c - fromEnum '0')
    | c >= 'A' && c <= 'F' = Just (fromEnum c - fromEnum 'A' + 10)
    | otherwise = Nothing
