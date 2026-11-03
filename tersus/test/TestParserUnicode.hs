module TestParserUnicode (testParserUnicode) where

import Data.Char (chr, isLetter, isUpper, isLower, isAlphaNum)

import qualified Compile
import MirEval (MirValue (..), runNamedFunction)
import ParserUnicodeSource (parserUnicodeSource)
import TestHarness
import Utils

testParserUnicode :: Test
testParserUnicode = TestList "testParserUnicode"
    [TestCase "generated predicates match the oracle at every Unicode category boundary" identity]

identity :: IO TestResult
identity = pure $ case Compile.lowerSource False parserUnicodeSource of
    Error err -> Just err
    Ok program -> firstFailure
        [ case runNamedFunction program name [MInt (toInteger cp)] of
            Error err -> Just err
            Ok actual -> if actual == Just (MBool expected) then Nothing else Just (name ++ " at codepoint " ++ show cp ++ ": " ++ show actual ++ " vs " ++ show expected)
        | (name, cp, expected) <- checks
        ]
  where
    firstFailure [] = Nothing
    firstFailure (Nothing : rest) = firstFailure rest
    firstFailure (failure : _) = failure
    checks = concatMap boundaries [("parserUnicodeLetter", isLetter), ("parserUnicodeUpper", isUpper), ("parserUnicodeLower", isLower), ("parserUnicodeAlphaNum", isAlphaNum)]
    boundaries (name, predicate) = [(name, cp, expected cp) | cp <- [-1, 0, 127, 128] ++ changes ++ [0x10ffff, 0x110000]]
      where
        expected cp = cp >= 128 && cp <= 0x10ffff && predicate (chr cp)
        changes = concat [[cp - 1, cp] | cp <- [129..0x10ffff], predicate (chr (cp - 1)) /= predicate (chr cp)]
