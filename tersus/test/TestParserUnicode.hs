module TestParserUnicode (testParserUnicode) where

import Data.Char (chr, isLetter, isUpper, isLower, isAlphaNum)

import qualified Compile
import MirEval (MirValue (..), runNamedFunction)
import ParserUnicodeSource (parserUnicodeSource)
import ParsedFile (emptyDecls, fileBody)
import qualified ParserSeed
import qualified TersusParser
import Syntax (Expression (..), Statement (..), Value (..))
import TestHarness
import Utils

testParserUnicode :: Test
testParserUnicode = TestList "testParserUnicode"
    [ TestCase "generated predicates match the oracle at every Unicode category boundary" identity
    , TestList "P1 identifiers follow the serving GHC Unicode version"
        [ TestCase (show cp) (servingIdentifier cp)
        | cp <- [0x1056f, 0x10570, 0x1057a, 0x10597, 0x16a6f, 0x16a70, 0x16abe, 0x1e28f, 0x1e290, 0x1e2ad, 0x11f01, 0x11f02, 0x1e4cf, 0x1e4d0]
        ]
    ]

servingIdentifier :: Int -> IO TestResult
servingIdentifier cp = do
    let name = [chr cp]
        source = name ++ " = 1; return " ++ name ++ ";"
    answer <- TersusParser.parseFileNative emptyDecls source
    pure $ case answer of
        Left e | ParserSeed.toolFailure e -> Just e
        Left _ -> testAssertTrue (not (isLetter (chr cp)))
        Right (parsed, _) -> testAssertTrue (isLetter (chr cp)) <> testAssertEq (fileBody parsed) [Assign name (Val (VInt 1)), Return (Var name)]

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
