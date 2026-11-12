module TestParserUnicode (testParserUnicode) where

import Data.Char (chr, isDigit)
import Data.List (isPrefixOf, isSuffixOf)

import qualified Compile
import ElaboratorTool (frontendToolFailure)
import MirEval (MirValue (..), runNamedFunction)
import ParsedFile (emptyDecls, fileBody)
import qualified ParserSeed
import PreludeSource (parserUnicodeSource)
import qualified TersusParser
import Syntax (Expression (..), Statement (..), Value (..))
import TestHarness
import Utils

testParserUnicode :: Test
testParserUnicode = TestList "testParserUnicode"
    [ TestCase "the classifiers hold exactly the checked-in intervals at every boundary" boundaries
    , TestList "identifiers follow Unicode 15.0 through the production frontend and P1"
        [ TestCase (show cp) (identifier cp letter)
        | (cp, letter) <-
            [ (0x1056f, False), (0x10570, True), (0x1057a, True), (0x10597, True)
            , (0x16a6f, False), (0x16a70, True), (0x16abe, True)
            , (0x1e28f, False), (0x1e290, True), (0x1e2ad, True)
            , (0x11f01, False), (0x11f02, True)
            , (0x1e4cf, False), (0x1e4d0, True)
            ]
        ]
    ]

-- The intervals each classifier's part functions test, read from the checked-in file
intervalsOf :: String -> [(Int, Int)]
intervalsOf name = concat [comparisons body | definition <- splitOn "fn " parserUnicodeSource, let (header, body) = break (== '(') definition, (name ++ "Part") `isPrefixOf` header]
  where
    comparisons text = case breakOn "cp >= " text of
        Nothing -> []
        Just rest ->
            let (lo, afterLo) = span isDigit rest
             in case breakOn "cp <= " afterLo of
                    Just more -> let (hi, remaining) = span isDigit more in (read lo, read hi) : comparisons remaining
                    Nothing -> []
    breakOn pattern text
        | null text = Nothing
        | pattern `isPrefixOf` text = Just (drop (length pattern) text)
        | otherwise = breakOn pattern (tail text)
    splitOn pattern text = case breakOn pattern text of
        Nothing -> [text]
        Just rest -> takeWhile' text : splitOn pattern rest
      where
        takeWhile' t = if pattern `isPrefixOf` t || null t then "" else head t : takeWhile' (tail t)

boundaries :: IO TestResult
boundaries = pure $ case Compile.lowerSource False parserUnicodeSource of
    Error err -> Just err
    Ok program -> firstFailure $
        [ testAssertTrue (not (null (intervalsOf name))) | name <- names ] ++
        [ case runNamedFunction program name [MInt (toInteger cp)] of
            Error err -> Just err
            Ok actual -> if actual == Just (MBool expected) then Nothing else Just (name ++ " at codepoint " ++ show cp ++ ": " ++ show actual ++ " vs " ++ show expected)
        | name <- names
        , let intervals = intervalsOf name
        , cp <- [-1, 0, 127, 128, 0x10ffff, 0x110000] ++ concat [[lo - 1, lo, hi, hi + 1] | (lo, hi) <- intervals]
        , let expected = any (\(lo, hi) -> cp >= lo && cp <= hi) intervals
        ]
  where
    names = ["parserUnicodeLetter", "parserUnicodeUpper", "parserUnicodeLower", "parserUnicodeAlphaNum"]
    firstFailure results = case [e | Just e <- results] of
        e : _ -> Just e
        [] -> Nothing

identifier :: Int -> Bool -> IO TestResult
identifier cp letter = do
    let name = [chr cp]
        source = name ++ " = 1; return " ++ name ++ ";"
        expected = [Assign name (Val (VInt 1)), Return (Var name)]
    native <- TersusParser.parseFileNative emptyDecls source
    let production = Compile.parseSource source
    pure $ case (native, production) of
        (Left e, _) | ParserSeed.toolFailure e -> Just e
        (_, Error e) | ParserSeed.toolFailure e || frontendToolFailure e -> Just e
        (Right (parsed, _), Ok statements) | letter ->
            testAssertEq (fileBody parsed) expected <> testAssertTrue (expected `isSuffixOf` filter (not . isMark) statements)
        (Left _, Error _) | not letter -> Nothing
        _ -> Just ("P1 or the production frontend disagrees with Unicode 15.0 on " ++ show cp ++ ": P1 " ++ either (const "refused") (const "accepted") native ++ ", production " ++ described production)
  where
    isMark statement = case statement of
        Mark _ _ -> True
        _ -> False
    described (Ok _) = "accepted"
    described (Error e) = "refused: " ++ e
