module TestDifferential (testDifferential, ergonomicsUnits) where

import AstData (writeBuiltinTable)
import BuiltinTable (builtinTable)
import Compile (parseWithEquality)
import Differential
import ElaborateRequest
import MirLower (lowerElaborated)
import Syntax (Elaborated (..))
import TestData (typeCheckSources)
import TestHarness
import TypeCheck (elaborate)
import Types (Type (..))
import Utils

ergonomicsUnits :: [Unit]
ergonomicsUnits =
    [ SourceText "if expression protocol" "x = if true { 3 } else { 4 }; return x;"
    , SourceText "block expression protocol" "return if true { let x = 3; x + 1 } else { 5 };"
    , SourceText "ascribed declaration protocol" "let x: Int = 3; return x;"
    , SourceText "generic template expression protocol" "fn choose<T>(c: Bool, a: T, b: T) -> T { let result: T = if c { a } else { b }; return result; }; return choose(true, 1, 2);"
    ]

-- The Haskell elaborator behind the text protocol agrees with itself on every request of a share of the corpus
-- (with the programs of testTypeCheck)
protocolAgreement :: Int -> IO TestResult
protocolAgreement batch = do
    files <- corpusUnits
    let units = batchItems 4 batch (files ++ [SourceText name source | (name, source) <- typeCheckSources] ++ ergonomicsUnits)
    results <- runDifferential throughText units
    let (agree, wording, disagree, unmodelled, failed) = tally [o | (_, _, o) <- results]
    putStrLn ("differential batch " ++ show batch ++ "/4: " ++ show (length units) ++ " units, " ++ show agree ++ " agree, " ++ show wording ++ " wording, " ++ show disagree ++ " disagree, " ++ show unmodelled ++ " not modelled, " ++ show failed ++ " failed")
    pure $ case [(unit, modu, o) | (unit, modu, o) <- results, o /= Agree] of
        [] | agree > 0 -> Nothing
        [] -> Just "no requests"
        (unit, modu, o) : _ -> Just (show unit ++ " " ++ modu ++ ": " ++ show o)

-- A candidate that gives one expression another type, or a refusal other words, or does not handle the program,
-- is not counted as agreeing
mutationControls :: IO TestResult
mutationControls = do
    let units = [SourceFile "examples/arithmetic.tersus", SourceFile "examples/rejected/type_argument_mismatch.tersus"]
    retyped <- runDifferential (perturbed retype) units
    reworded <- runDifferential (perturbed reword) units
    unmodelled <- runDifferential (\_ -> pure (Ok (NotModelled "everything"))) units
    pure $ firstFailure
        [ expect "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> o == Agree)
        , atLeastOne "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> False)
        , expect "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> o == Agree)
        , atLeastOne "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> False)
        , expect "not modelled" unmodelled (\o -> case o of NotModelledBy _ -> True; _ -> False)
        ]
  where
    perturbed change rq = pure (Ok (change (respond rq)))
    retype response = case response of
        Accepted (Elaborated stmts (t : ts)) i -> Accepted (Elaborated stmts ((if t == TBool then TInt else TBool) : ts)) i
        other -> other
    reword response = case response of
        Refused m -> Refused (m ++ "!")
        other -> other
    expect name results ok = case [o | (_, _, o) <- results, not (ok o)] of
        [] -> Nothing
        o : _ -> Just (name ++ ": " ++ show o)
    atLeastOne name results ok = if any (\(_, _, o) -> ok o) results then Nothing else Just (name ++ ": no request was caught")

-- The lowering takes exactly the expression types the elaboration gives, in their order: one more or one fewer is
-- refused, and two in the wrong order give another program (not every pair would: some types the lowering takes
-- leave no trace in what it writes)
visitOrder :: TestResult
visitOrder = case parseWithEquality "x = [true]; n = 3; return n;" of
    Left e -> Just e
    Right program -> case elaborate program of
        Error e -> Just e
        Ok (Elaborated stmts types) -> firstFailure
            [ case lowerElaborated (Elaborated stmts types) of
                Error e -> Just e
                Ok _ -> Nothing
            , testAssertErrorContains "never reached" (lowerElaborated (Elaborated stmts (types ++ [TInt])))
            , testAssertErrorContains "ran out of expression types" (lowerElaborated (Elaborated stmts (drop 1 types)))
            , case [i | (i, (a, b)) <- zip [0 ..] (zip types (drop 1 types)), a /= b] of
                [] -> Just "no two neighbouring types differ"
                i : _ ->
                    let swapped = take i types ++ [types !! (i + 1), types !! i] ++ drop (i + 2) types
                     in if show (lowerElaborated (Elaborated stmts swapped)) == show (lowerElaborated (Elaborated stmts types))
                            then Just "the lowering did not notice two types in the wrong order"
                            else Nothing
            ]

-- A request and a response read back as written, and malformed ones are refused
protocolRoundTrip :: IO TestResult
protocolRoundTrip = do
    requests <- unitRequests (FilePackage "examples/modules/app/main.tersus")
    pure $ case requests of
        Error e -> Just e
        Ok [] -> Just "no requests"
        Ok answered -> firstFailure (map (one . fst) answered ++ [malformed (fst (last answered))])
  where
    malformed rq = case (writeRequest rq, writeResponse (respond rq)) of
        (Ok request, Ok response) ->
            let refused name r = case r of
                    Error _ -> Nothing
                    Ok _ -> Just ("accepted " ++ name)
                swapLine old new text = unlines [if l == old then new else l | l <- lines text]
                firstData text = head [l | l <- lines text, take 5 l == "data "]
                resultEither r = case r of
                    Ok a -> Right a
                    Error e -> Left e
                withTable table text =
                    let (before, rest) = break (== "builtins") (lines text)
                        after = drop 1 (dropWhile (\l -> take 11 l /= "interfaces ") rest)
                        interfacesLine = head [l | l <- rest, take 11 l == "interfaces "]
                     in unlines (before ++ ["builtins", "data " ++ show (length (lines table))] ++ lines table ++ [interfacesLine] ++ after)
             in firstFailure
                    [ refused "a request with another header" (readRequest (swapLine "tersus-elaborate 1" "tersus-elaborate 2" request))
                    , refused "an unknown extraction" (readRequest (unlines [if take 8 l == "extract " then "extract all" else l | l <- lines request]))
                    , refused "a count with a leading zero" (readRequest (swapLine (firstData request) ("data 0" ++ drop 5 (firstData request)) request))
                    , refused "a block cut short" (readRequest (unlines (init (lines request))))
                    , refused "a line after the syntax" (readRequest (request ++ "more\n"))
                    , refused "two spaces after a key" (readRequest (swapLine "predeclare true" "predeclare  true" request))
                    , case (writeBuiltinTable builtinTable, writeBuiltinTable (take 1 builtinTable)) of
                        (Ok same, Ok other) -> firstFailure
                            [ either (Just . ("the same table put back: " ++)) (const Nothing) (resultEither (readRequest (withTable same request)))
                            , refused "another builtin table" (readRequest (withTable other request))
                            ]
                        (Error e, _) -> Just e
                        (_, Error e) -> Just e
                    , refused "a response with no interface line" (readResponse (unlines (takeWhile (/= "interface") (lines response))))
                    , refused "a response with another header" (readResponse (swapLine "tersus-elaborated 1" "tersus-elaborated 2" response))
                    ]
        (Error e, _) -> Just e
        (_, Error e) -> Just e
    one rq = case writeRequest rq `bindResult` readRequest of
        Error e -> Just e
        Ok rq' | rq' /= rq -> Just "request changed"
        Ok _ -> case writeResponse (respond rq) of
            Error e -> Just e
            Ok text -> case readResponse text `bindResult` writeResponse of
                Error e -> Just e
                Ok text' -> testAssertEq text' text

firstFailure :: [TestResult] -> TestResult
firstFailure = foldr (\r rest -> maybe rest Just r) Nothing

testDifferential :: Test
testDifferential = TestList "testDifferential"
    [ TestCase "requests and responses read back as written" protocolRoundTrip
    , TestCase "a candidate's mistakes are not agreements" mutationControls
    , testCase "the lowering takes exactly the elaborated expression types" visitOrder
    , TestList "the text protocol loses nothing over the corpus"
        [TestCase (show batch ++ "/4") (protocolAgreement batch) | batch <- [1 .. 4]]
    ]
