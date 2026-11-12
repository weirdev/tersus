module TestDifferential (testDifferential) where

import AstData (writeBuiltinTable)
import BuiltinTable (builtinTable)
import Compile (parseWithEquality)
import Data.List (isInfixOf)
import LibPackage (inlinedLibraryLength)
import Modules (ModuleId (..))
import Differential
import ElaborateRequest
import MirLower (lowerElaborated)
import Syntax (Elaborated (..))
import TestData (typeCheckSources)
import TestHarness
import Compile (elaborateStatements)
import qualified Data.ByteString.Char8 as B
import ElaboratorTool (runElaboratorRaw, sourceElaborator, sourceElaboratorExecutable)
import Compile (sourceRequest)
import Types (Type (..))
import Utils

-- The compiler's elaborator behind the text protocol agrees with itself on the requests of a package, of the compiler
-- libraries, of the smallest compiler package (whose interfaces have every kind of entry), of a refused program and of
-- the programs of testTypeCheck
protocolAgreement :: IO TestResult
protocolAgreement = do
    let units = [FilePackage "examples/modules/app/main.tersus", Libraries, EmbeddedPackage "lib/mir/mir_erase/mir_erase.tersus", SourceFile "examples/rejected/type_argument_mismatch.tersus"] ++ [SourceText name source | (name, source) <- typeCheckSources]
    results <- runDifferential throughText units
    let (agree, wording, disagree, unmodelled, failed) = tally [o | (_, _, o) <- results]
    putStrLn ("differential: " ++ show (length units) ++ " units, " ++ show agree ++ " agree, " ++ show wording ++ " wording, " ++ show disagree ++ " disagree, " ++ show unmodelled ++ " not modelled, " ++ show failed ++ " failed")
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
    unmodelled <- runDifferential (\asked -> mapResult (map (\(m, _) -> (m, NotModelled "everything"))) <$> throughText asked) units
    pure $ firstFailure
        [ expect "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> o == Agree)
        , atLeastOne "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> False)
        , expect "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> o == Agree)
        , atLeastOne "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> False)
        , expect "not modelled" unmodelled (\o -> case o of NotModelledBy _ -> True; _ -> False)
        ]
  where
    perturbed change asked = mapResult (map (fmap change)) <$> throughText asked
    retype response = case response of
        Accepted (Elaborated stmts (t : ts)) i ls -> Accepted (Elaborated stmts ((if t == TBool then TInt else TBool) : ts)) i ls
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
    Right program -> case elaborateStatements program of
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

-- A module's request and response read back as written, and malformed ones are refused
protocolRoundTrip :: IO TestResult
protocolRoundTrip = do
    requests <- mapM (unitRequests compilerFrontend) [SourceText name source | (name, source) <- take 8 typeCheckSources]
    case sequence (map resultList requests) of
        Left e -> pure (Just e)
        Right exchanges -> case [(rq, r) | (AskedModule rq, answers) <- concat exchanges, (_, r) <- answers] of
            [] -> pure (Just "no requests")
            answered -> pure $ firstFailure (map (one . fst) answered ++ [malformed (fst (last answered))] ++ map verdict ([Refused "a \"refusal\"", RefusedInterface "in module p::m: no interface", Unresolved "in module p::m: unknown name q", NotModelled "what"] ++ withLibraries (map snd answered)))
  where
    resultList r = case r of
        Ok a -> Right a
        Error e -> Left e
    withLibraries responses = take 1 [Accepted e i ["types", "clone"] | Accepted e i _ <- responses]
    malformed rq = case (writeRequest rq, writeResponse (sourceElaborator rq)) of
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
                    let (before, rest) = break (\l -> take 8 l == "builtins") (lines text)
                        after = drop 1 (dropWhile (\l -> take 11 l /= "interfaces ") rest)
                        interfacesLine = head [l | l <- rest, take 11 l == "interfaces "]
                     in unlines (before ++ take 1 rest ++ ["data " ++ show (length (lines table))] ++ lines table ++ [interfacesLine] ++ after)
             in firstFailure
                    [ refused "a request with another header" (readRequest (swapLine "tersus-elaborate 1" "tersus-elaborate 2" request))
                    , refused "an unknown extraction" (readRequest (unlines [if take 8 l == "extract " then "extract all" else l | l <- lines request]))
                    , refused "a count with a leading zero" (readRequest (swapLine (firstData request) ("data 0" ++ drop 5 (firstData request)) request))
                    , refused "a block cut short" (readRequest (unlines (init (lines request))))
                    , refused "a line after the syntax" (readRequest (request ++ "more\n"))
                    , refused "two spaces after a key" (readRequest (unlines [if take 11 l == "predeclare " then "predeclare  " ++ drop 11 l else l | l <- lines request]))
                    , case (writeBuiltinTable builtinTable, writeBuiltinTable (take 1 builtinTable)) of
                        (Ok same, Ok other) -> firstFailure
                            [ either (Just . ("the same table put back: " ++)) (const Nothing) (resultEither (readRequest (withTable same request)))
                            , refused "another builtin table" (readRequest (withTable other request))
                            ]
                        (Error e, _) -> Just e
                        (_, Error e) -> Just e
                    , refused "a response with no interface line" (readResponse (unlines (takeWhile (\l -> take 9 l /= "interface") (lines response))))
                    , case [(e, i) | Accepted e i _ <- [sourceElaborator rq]] of
                        [] -> Just "the request was not accepted"
                        (e, i) : _ -> case writeResponse (Accepted e i ["types", "clone"]) of
                            Error err -> Just err
                            Ok text -> refused "a libraries line with a wrong count" (readResponse (swapLine "libraries 2 \"types\" \"clone\"" "libraries 3 \"types\" \"clone\"" text))
                    , refused "a response with another header" (readResponse (swapLine "tersus-elaborated 1" "tersus-elaborated 2" response))
                    ]
        (Error e, _) -> Just e
        (_, Error e) -> Just e
    -- (every verdict reads back as it was written)
    verdict response = case writeResponse response `bindResult` readResponse of
        Error e -> Just e
        Ok back -> testAssertEq (show back) (show response)
    one rq = case writeRequest rq `bindResult` readRequest of
        Error e -> Just e
        Ok rq' | rq' /= rq -> Just "request changed"
        Ok _ -> case writeResponse (sourceElaborator rq) of
            Error e -> Just e
            Ok text -> case readResponse text `bindResult` writeResponse of
                Error e -> Just e
                Ok text' -> testAssertEq text' text

-- A load request with a section malformed gets no answer: the executable exits saying it is not a request
malformedLoads :: IO TestResult
malformedLoads = case writeLoadRequest (sourceRequest LoadParse False False [] "return 1;") of
    Error e -> pure (Just e)
    Ok request -> do
        exe <- sourceElaboratorExecutable
        case exe of
            Error e -> pure (Just e)
            Ok path -> do
                let cases =
                        [ ("a file with a wrong byte count", replaceLine (\l -> take 16 l == "file \"<source>\" ") (\l -> unwords (init (words l) ++ [show (read (last (words l)) + 1 :: Int)])) request)
                        , ("a count of files that is not the files given", replaceLine (== "files 1") (const "files 2") request)
                        , ("no builtins", replaceLine (== "builtins") (const "") request)
                        , ("a record after the request", request ++ "more\n")
                        , ("an unknown kind of load", replaceLine (== "load parse") (const "load everything") request)
                        ]
                asWritten <- runElaboratorRaw path request
                answers <- mapM (runElaboratorRaw path . snd) cases
                pure $ firstFailure $
                    [ case asWritten of
                        Ok (header : _) | B.unpack header == "tersus-elaborated 1" -> Nothing
                        other -> Just ("the request as written was not answered: " ++ take 200 (show other))
                    ]
                        ++ [if text == request then Just (name ++ " changed nothing") else Nothing | (name, text) <- cases]
                        ++ [ case answer of
                            Ok (header : _) | B.unpack header == "tersus-elaborated 1" -> Just ("the elaborator answered " ++ name)
                            _ -> Nothing
                           | ((name, _), answer) <- zip cases answers
                           ]
  where
    replaceLine matches change text = unlines [if matches l then change l else l | l <- lines text]

-- A request says how many of its first statements are libraries checked where they were defined, and the elaborator
-- does not check their functions with bounds again: a count that covers the trait and the function below accepts a body
-- that its bounds do not allow, and one statement fewer, the libraries alone or one statement less than them refuses it
checkedStatements :: TestResult
checkedStatements = case parseWithEquality "trait Show { fn show(self: &Self) -> Int; }; fn same<T: Show>(a: T, b: T) -> Bool { return a = b; }; return 0;" of
    Left e -> Just e
    Right stmts ->
        let inlined = inlinedLibraryLength stmts
            request n = Request (ModuleId "main" Nothing) False False NoInterface [] [] [] [stmts] n
            refusedAt n = case sourceElaborator (request n) of
                Refused m | "T is compared with =" `isInfixOf` m -> Nothing
                other -> Just ("checked " ++ show n ++ " was not refused at the definition: " ++ show other)
            acceptedAt n = case sourceElaborator (request n) of
                Accepted {} -> Nothing
                other -> Just ("checked " ++ show n ++ " checked a definition again: " ++ show other)
         in firstFailure
                [ if inlined > 0 && inlined + 3 == length stmts then Nothing else Just ("the inlined libraries are " ++ show inlined ++ " of " ++ show (length stmts) ++ " statements")
                , refusedAt (inlined - 1)
                , refusedAt inlined
                , refusedAt (inlined + 1)
                , acceptedAt (inlined + 2)
                , acceptedAt (inlined + 3)
                , case writeRequest (request (inlined + 2)) of
                    Error e -> Just e
                    Ok text -> firstFailure
                        [ case readRequest text of
                            Ok rq | rq == request (inlined + 2) -> Nothing
                            _ -> Just "the checked count did not read back"
                        , case readRequest (unlines [if take 8 l == "builtins" then "builtins checked 0" else l | l <- lines text]) of
                            Error _ -> Nothing
                            Ok _ -> Just "accepted a checked count of 0"
                        ]
                ]

firstFailure :: [TestResult] -> TestResult
firstFailure = foldr (\r rest -> maybe rest Just r) Nothing

testDifferential :: Test
testDifferential = TestList "testDifferential"
    [ TestCase "requests and responses read back as written" protocolRoundTrip
    , TestCase "a candidate's mistakes are not agreements" mutationControls
    , testCase "the lowering takes exactly the elaborated expression types" visitOrder
    , TestCase "the text protocol loses nothing" protocolAgreement
    , testCase "functions with bounds of statements already checked are not checked again" checkedStatements
    , TestCase "malformed load requests are not answered" malformedLoads
    ]
