module TestDifferential (testDifferential) where

import AstData (writeBuiltinTable)
import BuiltinTable (builtinTable)
import Compile (parseWithEquality)
import Differential
import ElaborateRequest
import MirLower (lowerElaborated)
import Syntax (Elaborated (..))
import TestData (typeCheckSources)
import TestHarness
import Compile (elaborateStatements)
import ElaboratorTool (runElaboratorText, sourceElaborator, sourceElaboratorExecutable)
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
    unmodelled <- runDifferential (\_ -> pure (Ok (NotModelled "everything"))) units
    pure $ firstFailure
        [ expect "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> o == Agree)
        , atLeastOne "retyped" retyped (\o -> case o of Disagree _ -> True; _ -> False)
        , expect "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> o == Agree)
        , atLeastOne "reworded" reworded (\o -> case o of Wording _ _ -> True; _ -> False)
        , expect "not modelled" unmodelled (\o -> case o of NotModelledBy _ -> True; _ -> False)
        ]
  where
    perturbed change rq = pure (Ok (change (sourceElaborator rq)))
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

-- A request and a response read back as written, and malformed ones are refused
protocolRoundTrip :: IO TestResult
protocolRoundTrip = do
    requests <- unitRequests sourceElaborator (FilePackage "examples/modules/app/main.tersus")
    case requests of
        Error e -> pure (Just e)
        Ok [] -> pure (Just "no requests")
        Ok answered -> do
            sections <- malformedSections [rq | (rq, _) <- answered, length (rqStatements rq) > 1]
            pure $ firstFailure (map (one . fst) answered ++ [malformed (fst (last answered)), sections] ++ map verdict ([Refused "a \"refusal\"", RefusedInterface "in module p::m: no interface", Unresolved "in module p::m: unknown name q", NotModelled "what"] ++ withLibraries (map snd answered)))
  where
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

-- A package module's request with its new sections malformed is refused by the compiler's reader and by the
-- elaborator's, and one whose syntax is not a block per file of the module is not written
malformedSections :: [Request] -> IO TestResult
malformedSections [] = pure (Just "no request for a module of several files")
malformedSections (rq : _) = case writeRequest rq of
    Error e -> pure (Just e)
    Ok request -> do
        exe <- sourceElaboratorExecutable
        case exe of
            Error e -> pure (Just e)
            Ok path -> do
                asWritten <- runElaboratorText path request
                let cases =
                        [ ("an empty library catalog", renameWord "libraries " "0" request)
                        , ("an unknown declaration kind", renameWord "decl " "constant" request)
                        , ("an unknown import level", renameWord "import " "package" request)
                        , ("a file of the module without its syntax", unlines (take (lastBlock (lines request)) (lines request)))
                        , ("syntax for a file the module does not have", unlines (lines request ++ drop (lastBlock (lines request)) (lines request)))
                        ]
                answers <- mapM (runElaboratorText path . snd) cases
                pure $ firstFailure $
                    [ case asWritten of
                        Error e -> Just ("the elaborator refused the request as written: " ++ e)
                        Ok _ -> Nothing
                    ]
                        ++ [if text == request then Just (name ++ " changed nothing") else Nothing | (name, text) <- cases]
                        ++ [refusedBy ("the compiler's reader accepted " ++ name) (readRequest text) | (name, text) <- cases]
                        ++ [refusedBy ("the elaborator accepted " ++ name) answer | ((name, _), answer) <- zip cases answers]
                        ++ [ refusedBy "a module's syntax with a file missing was written" (writeRequest rq{rqStatements = init (rqStatements rq)})
                           , refusedBy "a program's syntax of several blocks was written" (writeRequest rq{rqPackage = Nothing})
                           ]
  where
    refusedBy what r = case r of
        Error _ -> Nothing
        Ok _ -> Just what
    renameWord prefix new text = unlines (renameIn prefix new (lines text))
    renameIn prefix new (l : ls)
        | take (length prefix) l == prefix = (prefix ++ new ++ dropWhile (/= ' ') (drop (length prefix) l)) : ls
        | otherwise = l : renameIn prefix new ls
    renameIn _ _ [] = []
    lastBlock ls = head ([i | i <- reverse [0 .. length ls - 1], ls !! i == "data " ++ show (length ls - i - 1)] ++ [length ls])

firstFailure :: [TestResult] -> TestResult
firstFailure = foldr (\r rest -> maybe rest Just r) Nothing

testDifferential :: Test
testDifferential = TestList "testDifferential"
    [ TestCase "requests and responses read back as written" protocolRoundTrip
    , TestCase "a candidate's mistakes are not agreements" mutationControls
    , testCase "the lowering takes exactly the elaborated expression types" visitOrder
    , TestCase "the text protocol loses nothing" protocolAgreement
    ]
