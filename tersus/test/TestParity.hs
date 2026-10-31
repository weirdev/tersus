module TestParity
    ( testParity
    , parityCases
    , ParityCase (..)
    , unsupportedReason
    ) where

import Control.Concurrent.MVar (MVar, modifyMVar, newMVar)
import Control.Exception (evaluate)
import System.Timeout (timeout)
import Data.List (isInfixOf, isPrefixOf, nub)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import System.IO.Unsafe (unsafePerformIO)

import Cli (World (..), noWorld, runProgramIn)
import qualified Mir as M
import MirData (forNative, readProgram, writeProgram)
import MirLower (lowerElaborated)
import qualified MirValidate as Reference
import MirGhost (eraseGhosts)
import Pipeline (ownedSource, parseSource)
import SelfHostedMir (validateMirSubset)
import StdLibDefs (stdLibValCtx)
import Syntax
import TestHarness
import TestMirReader (sameText)
import TestNative (validatedPrograms)
import TestPipeline (exampleExpectations)
import TypeCheck (elaborate)
import Types
import Utils

data ParityCase = ParityCase
    { parityName :: String
    , paritySource :: IO String
    }

parityCases :: [ParityCase]
parityCases =
    [ParityCase ("example " ++ path) (readFile path) | (path, _) <- exampleExpectations]
        ++ [ParityCase ("program " ++ name) (pure source) | (name, source) <- validatedPrograms]

data Tally = Tally
    { tallyTotal :: Int
    , tallyExercised :: Int
    , tallySkipReasons :: Map.Map String Int
    , tallyNotMir :: Int
    , tallyTimedOut :: [String]
    , tallyReader :: Int
    , tallyReaderSkipped :: Int
    , tallyReaderTimedOut :: [String]
    }

emptyTally :: Tally
emptyTally = Tally 0 0 Map.empty 0 [] 0 0 []

{-# NOINLINE parityTally #-}
parityTally :: MVar Tally
parityTally = unsafePerformIO (newMVar emptyTally)

bump :: (Tally -> Tally) -> IO ()
bump f = modifyMVar parityTally (\t -> pure (f t, ()))

testParity :: Test
testParity =
    TestList
        "testParity"
        [ TestParallel "validation" [TestCase (parityName c) (validationCase c) | c <- parityCases]
        , TestParallel "mirReader" [TestCase (parityName c) (readerCase c) | c <- readerCases]
        , TestCase "corpus summary" summaryCase
        ]

readerEvery :: Int
readerEvery = 7

readerCases :: [ParityCase]
readerCases = [c | (i, c) <- zip [0 :: Int ..] parityCases, i `mod` readerEvery == 0]

summaryCase :: IO TestResult
summaryCase = do
    tally <- modifyMVar parityTally (\t -> pure (t, t))
    putStrLn $
        "parity corpus: "
            ++ show (tallyTotal tally)
            ++ " cases, "
            ++ show (tallyExercised tally)
            ++ " exercised by the self-hosted validator, "
            ++ show (sum (Map.elems (tallySkipReasons tally)))
            ++ " skipped by the capability predicate, "
            ++ show (tallyNotMir tally)
            ++ " not lowered to MIR, "
            ++ show (length (tallyTimedOut tally))
            ++ " timed out in the self-hosted validator, "
            ++ show (tallyReader tally)
            ++ " read back through the Tersus MIR reader (every "
            ++ show readerEvery
            ++ "th case), "
            ++ show (tallyReaderSkipped tally)
            ++ " of those not compiled programs, "
            ++ show (length (tallyReaderTimedOut tally))
            ++ " of those timed out in the reader"
    mapM_ (\(reason, n) -> putStrLn ("parity skipped, " ++ show n ++ ": " ++ reason)) (Map.toList (tallySkipReasons tally))
    mapM_ (\name -> putStrLn ("parity timed out in the self-hosted validator: " ++ name)) (tallyTimedOut tally)
    mapM_ (\name -> putStrLn ("parity timed out in the Tersus MIR reader: " ++ name)) (tallyReaderTimedOut tally)
    pure $
        if tallyExercised tally == 0
            then Just "the parity corpus exercised no program through the self-hosted validator"
            else Nothing

-- The self-hosted validator, lowered once for this group. It is not validated
-- again here: that lib/validation.tersus itself validates is checked with
-- compileSource by testSelfHostedEquality in TestPipeline, and validating it
-- with the reference validator costs more than every case below together.
{-# NOINLINE checkerResult #-}
checkerResult :: MVar (Maybe (Result M.Program String))
checkerResult = unsafePerformIO (newMVar Nothing)

checkerProgram :: IO (Result M.Program String)
checkerProgram = modifyMVar checkerResult $ \cached -> case cached of
    Just result -> pure (cached, result)
    Nothing -> do
        source <- readFile "lib/validation.tersus"
        let result = parseSource source `bindResult` elaborate `bindResult` lowerElaborated `bindResult` eraseGhosts
        pure (Just result, result)

validationCase :: ParityCase -> IO TestResult
validationCase parityCase = do
    bump (\t -> t{tallyTotal = tallyTotal t + 1})
    source <- paritySource parityCase
    checkerResult' <- checkerProgram
    case checkerResult' of
        Error e -> pure (Just (parityName parityCase ++ ": the Tersus validator does not compile: " ++ e))
        Ok checker -> case lower source of
            Error _ -> do
                bump (\t -> t{tallyNotMir = tallyNotMir t + 1})
                pure Nothing
            Ok mir -> case unsupportedReason mir of
                Just reason -> do
                    bump (\t -> t{tallySkipReasons = Map.insertWith (+) reason 1 (tallySkipReasons t)})
                    pure Nothing
                Nothing -> do
                    let outcome = case (Reference.validateProgram mir, validateMirSubset checker mir) of
                            (Ok _, Ok (Just True)) -> Nothing
                            (Error _, Ok (Just False)) -> Nothing
                            (Ok _, Ok (Just False)) -> Just "the reference validator accepts and the self-hosted validator rejects"
                            (Error e, Ok (Just True)) -> Just ("the reference validator rejects (" ++ take 120 e ++ ") and the self-hosted validator accepts")
                            (_, Ok Nothing) -> Just "the capability predicate claims this program is supported, but the self-hosted bridge returned Nothing: extend unsupportedReason in TestParity with the documented limitation, or fix SelfHostedMir"
                            (_, Error e) -> Just ("the self-hosted validator failed: " ++ e)
                    finished <- timeout validationTimeoutMicros (evaluate (maybe 0 length outcome))
                    case finished of
                        Nothing -> do
                            bump (\t -> t{tallyTimedOut = tallyTimedOut t ++ [parityName parityCase]})
                            pure Nothing
                        Just _ -> do
                            case outcome of
                                Nothing -> bump (\t -> t{tallyExercised = tallyExercised t + 1})
                                Just _ -> pure ()
                            pure (fmap (\message -> parityName parityCase ++ ": " ++ message) outcome)

validationTimeoutMicros :: Int
validationTimeoutMicros = 10000000

lower :: String -> Result M.Program String
lower source = parseSource source `bindResult` elaborate `bindResult` lowerElaborated

readerCase :: ParityCase -> IO TestResult
readerCase parityCase = do
    source <- paritySource parityCase
    readerResult <- compileOnce =<< readFile "examples/mir_reader.tersus"
    case (ownedSource source, readerResult) of
        (Error _, _) -> do
            bump (\t -> t{tallyReaderSkipped = tallyReaderSkipped t + 1})
            pure Nothing
        (_, Error e) -> pure (Just (parityName parityCase ++ ": the Tersus MIR reader does not compile: " ++ e))
        (Ok owned, Ok reader) -> do
            let text = writeProgram owned
                haskellRoundTrip = case readProgram text of
                    Error e -> Just ("the Haskell MIR reader refuses its own data: " ++ e)
                    Ok back -> if back == forNative owned then Nothing else Just "the Haskell MIR reader reads back another program"
            case haskellRoundTrip of
                Just message -> pure (Just (parityName parityCase ++ ": " ++ message))
                Nothing -> do
                    let outcome = case runProgramIn noWorld{worldInput = text} reader of
                            Error e -> Just ("the Tersus MIR reader failed: " ++ e)
                            Ok ((output, errors), _)
                                | not (null errors) -> Just ("the Tersus MIR reader reported: " ++ errors)
                                | sameText output text -> Nothing
                                | otherwise -> Just "the Tersus MIR reader wrote back different data"
                    finished <- timeout validationTimeoutMicros (evaluate (maybe 0 length outcome))
                    case finished of
                        Nothing -> do
                            bump (\t -> t{tallyReaderTimedOut = tallyReaderTimedOut t ++ [parityName parityCase]})
                            pure Nothing
                        Just _ -> do
                            case outcome of
                                Nothing -> bump (\t -> t{tallyReader = tallyReader t + 1})
                                Just _ -> pure ()
                            pure (fmap (\message -> parityName parityCase ++ ": " ++ message) outcome)

unsupportedReason :: M.Program -> Maybe String
unsupportedReason program
    | any isEnumDecl (Map.elems (M.progTypes program)) = Just "enum types"
    | any externFn allFunctions = Just "extern functions"
    | any unsupportedLocalType allFunctions = Just "word, address, block, function, forall, uninit or reference types"
    | any unsupportedDeclType (Map.elems (M.progTypes program)) = Just "word, address, block, function, forall, uninit or reference types in a declaration"
    | not (Set.null (M.readersOfInput program)) = Just "programs that read the world (input, arguments or files)"
    | not (null (M.fnParams (M.progMain program))) = Just "a main with parameters"
    | not (null (M.specRequires mainSpec)) || not (null (M.specEnsures mainSpec)) = Just "contracts on main"
    | any (\fn -> M.specTermination (M.fnSpec fn) /= Nothing) allFunctions = Just "shrinks or termination clauses on functions"
    | Just reason <- unsupportedShape program = Just reason
    | Just reason <- unsupportedProofs program = Just reason
    | Just reason <- unsupportedCalls program = Just reason
    | Just reason <- unsupportedLoops program = Just reason
    | Just reason <- unsupportedAssumed program = Just reason
    | Just reason <- unsupportedReturn program = Just reason
    | otherwise = Nothing
  where
    allFunctions = M.progMain program : Map.elems (M.progFunctions program)
    mainSpec = M.fnSpec (M.progMain program)
    isEnumDecl M.EnumDecl{} = True
    isEnumDecl _ = False
    externFn fn = "extern " `isPrefixOf` M.fnName fn
    unsupportedLocalType fn = any (unsupportedType . M.localType) (Map.elems (M.fnLocals fn)) || maybe False unsupportedType (M.fnReturns fn)
    unsupportedDeclType (M.StructDecl fields) = any (unsupportedType . snd) fields
    unsupportedDeclType (M.EnumDecl variants) = any (any (unsupportedType . snd) . snd) variants

unsupportedType :: Type -> Bool
unsupportedType t = case t of
    TWord{} -> True
    TAddr{} -> True
    TBlock{} -> True
    TList element -> unsupportedType element
    TArrayOf element _ -> unsupportedType element
    TBox element -> unsupportedType element
    TFn args result -> any unsupportedType (result : args)
    TForall _ _ element -> unsupportedType element
    TUninit element -> unsupportedType element
    TRef element -> unsupportedType element
    TNamed _ args -> any argUnsupported args
    _ -> False
  where
    argUnsupported (ArgType element) = unsupportedType element
    argUnsupported _ = False

unsupportedShape :: M.Program -> Maybe String
unsupportedShape program
    | any negativeLocal allFunctions = Just "negative locals"
    | any badParams allFunctions = Just "duplicate, return-slot or size parameters"
    | any (\fn -> Map.member (M.BlockId (-1)) (M.fnBlocks fn)) allFunctions = Just "a block numbered -1"
    | any badBlock allBlocks = Just "statements, operations, operands, constants or terminators outside the subset (ownership, address, block, world, narrow, variant or function-value operations, moved operands, data or function constants, unreachable or indirect calls)"
    | badDefinitions = Just "function definitions that are nested, not at the top of main, duplicated, or named for the standard library"
    | genericInvariantInstance = Just "invariants of a generic struct instance"
    | badNewArraySize = Just "an array made with a length that is not its size parameter"
    | otherwise = Nothing
  where
    allFunctions = M.progMain program : Map.elems (M.progFunctions program)
    allBlocks = [block | fn <- allFunctions, block <- Map.elems (M.fnBlocks fn)]
    negativeLocal fn = any (\(M.Local n) -> n < 0) (Map.keys (M.fnLocals fn))
    badParams fn =
        length (M.fnParams fn) /= length (nub (M.fnParams fn))
            || M.Local 0 `elem` M.fnParams fn
            || length (M.fnSizeParams fn) > length (M.fnParams fn)
            || length (M.fnSizeParams fn) /= length (nub (M.fnSizeParams fn))
            || any ambiguous (M.fnSizeParams fn)
            || any assigned sizeParams
            || any wrongName (zip sizeParams (M.fnSizeParams fn))
      where
        sizeParams = drop (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn)
        ambiguous name = length [p | p <- M.fnParams fn, Just d <- [Map.lookup p (M.fnLocals fn)], M.localName d == Just name] /= 1
        assigned local = any (writes local) (concatMap M.blockStatements (Map.elems (M.fnBlocks fn))) || any (termWrites local . M.blockTerminator) (Map.elems (M.fnBlocks fn))
        writes local (M.Assign dest _) = local == dest
        writes local (M.Peek dest _) = local == dest
        writes local (M.Drop dest) = local == dest
        writes _ _ = False
        termWrites local (M.Call _ _ dest _) = local == dest
        termWrites _ _ = False
        wrongName (local, name) = (M.localName =<< Map.lookup local (M.fnLocals fn)) /= Just name
    badBlock (M.BasicBlock stmts term) = any badStmt stmts || badTerm term
    badStmt (M.Drop _) = True
    badStmt (M.Peek _ _) = True
    badStmt (M.Ghost _ (M.GhostValidation (ProofAssert _))) = False
    badStmt (M.Ghost _ M.GhostFunction{}) = False
    badStmt (M.Ghost _ _) = True
    badStmt (M.Assign _ rvalue) = badRvalue rvalue
    badRvalue (M.Use operand) = badOperand operand
    badRvalue (M.BinaryOp _ a b) = badOperand a || badOperand b
    badRvalue (M.ListOp op args) = op `notElem` supportedListOps || length args /= listOpArity op || any badOperand args
    badRvalue (M.MakeBox operand) = badOperand operand
    badRvalue (M.Unbox operand) = badOperand operand
    badRvalue (M.Unsize operand) = badOperand operand
    badRvalue (M.CopyOf operand) = badOperand operand
    badRvalue (M.MakeData _ fields) = any (badOperand . snd) fields
    badRvalue (M.ReadField operand _ _) = badOperand operand
    badRvalue _ = True
    supportedListOps = [M.Length, M.Get, M.Push, M.Pop, M.Set, M.NewArray, M.NewBoxed, M.NewEmptyBoxed, M.First, M.Last]
    listOpArity op = case op of
        M.Length -> 1
        M.Get -> 2
        M.Push -> 2
        M.Pop -> 1
        M.Set -> 3
        M.NewArray -> 2
        M.NewBoxed -> 2
        M.NewEmptyBoxed -> 0
        M.First -> 1
        M.Last -> 1
        _ -> -1
    badOperand (M.Move _) = True
    badOperand (M.Copy _) = False
    badOperand (M.Const constant) = badConstant constant
    badConstant (M.CInt n) = not (inIntRange n)
    badConstant (M.CBool _) = False
    badConstant (M.CList values) = any badConstant values
    badConstant (M.CArray values) = any badConstant values
    badConstant _ = True
    badTerm M.Return = False
    badTerm (M.Goto _) = False
    badTerm (M.SwitchBool (M.Copy _) _ _) = False
    badTerm (M.SwitchBool (M.Const (M.CBool _)) _ _) = False
    badTerm (M.SwitchBool _ _ _) = True
    badTerm (M.Call (M.Const (M.CFn _)) args _ _) = any badOperand args
    badTerm (M.Call _ _ _ _) = True
    badTerm M.Unreachable = True
    definitions =
        [ (isMain, blockId, name, source, top)
        | (isMain, fn) <- (True, M.progMain program) : [(False, f) | f <- Map.elems (M.progFunctions program)]
        , (blockId, block) <- Map.toList (M.fnBlocks fn)
        , M.Ghost _ (M.GhostFunction name source top) <- M.blockStatements block
        ]
    badDefinitions =
        any (\(isMain, blockId, _, _, top) -> not top || not isMain || blockId /= M.BlockId 0) definitions
            || any (\name -> Map.member name (fst stdLibValCtx)) sources
            || length sources /= length (nub sources)
            || length targets /= length (nub targets)
            || length targets /= Map.size (M.progFunctions program)
            || any (\name -> Map.notMember name (M.progFunctions program)) targets
            || any (\(name, fn) -> name /= M.fnName fn) (Map.toList (M.progFunctions program))
      where
        sources = [source | (_, _, _, source, _) <- definitions]
        targets = [name | (_, _, name, _, _) <- definitions]
    genericInvariantInstance =
        or
            [ not (null clauses) && not (null args)
            | fn <- allFunctions
            , decl <- Map.elems (M.fnLocals fn)
            , TNamed base args <- [M.localType decl]
            , let clauses = Map.findWithDefault [] base (M.progInvariants program)
            ]
            || or
                [ '<' `elem` name && not (null (Map.findWithDefault [] (baseName name) (M.progInvariants program)))
                | fn <- allFunctions
                , block <- Map.elems (M.fnBlocks fn)
                , M.Assign _ (M.MakeData name _) <- M.blockStatements block
                ]
    baseName name = takeWhile (/= '<') name
    badNewArraySize =
        or
            [ case [p | p <- sizeParamsOf fn, Just d <- [Map.lookup p (M.fnLocals fn)], M.localName d == Just sizeName] of
                p : _ -> lengthValue /= M.Copy p
                [] -> True
            | fn <- allFunctions
            , block <- Map.elems (M.fnBlocks fn)
            , M.Assign dest (M.ListOp M.NewArray [lengthValue, _]) <- M.blockStatements block
            , Just decl <- [Map.lookup dest (M.fnLocals fn)]
            , TArrayOf _ (SizeParam sizeName) <- [M.localType decl]
            ]
    sizeParamsOf fn = drop (length (M.fnParams fn) - length (M.fnSizeParams fn)) (M.fnParams fn)

unsupportedProofs :: M.Program -> Maybe String
unsupportedProofs program
    | any (not . proofSupported) allClauses = Just "proof forms outside the subset (only relation asserts over locals, literals and size, field, get, set, push, pop, first, last, array and arithmetic applications)"
    | otherwise = Nothing
  where
    allFunctions = M.progMain program : Map.elems (M.progFunctions program)
    allClauses =
        concatMap (\fn -> M.specRequires (M.fnSpec fn) ++ M.specEnsures (M.fnSpec fn)) allFunctions
            ++ concatMap (M.loopInvariant . snd) (concatMap (Map.toList . M.specLoops . M.fnSpec) allFunctions)
            ++ concat (Map.elems (M.progInvariants program))
            ++ [clause | fn <- allFunctions, block <- Map.elems (M.fnBlocks fn), M.Ghost _ (M.GhostValidation clause) <- M.blockStatements block]

unsupportedCalls :: M.Program -> Maybe String
unsupportedCalls program
    | any badCall allCalls = Just "calls outside the subset (unknown or value callees, callees with no return, callees that reassign a parameter, recursive or forward calls, or size arguments that are not constants or size parameters)"
    | otherwise = Nothing
  where
    functions = M.progFunctions program
    allFunctions = M.progMain program : Map.elems functions
    definitionOrder = Map.fromList (zip targets [0 :: Int ..])
    targets =
        [ name
        | fn <- [M.progMain program]
        , block <- Map.elems (M.fnBlocks fn)
        , M.Ghost _ (M.GhostFunction name _ _) <- M.blockStatements block
        ]
    allCalls =
        [ (callerName, caller, name, args)
        | caller <- allFunctions
        , let callerName = M.fnName caller
        , block <- Map.elems (M.fnBlocks caller)
        , M.Call (M.Const (M.CFn name)) args _ _ <- [M.blockTerminator block]
        ]
    badCall (callerName, caller, name, args) = case Map.lookup name functions of
        Nothing -> True
        Just callee ->
            M.fnReturns callee == Nothing
                || length args /= length (M.fnParams callee)
                || any (parameterAssigned callee) (M.fnParams callee)
                || not (all validSizeArg (drop (length args - length (M.fnSizeParams callee)) args))
                || forwardCall callerName name
          where
            validSizeArg (M.Const (M.CInt _)) = True
            validSizeArg (M.Copy local) = local `elem` callerSizeParams
            validSizeArg _ = False
            callerSizeParams = drop (length (M.fnParams caller) - length (M.fnSizeParams caller)) (M.fnParams caller)
            forwardCall callerName' called = case (Map.lookup callerName' definitionOrder, Map.lookup called definitionOrder) of
                (Just callerIndex, Just calledIndex) -> calledIndex >= callerIndex
                _ -> callerName' /= "main" && Map.member callerName' functions
    parameterAssigned callee local =
        any (writes local) (concatMap M.blockStatements (Map.elems (M.fnBlocks callee)))
            || any (termWrites local . M.blockTerminator) (Map.elems (M.fnBlocks callee))
      where
        writes dest (M.Assign d _) = d == dest
        writes dest (M.Peek d _) = d == dest
        writes dest (M.Drop d) = d == dest
        writes _ _ = False
        termWrites dest (M.Call _ _ d _) = d == dest
        termWrites _ _ = False

unsupportedLoops :: M.Program -> Maybe String
unsupportedLoops program
    | any badLoop allLoops = Just "loop shapes outside the subset (only counting loops over an Int, with a boolean header and a supported invariant)"
    | otherwise = Nothing
  where
    allLoops =
        [ (fn, header, spec)
        | fn <- M.progMain program : Map.elems (M.progFunctions program)
        , (header, spec) <- Map.toList (M.specLoops (M.fnSpec fn))
        ]
    badLoop (fn, header, spec) = not supportedTermination || not supportedHeader || not supportedUpper || not headerCompare || compoundCondition || generatedForLoop
      where
        supportedTermination = case M.loopTermination spec of
            Just (Counting (Var _)) -> True
            Just (Counting (F (Val (VFunct _ _ _ (BuiltinFunct Minus) _)) [_, Var _])) -> True
            _ -> False
        supportedUpper = case M.loopTermination spec of
            Just (Counting (F (Val (VFunct _ _ _ (BuiltinFunct Minus) _)) [upper, Var _])) -> simpleUpper upper
            _ -> True
          where
            simpleUpper (Var _) = True
            simpleUpper (Val (VInt _)) = True
            simpleUpper _ = False
        supportedHeader = case Map.lookup header (M.fnBlocks fn) of
            Just block -> case M.blockTerminator block of
                M.SwitchBool (M.Copy _) _ _ -> True
                _ -> False
            Nothing -> True
        headerCompare = case Map.lookup header (M.fnBlocks fn) of
            Just (M.BasicBlock stmts (M.SwitchBool (M.Copy local) _ _)) ->
                any (\stmt -> case stmt of M.Assign dest (M.BinaryOp (M.Compare _) _ _) -> dest == local; _ -> False) stmts
            _ -> True
        compoundCondition = case Map.lookup header (M.fnBlocks fn) of
            Just (M.BasicBlock _ (M.SwitchBool _ yes no)) ->
                yes /= M.loopBody spec
                    || (case Map.lookup no (M.fnBlocks fn) of
                            Just (M.BasicBlock _ (M.SwitchBool _ t1 t2)) -> M.loopBody spec `elem` [t1, t2]
                            _ -> False)
            _ -> False
        generatedForLoop =
            any ("$" `isPrefixOf`) (Map.keys (M.loopEnv spec))
                || any (any ("$" `isPrefixOf`) . proofNames) (M.loopInvariant spec)
        proofNames (ProofAssert proof) = names proof
          where
            names (ATerm name) = [name]
            names (FApp f args) = names f ++ concatMap names args
            names (Forall name guards body) = [name] ++ concatMap names guards ++ names body
            names (BVar name) = [name]
            names (CTerm _) = []
        proofNames _ = []


unsupportedAssumed :: M.Program -> Maybe String
unsupportedAssumed program
    | any (\clause -> proofSupported clause && not (clauseTotal clause)) assumedClauses = Just "contracts or invariants that are assumed mention a partial operation (division, remainder, indexing, push, pop, first, last or array creation in a proof)"
    | otherwise = Nothing
  where
    functions = M.progFunctions program
    assumedClauses =
        concatMap (M.specRequires . M.fnSpec) (M.progMain program : Map.elems functions)
            ++ [clause | fn <- M.progMain program : Map.elems functions, block <- Map.elems (M.fnBlocks fn), M.Call (M.Const (M.CFn name)) _ _ _ <- [M.blockTerminator block], Just callee <- [Map.lookup name functions], clause <- M.specEnsures (M.fnSpec callee)]
            ++ concat (Map.elems (M.progInvariants program))
    clauseTotal (ProofAssert proof) = case proof of
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel _)) _)) [a, b] -> totalOperand a && totalOperand b
        _ -> False
    clauseTotal _ = False
    totalOperand (ATerm _) = True
    totalOperand (CTerm (VInt n)) = inIntRange n
    totalOperand (CTerm (VBool _)) = True
    totalOperand (FApp (CTerm (VFunct _ _ _ (BuiltinFunct f) _)) args) = case (f, args) of
        (Size, [a]) -> totalOperand a
        (Field _ _, [a]) -> totalOperand a
        (Plus, [a, b]) -> totalOperand a && totalOperand b
        (Minus, [a, b]) -> totalOperand a && totalOperand b
        (Times, [a, b]) -> totalOperand a && totalOperand b
        _ -> False
    totalOperand _ = False

proofSupported :: ValidationStatement -> Bool
proofSupported (ProofAssert proof) = case proof of
    FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel _)) _)) [a, b] -> operandSupported a && operandSupported b
    _ -> False
proofSupported _ = False

operandSupported :: VariableProof -> Bool
operandSupported (ATerm _) = True
operandSupported (CTerm (VInt n)) = inIntRange n
operandSupported (CTerm (VBool _)) = True
operandSupported (FApp (ATerm "pop") [arg]) = operandSupported arg
operandSupported (FApp (CTerm (VFunct _ _ _ (BuiltinFunct f) _)) args) = case (f, args) of
    (Size, [a]) -> operandSupported a
    (Field _ _, [a]) -> operandSupported a
    (Get, [a, b]) -> operandSupported a && operandSupported b
    (Push, [a, b]) -> operandSupported a && operandSupported b
    (NewArray, [a, b]) -> operandSupported a && operandSupported b
    (Pop, [a]) -> operandSupported a
    (Set, [a, b, c]) -> operandSupported a && operandSupported b && operandSupported c
    (First, [a]) -> operandSupported a
    (Last, [a]) -> operandSupported a
    (Plus, [a, b]) -> operandSupported a && operandSupported b
    (Minus, [a, b]) -> operandSupported a && operandSupported b
    (Times, [a, b]) -> operandSupported a && operandSupported b
    (Div, [a, b]) -> operandSupported a && operandSupported b
    (Mod, [a, b]) -> operandSupported a && operandSupported b
    _ -> False
operandSupported _ = False

unsupportedReturn :: M.Program -> Maybe String
unsupportedReturn program
    | any functionBad allFunctions = Just "a return slot that is not assigned on every path to a return"
    | otherwise = Nothing
  where
    allFunctions = M.progMain program : Map.elems (M.progFunctions program)
    functionBad fn = case M.fnReturns fn of
        Nothing -> False
        Just _ -> any returnUnassigned (Map.toList blocks)
      where
        blocks = M.fnBlocks fn
        assigns0 (M.BasicBlock stmts term) =
            any (\stmt -> case stmt of M.Assign (M.Local 0) _ -> True; _ -> False) stmts
                || (case term of M.Call _ _ (M.Local 0) _ -> True; _ -> False)
        preds = Map.fromListWith (++) [(target, [source]) | (source, block) <- Map.toList blocks, target <- M.successors (M.blockTerminator block)]
        mustOut = fixpoint (Map.fromList [(blockId, blockId /= M.BlockId 0) | blockId <- Map.keys blocks])
          where
            fixpoint current
                | next == current = current
                | otherwise = fixpoint next
              where
                next = Map.mapWithKey step current
                step blockId _
                    | blockId == M.BlockId 0 = assigns0 (blocks Map.! blockId)
                    | otherwise =
                        let incoming = [Map.findWithDefault True p current | p <- Map.findWithDefault [] blockId preds]
                            mustIn = if null incoming then True else and incoming
                         in mustIn || assigns0 (blocks Map.! blockId)
        returnUnassigned (blockId, block) = case M.blockTerminator block of
            M.Return -> not (Map.findWithDefault True blockId mustOut)
            _ -> False
