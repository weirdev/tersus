{-# OPTIONS_GHC -fno-full-laziness -fno-cse #-}
-- The feasibility spike for moving elaboration into Tersus (REPLACING_HASKELL.md, "Feasibility spike: findings").
-- Not part of the compiler: it builds the spike elaborator in dev/frontend-spike/elaborate/ and compares it
-- with TypeCheck.elaborateWith over single-file programs. (Full laziness is off so that a repeated timing
-- elaborates again instead of reusing the first result.)
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM, forM_, when)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, sort)
import GHC.Clock (getMonotonicTime)
import System.Directory (XdgDirectory (..), copyFileWithMetadata, createDirectoryIfMissing, doesFileExist, getTemporaryDirectory, getXdgDirectory, listDirectory)
import System.Environment (getArgs, setEnv)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath ((</>))
import System.IO (IOMode (..), hPutStrLn, stderr, withFile)
import System.Process (CreateProcess (..), StdStream (..), createProcess, proc, waitForProcess)
import Text.Printf (printf)

import qualified AstData as A
import Bootstrap (llvmOfOwned)
import Interface (ModuleInterface, mergeInterfacesImportEnv, withoutDeclaredNames)
import LibPackage (libModuleOfDisplay, libPackage, libSelectionFor)
import MirLower (lowerModuleWith)
import Modules (LoadResult (..))
import qualified Modules
import Native (buildExecutable, runWithInputFull)
import Pipeline (assumptionsOfPackage, compileModules, compileModulesBootstrap, compileModulesValidated, loadFromEntry, ownedModuleProgram)
import PreludeSource (toolPackageFiles)
import SourceParse (declaredNames, definedFunctionNames)
import Syntax
import TersusParser (parseSourceParts)
import TypeCheck (ImportEnv, elaborateWith)
import Utils

spikeDir :: FilePath
spikeDir = "dev/frontend-spike/elaborate"

-- The spike is mounted as the module elaborate::spike of a package beside lib/data, which it imports: a package
-- imports only its siblings, and lib/data is not one of dev/'s.
spikeEntry :: FilePath
spikeEntry = "lib/elaborate/spike/elaborate.tersus"

main :: IO ()
main = getArgs >>= \args -> case args of
    ["dump", file, prefix] -> dump file prefix
    ["build", output] -> build output
    ["ir", output] -> spikeIr >>= writeFile output
    ["build-ir", input, output] -> readFile input >>= buildExecutable output >>= orFail ("built " ++ output)
    ["validate"] -> validate False
    ["validate", "--cold"] -> validate True
    ("compare" : "--runs" : n : exe : files) | [(runs, "")] <- reads n, runs > 0 -> compareAll runs exe files
    ("compare" : exe : files) -> compareAll 1 exe files
    _ -> failWith usage
  where
    usage = "usage: frontend-spike (dump FILE PREFIX | build EXE | ir OUT.ll | build-ir IN.ll EXE | validate [--cold] | compare [--runs N] EXE FILE...)"

data Prepared = Prepared
    { prRequest :: String
    , prEnv :: ImportEnv
    , prIfaces :: [ModuleInterface]
    , prStatements :: [Statement]
    }

-- A single-file program as Compile.lowerSourceParts elaborates it: its own statements, and the interfaces of
-- the libraries it selects
prepare :: String -> Result Prepared String
prepare source =
    parseSourceParts True source `bindResult` \(names, _library, stmts) ->
        libPackage `bindResult` \pkg ->
            let selected = [name | display <- names, Just name <- [libModuleOfDisplay display]]
             in case libSelectionFor pkg selected stmts of
                    Left err -> Error err
                    Right (selectedIfaces, _) ->
                        let own = concatMap declaredNames stmts ++ concatMap definedFunctionNames stmts
                            ifaces = map (withoutDeclaredNames own) selectedIfaces
                         in A.writeParsed stmts `bindResult` \request ->
                                Ok (Prepared request (mergeInterfacesImportEnv ifaces) ifaces stmts)

haskellElaborated :: Prepared -> Result (Elaborated, String) String
haskellElaborated p =
    elaborateWith (prEnv p) (prStatements p) `bindResult` \(elaborated, _) ->
        A.writeElaborated elaborated `bindResult` \text -> Ok (elaborated, text)

dump :: FilePath -> FilePath -> IO ()
dump file prefix = do
    source <- readFile file
    case prepare source of
        Error e -> failWith e
        Ok p -> do
            writeFile (prefix ++ ".request.ast") (prRequest p)
            case haskellElaborated p of
                Error e -> putStrLn ("haskell refuses: " ++ e)
                Ok (_, text) -> writeFile (prefix ++ ".haskell.ast") text

spikeFiles :: IO [(FilePath, String)]
spikeFiles = do
    names <- sort . filter (".tersus" `isSuffixOf`) <$> listDirectory spikeDir
    own <- forM names $ \name -> do
        text <- readFile (spikeDir </> name)
        _ <- evaluate (length text)
        pure ("lib/elaborate/spike/" ++ name, text)
    pure (("lib/elaborate/package.tersus", "") : own ++ [f | f@(path, _) <- toolPackageFiles, "lib/data/" `isPrefixOf` path])

loadSpike :: IO Modules.LoadedPackage
loadSpike = do
    files <- spikeFiles
    case loadFromEntry (Modules.resolverFromFiles files) spikeEntry of
        Right (PackageResult pkg) -> pure pkg
        Right _ -> failWith "the spike is not a package"
        Left e -> failWith e

-- The LLVM IR of the spike as the host builds its own programs: linked and erased, not validated, owned and
-- emitted by the production emitter. It is the shape a frontend seed (F0) would take.
spikeIr :: IO String
spikeIr = do
    pkg <- loadSpike
    case compileModulesBootstrap pkg `bindResult` ownedModuleProgram of
        Error e -> failWith e
        Ok owned -> llvmOfOwned owned >>= \ir -> case ir of
            Error e -> failWith e
            Ok text -> pure text

build :: FilePath -> IO ()
build output = spikeIr >>= buildExecutable output >>= orFail ("built " ++ output)

orFail :: String -> Result () String -> IO ()
orFail done r = case r of
    Error e -> failWith e
    Ok () -> putStrLn done

-- Validated by the production validator, which checks one function at a time and keeps each verdict in the
-- cache. --cold runs it with a copy of the cache that has the built tools and no verdicts, so every function
-- is checked.
validate :: Bool -> IO ()
validate cold = do
    verdicts <- if cold then coldCache else pure Nothing
    pkg <- loadSpike
    start <- getMonotonicTime
    outcome <- evaluate (case compileModulesValidated pkg of Ok _ -> Nothing; Error e -> Just e)
    end <- getMonotonicTime
    printf "validation %s in %.1fs\n" (maybe "passed" (const "FAILED") outcome) (end - start)
    forM_ verdicts $ \dir -> do
        made <- concat <$> (listDirectory dir >>= mapM (\sub -> if "verdicts-" `isPrefixOf` sub then listDirectory (dir </> sub) else pure []))
        printf "function verdicts made: %d\n" (length (filter (not . (".lock" `isSuffixOf`)) made))
    case compileModules pkg of
        Error e -> putStrLn ("assumptions: " ++ e)
        Ok compiled -> putStrLn ("assumptions: " ++ show (assumptionsOfPackage compiled))
    mapM_ failWith outcome

coldCache :: IO (Maybe FilePath)
coldCache = do
    cache <- getXdgDirectory XdgCache "tersus"
    temp <- getTemporaryDirectory
    stamp <- getMonotonicTime
    let root = temp </> ("frontend-spike-cold-" ++ show (round (stamp * 1000) :: Integer))
        copy = root </> "tersus"
    createDirectoryIfMissing True copy
    entries <- listDirectory cache
    forM_ entries $ \entry -> do
        isFile <- doesFileExist (cache </> entry)
        when (isFile && not ("verdicts-" `isPrefixOf` entry)) $ copyFileWithMetadata (cache </> entry) (copy </> entry)
    setEnv "XDG_CACHE_HOME" root
    pure (Just copy)

data Outcome = Agree | Disagree String | NotModelled String | NotParsed String | BothRefuse String String | CandidateFails String

-- Times: Haskell's elaboration and writing of the data, in-process; the spike run through the host (request
-- piped in, reply read back as a String, as a host adapter would); and the spike alone (request from a file,
-- reply to /dev/null)
data Measured = Measured {mOutcome :: Outcome, mHaskell :: Double, mTersus :: Double, mNative :: Double}

compareAll :: Int -> FilePath -> [FilePath] -> IO ()
compareAll runs exe files = do
    starts <- forM [1 .. 20 :: Int] $ \_ -> timed (runWithInputFull exe "")
    printf "process start and exit with empty input: median %.2fms of 20\n" (median (map snd starts) * 1000)
    -- (one elaboration first, untimed, so the checker's own tables are not counted against the first program)
    forM_ (take 1 files) $ \file -> readFile file >>= \source -> evaluate (warm (prepare source))
    results <- forM files $ \file -> do
        source <- readFile file
        m <- compareOne runs exe source
        printf "%-60s %-14s haskell %8.2fms  tersus %8.2fms  native %8.2fms\n" file (outcomeLabel (mOutcome m)) (mHaskell m * 1000) (mTersus m * 1000) (mNative m * 1000)
        case mOutcome m of
            Disagree why -> putStrLn ("  " ++ why)
            CandidateFails why -> putStrLn ("  " ++ why)
            NotModelled why -> putStrLn ("  " ++ why)
            NotParsed why -> putStrLn ("  " ++ why)
            BothRefuse haskell tersus | haskell /= tersus -> putStrLn ("  haskell: " ++ haskell ++ "\n  tersus:  " ++ tersus)
            _ -> pure ()
        pure m
    let count p = length (filter (p . mOutcome) results)
        agreeing = filter (isAgree . mOutcome) results
        th = sum (map mHaskell agreeing)
        tc = sum (map mTersus agreeing)
        tn = sum (map mNative agreeing)
    printf "agree %d, refused alike %d, refused differently %d, disagree %d, not modelled %d, not parsed %d, candidate failures %d\n"
        (length agreeing) (count sameRefusal) (count otherRefusal) (count isDisagree) (count isNotModelled) (count isNotParsed) (count isFailure)
    printf "agreeing programs (median of %d runs each): haskell %.1fms, tersus through the host %.1fms, tersus alone %.1fms\n" runs (th * 1000) (tc * 1000) (tn * 1000)
    when (count isDisagree + count isFailure + count otherRefusal > 0) $ exitWith (ExitFailure 1)
  where
    isAgree o = case o of Agree -> True; _ -> False
    isDisagree o = case o of Disagree _ -> True; _ -> False
    isNotModelled o = case o of NotModelled _ -> True; _ -> False
    isNotParsed o = case o of NotParsed _ -> True; _ -> False
    sameRefusal o = case o of BothRefuse a b -> a == b; _ -> False
    otherRefusal o = case o of BothRefuse a b -> a /= b; _ -> False
    isFailure o = case o of CandidateFails _ -> True; _ -> False

warm :: Result Prepared String -> Int
warm r = case r `bindResult` haskellElaborated of
    Ok (_, text) -> length text
    Error e -> length e

outcomeLabel :: Outcome -> String
outcomeLabel o = case o of
    Agree -> "agree"
    Disagree _ -> "DISAGREE"
    NotModelled _ -> "not-modelled"
    NotParsed _ -> "not-parsed"
    BothRefuse a b
        | a == b -> "refused-alike"
        | otherwise -> "REFUSED-OTHERWISE"
    CandidateFails _ -> "FAIL"

timed :: IO a -> IO (a, Double)
timed action = do
    t0 <- getMonotonicTime
    a <- action
    t1 <- getMonotonicTime
    pure (a, t1 - t0)

median :: [Double] -> Double
median [] = 0
median xs = sort xs !! (length xs `div` 2)

-- Elaborates again on every call (the run number keeps it from being shared)
haskellRun :: Prepared -> Int -> Result String String
haskellRun p run = case run `seq` haskellElaborated p of
    Ok (_, text) -> length text `seq` Ok text
    Error e -> length e `seq` Error e

compareOne :: Int -> FilePath -> String -> IO Measured
compareOne runs exe source = case prepare source of
    Error e -> pure (Measured (NotParsed (takeWhile (/= '\n') e)) 0 0 0)
    Ok p -> do
        -- (the request and the import environment are made first: the timing is of elaboration alone; each timed
        -- run's result is forced and dropped, so no run holds the results of the others)
        _ <- evaluate (length (prRequest p) + length (show (prEnv p)))
        requestFile <- (</> "frontend-spike-request.ast") <$> getTemporaryDirectory
        writeFile requestFile (prRequest p)
        nativeTimes <- forM [1 .. runs] $ \_ -> snd <$> timed (runAlone exe requestFile)
        hostTimes <- forM [1 .. runs] $ \_ -> snd <$> timed (runWithInputFull exe (prRequest p) >>= \(_, out, err) -> evaluate (length out + length err))
        haskellTimes <- forM [1 .. runs] $ \run -> snd <$> timed (evaluate (either length length (resultEither (haskellRun p run))))
        let haskell = haskellRun p 0
        (code, out, err) <- runWithInputFull exe (prRequest p)
        let measured o = Measured o (median haskellTimes) (median hostTimes) (median nativeTimes)
            firstLine = takeWhile (/= '\n')
        pure $ measured $ case (code, haskell) of
            (ExitSuccess, Error refusal)
                | "tersus-ast 1 elaborated" `isPrefixOf` out -> Disagree ("Haskell refuses (" ++ refusal ++ "), the candidate accepts")
                | "not modelled" `isInfixOf` err -> NotModelled (firstLine err)
                | otherwise -> BothRefuse refusal (firstLine err)
            (ExitSuccess, Ok expected)
                | stripResult out == expected -> case A.readElaborated (stripResult out) of
                    Error e -> CandidateFails ("readElaborated: " ++ e)
                    Ok elaborated -> case lowerModuleWith (prEnv p) (prIfaces p) elaborated of
                        Error e -> CandidateFails ("lowering: " ++ e)
                        Ok _ -> Agree
                | "not modelled" `isInfixOf` err -> NotModelled (firstLine err)
                | otherwise -> Disagree (firstDifference expected (stripResult out) ++ (if null err then "" else " stderr: " ++ take 300 err))
            (failure, _) -> CandidateFails (show failure ++ " " ++ take 300 err)

resultEither :: Result a String -> Either String a
resultEither r = case r of
    Ok a -> Right a
    Error e -> Left e

runAlone :: FilePath -> FilePath -> IO ExitCode
runAlone exe requestFile =
    withFile requestFile ReadMode $ \input -> withFile "/dev/null" WriteMode $ \output -> do
        (_, _, _, process) <- createProcess (proc exe []){std_in = UseHandle input, std_out = UseHandle output, std_err = UseHandle output}
        waitForProcess process

-- The native runtime prints the value main returns after what the program wrote
stripResult :: String -> String
stripResult out = case reverse (lines out) of
    "0" : rest -> unlines (reverse rest)
    _ -> out

firstDifference :: String -> String -> String
firstDifference a b = go (1 :: Int) (lines a) (lines b)
  where
    go n (x : xs) (y : ys)
        | x == y = go (n + 1) xs ys
        | otherwise = "line " ++ show n ++ ": expected " ++ take 120 x ++ " | got " ++ take 120 y
    go n [] (y : _) = "line " ++ show n ++ ": extra " ++ take 120 y
    go n (x : _) [] = "line " ++ show n ++ ": missing " ++ take 120 x
    go _ [] [] = "identical"

failWith :: String -> IO a
failWith e = hPutStrLn stderr e >> exitWith (ExitFailure 1)
