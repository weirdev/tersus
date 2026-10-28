module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM)
import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import System.FilePath ((</>))
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdout)
import System.Timeout (timeout)

import qualified Mir as M
import MirLower (lowerElaborated)
import qualified MirValidate as Reference
import Pipeline (compileSource, parseSource)
import SelfHostedMir (validateMirSubset)
import TypeCheck (elaborate)
import Utils (Result (..), bindResult)

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    source <- readFile "lib/validation.tersus"
    case compileSource source of
        Error e -> putStrLn ("CHECKER ERROR: " ++ e)
        Ok checker -> do
            files <- sort . filter (".tersus" `isSuffixOf`) <$> listDirectory "examples"
            results <- forM files $ \file -> do
                putStrLn ("BEGIN " ++ file)
                text <- readFile ("examples" </> file)
                outcome <- timeout 10000000 (evaluate (run checker text))
                let result = maybe TimedOut id outcome
                putStrLn (file ++ ": " ++ describe result)
                pure (file, result)
            let outcomes = map snd results
                count p = length (filter p outcomes)
            putStrLn ""
            putStrLn ("total " ++ show (length outcomes)
                ++ ", agree-accept " ++ show (count isAccept)
                ++ ", agree-reject " ++ show (count isReject)
                ++ ", mismatch " ++ show (count isMismatch)
                ++ ", unsupported " ++ show (count isUnsupported)
                ++ ", timed out " ++ show (count isTimedOut)
                ++ ", not-mir " ++ show (count isNotMir))

data Outcome
    = NotMir String
    | AgreeAccept
    | AgreeReject
    | Mismatch String
    | Unsupported
    | TimedOut

describe :: Outcome -> String
describe (NotMir e) = "not MIR (" ++ take 60 e ++ ")"
describe AgreeAccept = "accept"
describe AgreeReject = "reject"
describe (Mismatch e) = "MISMATCH " ++ e
describe Unsupported = "unsupported"
describe TimedOut = "TIMEOUT"

isAccept :: Outcome -> Bool
isAccept AgreeAccept = True
isAccept _ = False

isReject :: Outcome -> Bool
isReject AgreeReject = True
isReject _ = False

isMismatch :: Outcome -> Bool
isMismatch (Mismatch _) = True
isMismatch _ = False

isUnsupported :: Outcome -> Bool
isUnsupported Unsupported = True
isUnsupported _ = False

isTimedOut :: Outcome -> Bool
isTimedOut TimedOut = True
isTimedOut _ = False

isNotMir :: Outcome -> Bool
isNotMir (NotMir _) = True
isNotMir _ = False

run :: M.Program -> String -> Outcome
run checker text =
    case parseSource text `bindResult` elaborate `bindResult` lowerElaborated of
        Error e -> NotMir e
        Ok mir -> case (Reference.validateProgram mir, validateMirSubset checker mir) of
            (Ok _, Ok (Just True)) -> AgreeAccept
            (Error _, Ok (Just False)) -> AgreeReject
            (Ok _, Ok (Just False)) -> Mismatch "reference accepts, self-hosted rejects"
            (Error e, Ok (Just True)) -> Mismatch ("reference rejects, self-hosted accepts: " ++ take 80 e)
            (_, Ok Nothing) -> Unsupported
            (_, Error e) -> Mismatch ("self-hosted error: " ++ take 80 e)
