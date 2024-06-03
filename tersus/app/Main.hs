module Main (main) where

import Parse

main :: IO ()
main = do
    -- let input = "assign x = 5"
    input <- getLine
    case parseStatementBlock input of
        Left err -> print err
        Right result -> putStrLn $ "Parsed result: " ++ show result
