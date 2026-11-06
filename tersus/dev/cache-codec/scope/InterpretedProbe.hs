module Main (main) where
import TestHarness (sharedProgramCacheFile)
main :: IO ()
main = do
    file <- sharedProgramCacheFile "binary-probe" "return 314159;"
    print file
    if file == Nothing then pure () else error "interpreted execution must not use the compiled-program cache"
