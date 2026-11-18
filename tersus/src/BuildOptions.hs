module BuildOptions (describeBuildOptions) where

import Control.Exception (evaluate)
import Data.Char (isDigit)
import Data.List (isInfixOf, isPrefixOf, isSuffixOf, nub, sort, stripPrefix)
import qualified System.Directory as Directory
import System.FilePath ((</>))

import Hash (fingerprint)

-- What a build compiles with, as the command line GHC itself was given says
-- it: in an ordinary Cabal or Stack build that is the whole invocation of the
-- configured component, so the package's own options, what configuring
-- resolved and what the build command adds on top are all in it. The files
-- whose contents the description is bound to come back with it, for the
-- caller to depend on.
--
-- Where the build writes says nothing about what it writes, so an output
-- directory is only that. What it reads is not interchangeable, and each read
-- is bound to the authority it comes with:
--
--   * a directory whose source the caller already captures and compares
--     (`captured`, given as directories of the package) by its place there,
--     which is what that capture is of, listings included;
--   * an output directory of this build's own, and a directory under one, by
--     the modules and headers the build generates there (not by the objects
--     and interfaces it compiles into the same place), so a generated input
--     that changes under the same name is another build;
--   * a package database, and the compiler's own directory, by the records
--     of the packages they hold, which carry their ABI and configuration and
--     name where they were installed, so a description holds for one
--     installation and not for another;
--   * a package environment and a CPP header by what they contain.
--
-- A read of anything else -- another tree's source, an outside include or
-- library directory, an in-tree directory nothing binds -- is not something
-- this can describe, and neither is an invocation that is not an ordinary
-- build of a configured package. Then there is no description at all.
describeBuildOptions :: FilePath -> [FilePath] -> String -> [String] -> IO (Maybe ([String], [FilePath]))
describeBuildOptions root captured compiled arguments
    | not ("ghc" `isPrefixOf` compiled) || "iserv" `isInfixOf` compiled = pure Nothing
    | any (`elem` arguments) interpreted = pure Nothing
    | not (all (`elem` arguments) configured) = pure Nothing
    | otherwise = do
        treePath <- Directory.canonicalizePath root
        sourceDirs <- mapM (Directory.canonicalizePath . (root </>)) (nub captured)
        outputDirs <- mapM Directory.canonicalizePath (nub (values written arguments))
        described <- describe (Reads treePath sourceDirs outputDirs) arguments
        pure (fmap (\(shown, bound) -> ("tersus-observed-build 1" : shown, bound)) described)
  where
    -- (a splice elaborated outside this compilation, or no compilation of a package at all, is another build than this one)
    interpreted = ["--interactive", "--frontend", "--run", "-e", "-x", "-fexternal-interpreter"]
    -- (what Cabal, and Stack through it, gives GHC for a configured component)
    configured = ["--make", "-fbuilding-cabal-package", "-this-unit-id"]

data Reads = Reads
    { tree :: FilePath
    , sources :: [FilePath]
    , outputs :: [FilePath]
    }

-- Where this build writes: its own, and not part of what it makes
written :: [String]
written = ["-odir", "-hidir", "-stubdir", "-outputdir", "-hiedir", "-dumpdir", "-tmpdir", "-hpcdir", "-o"]

-- Where it looks for modules and headers
searched :: [String]
searched = ["-i", "-I"]

-- What GHC can read from a directory it searches
readable :: [String]
readable = [".hs", ".lhs", ".hsc", ".hs-boot", ".hsig", ".h"]

values :: [String] -> [String] -> [String]
values options arguments = [value | (option, value) <- zip arguments (drop 1 arguments), option `elem` options]

describe :: Reads -> [String] -> IO (Maybe ([String], [FilePath]))
describe _ [] = pure (Just ([], []))
describe inputs (argument : rest)
    -- (how many modules a build compiles at a time is not how it compiles them)
    | Just count <- stripPrefix "-j" argument, all isDigit count = continue [] [] rest
    | argument `elem` written = withValue (\_ more -> continue [argument, "<output>"] [] more)
    | argument `elem` ["-package-db", "-package-conf"] =
        withValue (\value more -> bound (registered value) (\shown files -> continue [argument, shown] files more))
    | argument == "-package-env" =
        withValue (\value more -> bound (held value) (\shown files -> continue [argument, shown] files more))
    | Just (option, value) <- glued searched argument =
        bound (searchedPath inputs value) (\shown files -> continue [option ++ shown] files rest)
    | Just directory <- stripPrefix "-B" argument, not (null directory) =
        bound (registered (directory </> "package.conf.d")) (\shown files -> continue ["-B" ++ shown] files rest)
    | Just header <- stripPrefix "-optP" argument, not ("-" `isPrefixOf` header) =
        bound (held header) (\shown files -> continue ["-optP" ++ shown] files rest)
    | '/' `notElem` argument = continue [argument] [] rest
    | otherwise = pure Nothing
  where
    withValue use = case rest of
        value : more -> use value more
        [] -> pure Nothing
    bound description use = do
        described <- description
        maybe (pure Nothing) (uncurry use) described
    continue shown files more = fmap (fmap (\(rest', files') -> (shown ++ rest', files ++ files'))) (describe inputs more)

glued :: [String] -> String -> Maybe (String, String)
glued options argument = case [(option, value) | option <- options,
        Just value <- [stripPrefix option argument], not (null value)] of
    found : _ -> Just found
    [] -> Nothing

-- A directory this build reads modules or headers from, bound to what makes
-- it the input it is, or to nothing at all
searchedPath :: Reads -> FilePath -> IO (Maybe (String, [FilePath]))
searchedPath inputs value = do
    path <- Directory.canonicalizePath value
    case [directory | directory <- outputs inputs, directory `covers` path] of
        directory : _ -> generated directory path
        [] | path `elem` sources inputs ->
                pure (Just ("<source " ++ maybe path id (stripPrefix (tree inputs ++ "/") path) ++ ">", []))
           | otherwise -> pure Nothing
  where
    covers directory path = directory == path || (directory ++ "/") `isPrefixOf` path

-- A directory the build generates, by what GHC can read from it: the modules
-- and headers it writes there (hsc2hs writes them at the root of the output
-- directory, Cabal the rest under it), and not the object and interface
-- files it compiles into the same place.
generated :: FilePath -> FilePath -> IO (Maybe (String, [FilePath]))
generated output directory = do
    present <- Directory.doesDirectoryExist directory
    entries <- if present then Directory.listDirectory directory else pure []
    let names = sort [entry | entry <- entries, any (`isSuffixOf` entry) readable]
        place = maybe "." id (stripPrefix (output ++ "/") directory)
    contents <- mapM (strictly . (directory </>)) names
    pure (Just ("<generated " ++ place ++ " " ++ fingerprint (concat (zipWith (\name text -> [name, text]) names contents)) ++ ">",
        map (directory </>) names))

-- A package database, by the records of the packages it holds: their ABI,
-- their configuration and where they were installed
registered :: FilePath -> IO (Maybe (String, [FilePath]))
registered directory = do
    present <- Directory.doesDirectoryExist directory
    file <- Directory.doesFileExist directory
    case (present, file) of
        (True, _) -> do
            entries <- Directory.listDirectory directory
            let records = sort [entry | entry <- entries, ".conf" `isSuffixOf` entry]
            contents <- mapM (strictly . (directory </>)) records
            pure (Just ("<packages " ++ fingerprint (concat (zipWith (\name text -> [name, text]) records contents)) ++ ">", []))
        (_, True) -> held directory
        _ -> pure Nothing

-- A file, by what it holds
held :: FilePath -> IO (Maybe (String, [FilePath]))
held path = do
    present <- Directory.doesFileExist path
    if not present then pure Nothing else do
        contents <- strictly path
        pure (Just ("<contents " ++ fingerprint [contents] ++ ">", [path]))

strictly :: FilePath -> IO String
strictly path = do
    contents <- readFile path
    _ <- evaluate (length contents)
    pure contents
