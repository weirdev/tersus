-- The elaborator's request and response (AST_DATA.md, "Elaboration requests"): what a host gives an
-- elaborator to elaborate one module, and what it gets back (ElaboratorTool runs the elaborator written in Tersus).
module ElaborateRequest
    ( Elaborator
    , Extraction (..)
    , Request (..)
    , Library (..)
    , Package (..)
    , PackageFile (..)
    , FileImport (..)
    , Response (..)
    , writeRequest
    , readRequest
    , writeResponse
    , readResponse
    , readResponseLines
    , readResponseBytes
    , acceptedElaboration
    , requestHeader
    , responseHeader
    ) where

import qualified Data.ByteString.Char8 as B
import qualified Data.Map as Map

import AstData (readElaboratedBytes, readElaboratedLines, readParsedLines, writeElaboratedLines, writeParsedLines)
import BuiltinTable (builtinTableLines)
import DataCodec (Token (..), quote, strictTokenize)
import Interface (ModuleInterface (..))
import InterfaceData (readInterfaceBytes, readInterfaceLines, writeInterfaceLines)
import Modules (Declaration (..), DeclarationKind (..), ImportLevel (..), ModuleId (..))
import Syntax (Elaborated (..), Statement)
import Utils

-- Which interface to return: ordinary modules share one template export policy;
-- compiler-library extraction additionally retains physical constructor views.
data Extraction = NoInterface | ModuleInterfaceOf | LibInterfaceOf
    deriving (Show, Eq)

-- The module, whether it predeclares its own types (a package module does), whether it is a module of the
-- compiler libraries (which see a generic struct's constructor as the struct it builds), the interface to
-- give back, the interfaces of the modules it imports, checked defining dependencies, the compiler libraries it
-- may be given (the elaborator selects among them), the package its names are resolved in, the statements
-- as read: one list for each of the module's files in the package's order, or one for a program, and how many of
-- the program's first statements are compiler libraries put in front of it, whose functions with bounds were checked
-- against their bounds where the libraries were (written `builtins checked N`, only when N is not 0, so a request
-- that has none reads as before).
data Request = Request
    { rqModule :: ModuleId
    , rqPredeclare :: Bool
    , rqLibrary :: Bool
    , rqExtraction :: Extraction
    , rqInterfaces :: [ModuleInterface]
    , rqDefinitions :: [[ModuleInterface]]
    , rqLibraries :: [Library]
    , rqPackage :: Maybe Package
    , rqStatements :: [[Statement]]
    , rqCheckedStatements :: Int
    }
    deriving (Show, Eq)

data Library = Library
    { libraryName :: String
    , libraryImports :: [String]
    , libraryInterface :: ModuleInterface
    }
    deriving (Show, Eq)

data Package = Package
    { packageEntry :: ModuleId
    , packageFiles :: [PackageFile]
    }
    deriving (Show, Eq)

data PackageFile = PackageFile
    { fileModule :: ModuleId
    , fileStem :: String
    , fileName :: String
    , fileDeclarations :: [Declaration]
    , fileImports :: [FileImport]
    }
    deriving (Show, Eq)

-- A resolved import (Modules.ResolvedImport) as resolution reads it
data FileImport = FileImport
    { importLevel :: ImportLevel
    , importTarget :: ModuleId
    , importFile :: Maybe String
    , importSymbol :: Maybe String
    , importAs :: Maybe String
    , importOnly :: Maybe [String]
    }
    deriving (Show, Eq)

data Response
    = -- with the compiler libraries the elaborator selected for the module
      Accepted Elaborated (Maybe ModuleInterface) [String]
    | -- the module does not check
      Refused String
    | -- it checks, but its interface cannot be given (Interface.extractInterface)
      RefusedInterface String
    | -- its names do not resolve, or the libraries it calls for cannot be given it; the message is whole
      Unresolved String
    | -- the elaborator does not handle the program yet, which is not a verdict on it
      NotModelled String
    deriving (Show)

type Elaborator = Request -> Response

writeRequest :: Request -> Result String String
writeRequest rq =
    syntax `bindResult` \() ->
    builtinTableLines `bindResult` \builtins ->
    mapAll linesOf (rqInterfaces rq) `bindResult` \ifaces ->
        mapAll writeDefinition (rqDefinitions rq) `bindResult` \definitions ->
        mapAll writeLibrary (rqLibraries rq) `bindResult` \libraries ->
        mapAll writeParsedLines (rqStatements rq) `bindResult` \asts ->
            Ok $
                unlines
                    ( [ requestHeader
                      , unwords ["module", quote pkg, maybe "none" quote modu]
                      , "predeclare " ++ boolWord (rqPredeclare rq)
                      , "library " ++ boolWord (rqLibrary rq)
                      , "extract " ++ extractionWord (rqExtraction rq)
                      , "builtins" ++ (if rqCheckedStatements rq > 0 then " checked " ++ show (rqCheckedStatements rq) else "")
                      ]
                        ++ block builtins
                        ++ ["interfaces " ++ show (length ifaces)]
                        ++ concatMap block ifaces
                        ++ ["definitions " ++ show (length definitions)]
                        ++ concat definitions
                        ++ (if null libraries then [] else ("libraries " ++ show (length libraries)) : concat libraries)
                        ++ maybe [] packageLines (rqPackage rq)
                        ++ concatMap block asts
                    )
  where
    syntax
        | null (rqStatements rq) || length (rqStatements rq) /= syntaxBlocks (rqModule rq) (rqPackage rq) = Error "ElaborateRequest: the syntax is not one block per file of the module"
        | otherwise = Ok ()
    writeDefinition [] = Error "ElaborateRequest: empty defining context"
    writeDefinition context = mapAll linesOf context `bindResult` \texts -> Ok (("definition " ++ show (length texts)) : concatMap block texts)
    writeLibrary (Library name imports iface) = linesOf iface `bindResult` \text -> Ok (unwords (["library", quote name, show (length imports)] ++ map quote imports) : block text)
    -- (a defining context repeats the interfaces of the modules it depends on, so each is written once)
    written = Map.fromList [(ifModule i, (i, writeInterfaceLines i)) | i <- rqInterfaces rq ++ concat (rqDefinitions rq) ++ map libraryInterface (rqLibraries rq)]
    linesOf iface = case Map.lookup (ifModule iface) written of
        Just (known, ls) | known == iface -> ls
        _ -> writeInterfaceLines iface
    ModuleId pkg modu = rqModule rq

syntaxBlocks :: ModuleId -> Maybe Package -> Int
syntaxBlocks modu = maybe 1 (\package -> length [f | f <- packageFiles package, fileModule f == modu])

packageLines :: Package -> [String]
packageLines (Package entry files) = unwords (["package"] ++ moduleWords entry ++ [show (length files)]) : concatMap fileLines files
  where
    fileLines (PackageFile modu stem name decls imports) =
        unwords (["file"] ++ moduleWords modu ++ [quote stem, quote name, show (length decls), show (length imports)])
            : map declLine decls ++ map importLine imports
    declLine (Declaration kind name functions) = unwords (["decl", kindWord kind, quote name, show (length functions)] ++ map quote functions)
    importLine (FileImport level target file symbol alias names) =
        unwords (["import", levelWord level] ++ moduleWords target ++ map optional [file, symbol, alias] ++ maybe ["none"] (\ns -> show (length ns) : map quote ns) names)
    optional = maybe "none" quote

moduleWords :: ModuleId -> [String]
moduleWords (ModuleId pkg modu) = [quote pkg, maybe "none" quote modu]

kindWord :: DeclarationKind -> String
kindWord kind = case kind of
    DeclaresType -> "type"
    DeclaresVariant -> "variant"
    DeclaresTrait -> "trait"
    DeclaresFunction -> "function"
    DeclaresAxiom -> "axiom"
    DeclaresProof -> "proof"

levelWord :: ImportLevel -> String
levelWord level = case level of
    LevelModule -> "module"
    LevelFile -> "file"
    LevelSymbol -> "symbol"

readRequest :: String -> Result Request String
readRequest text = case lines text of
    "tersus-elaborate 1" : moduleLine : predeclareLine : libraryLine : extractLine : builtinsLine : afterBuiltins ->
        checkedOf builtinsLine `bindResult` \checked ->
        moduleOf moduleLine `bindResult` \modu ->
        wordAfter "predeclare" predeclareLine `bindResult` \predeclare ->
        boolOf predeclare `bindResult` \flag ->
        wordAfter "library" libraryLine `bindResult` \library ->
        boolOf library `bindResult` \libraryFlag ->
        wordAfter "extract" extractLine `bindResult` \extract ->
        extractionOf extract `bindResult` \extraction ->
        blocks 1 afterBuiltins `bindResult` \(builtinTexts, afterTable) ->
        builtinTableLines `bindResult` \table ->
        (if builtinTexts == [table] then Ok () else Error "ElaborateRequest: the request's builtin table is not this compiler's") `bindResult` \() ->
        firstLine afterTable `bindResult` \(countLine, rest) ->
        wordAfter "interfaces" countLine `bindResult` \countText ->
        countOf countText `bindResult` \count ->
        blocks count rest `bindResult` \(ifaceTexts, rest') ->
        mapAll readInterfaceLines ifaceTexts `bindResult` \ifaces ->
        definitionBlocks rest' `bindResult` \(definitionTexts, afterDefinitions) ->
        mapAll (mapAll readInterfaceLines) definitionTexts `bindResult` \definitions ->
        libraryBlocks afterDefinitions `bindResult` \(libraries, afterLibraries) ->
        packageOf afterLibraries `bindResult` \(package, syntax) ->
        blocks (syntaxBlocks modu package) syntax `bindResult` \(astTexts, rest'') ->
            if not (null rest'')
                then Error "ElaborateRequest: records after the module's syntax"
                else if null astTexts then Error "ElaborateRequest: no syntax"
                else mapAll readParsedLines astTexts `bindResult` \stmts -> Ok (Request modu flag libraryFlag extraction ifaces definitions libraries package stmts checked)
    _ -> Error "ElaborateRequest: not an elaboration request"
  where
    definitionBlocks (line : rest) = wordAfter "definitions" line `bindResult` countOf `bindResult` \count -> contexts count rest
    definitionBlocks [] = Error "ElaborateRequest: missing defining interfaces"
    contexts 0 rest = Ok ([], rest)
    contexts n (line : rest) = wordAfter "definition" line `bindResult` countOf `bindResult` \count ->
        if count == 0 then Error "ElaborateRequest: empty defining context" else
        blocks count rest `bindResult` \(context, remaining) -> contexts (n - 1) remaining `bindResult` \(more, syntax) -> Ok (context : more, syntax)
    contexts _ [] = Error "ElaborateRequest: missing defining context"
    checkedOf line = case words line of
        ["builtins"] | line == "builtins" -> Ok 0
        ["builtins", "checked", count] | line == unwords ["builtins", "checked", count] -> countOf count `bindResult` \n ->
            if n > 0 then Ok n else Error "ElaborateRequest: a checked count of 0 is not written"
        _ -> Error "ElaborateRequest: expected builtins"
    moduleOf line = strictTokenize line `bindResult` \ts -> case ts of
        [Word "module", Str pkg, Word "none"] -> Ok (ModuleId pkg Nothing)
        [Word "module", Str pkg, Str modu] -> Ok (ModuleId pkg (Just modu))
        _ -> Error "ElaborateRequest: malformed module"
    libraryBlocks (line : rest) | take 10 line == "libraries " = wordAfter "libraries" line `bindResult` countOf `bindResult` \count ->
        if count == 0 then Error "ElaborateRequest: an empty library catalog is written as none" else libraryEntries count rest
    libraryBlocks ls = Ok ([], ls)
    libraryEntries 0 rest = Ok ([], rest)
    libraryEntries n (line : rest) = strictTokenize line `bindResult` \ts -> case ts of
        Word "library" : Str name : Word count : imports
            | Ok k <- countOf count, length imports == k, Just names <- mapM strOf imports ->
                blocks 1 rest `bindResult` \(texts, remaining) -> case texts of
                    [text] -> readInterfaceLines text `bindResult` \iface ->
                        libraryEntries (n - 1) remaining `bindResult` \(more, after) -> Ok (Library name names iface : more, after)
                    _ -> Error "ElaborateRequest: malformed library"
        _ -> Error "ElaborateRequest: malformed library"
    libraryEntries _ [] = Error "ElaborateRequest: missing library"
    packageOf (line : rest) | take 8 line == "package " = strictTokenize line `bindResult` \ts -> case ts of
        [Word "package", p, m, Word count] | Ok entry <- moduleIdOf p m, Ok n <- countOf count ->
            packageFilesOf n rest `bindResult` \(files, after) -> Ok (Just (Package entry files), after)
        _ -> Error "ElaborateRequest: malformed package"
    packageOf ls = Ok (Nothing, ls)
    packageFilesOf 0 rest = Ok ([], rest)
    packageFilesOf n (line : rest) = strictTokenize line `bindResult` \ts -> case ts of
        [Word "file", p, m, Str stem, Str name, Word declCount, Word importCount]
            | Ok modu <- moduleIdOf p m, Ok d <- countOf declCount, Ok i <- countOf importCount, length rest >= d + i ->
                mapAll declOf (take d rest) `bindResult` \decls ->
                mapAll importOf (take i (drop d rest)) `bindResult` \imports ->
                packageFilesOf (n - 1) (drop (d + i) rest) `bindResult` \(more, after) -> Ok (PackageFile modu stem name decls imports : more, after)
        _ -> Error "ElaborateRequest: malformed package file"
    packageFilesOf _ [] = Error "ElaborateRequest: missing package file"
    declOf line = strictTokenize line `bindResult` \ts -> case ts of
        Word "decl" : Word kind : Str name : Word count : functions
            | Just k <- lookup kind [(kindWord d, d) | d <- [minBound ..]], Ok n <- countOf count, length functions == n, Just fs <- mapM strOf functions -> Ok (Declaration k name fs)
        _ -> Error "ElaborateRequest: malformed declaration"
    importOf line = strictTokenize line `bindResult` \ts -> case ts of
        Word "import" : Word level : p : m : file : symbol : alias : names
            | Just l <- lookup level [(levelWord v, v) | v <- [minBound ..]], Ok target <- moduleIdOf p m, Just f <- optionalOf file, Just s <- optionalOf symbol, Just a <- optionalOf alias, Just ns <- namesOf names ->
                Ok (FileImport l target f s a ns)
        _ -> Error "ElaborateRequest: malformed import"
    moduleIdOf (Str pkg) (Word "none") = Ok (ModuleId pkg Nothing)
    moduleIdOf (Str pkg) (Str modu) = Ok (ModuleId pkg (Just modu))
    moduleIdOf _ _ = Error "ElaborateRequest: malformed module"
    strOf (Str text) = Just text
    strOf _ = Nothing
    optionalOf (Word "none") = Just Nothing
    optionalOf (Str text) = Just (Just text)
    optionalOf _ = Nothing
    namesOf [Word "none"] = Just Nothing
    namesOf (Word count : names) | Ok n <- countOf count, length names == n = Just <$> mapM strOf names
    namesOf _ = Nothing
    boolOf w = case w of
        "true" -> Ok True
        "false" -> Ok False
        _ -> Error "ElaborateRequest: malformed flag"
    extractionOf w = case [e | e <- [NoInterface, ModuleInterfaceOf, LibInterfaceOf], extractionWord e == w] of
        [e] -> Ok e
        _ -> Error "ElaborateRequest: unknown extraction"

writeResponse :: Response -> Result String String
writeResponse response = case response of
    Accepted elaborated iface libraries ->
        writeElaboratedLines elaborated `bindResult` \ast ->
            maybe (Ok Nothing) (mapResult Just . writeInterfaceLines) iface `bindResult` \ifaceLines ->
                Ok (unlines ([responseHeader, "accepted"] ++ block ast ++ maybe ["interface none"] (\t -> "interface" : block t) ifaceLines ++ librariesLine libraries))
    Refused message -> Ok (unlines [responseHeader, "refused " ++ quote message])
    RefusedInterface message -> Ok (unlines [responseHeader, "interfaceRefused " ++ quote message])
    Unresolved message -> Ok (unlines [responseHeader, "unresolved " ++ quote message])
    NotModelled what -> Ok (unlines [responseHeader, "unmodelled " ++ quote what])

readResponse :: String -> Result Response String
readResponse = readResponseLines . lines

readResponseLines :: [String] -> Result Response String
readResponseLines = readResponseWith id readElaboratedLines readInterfaceLines

readResponseBytes :: [B.ByteString] -> Result Response String
readResponseBytes = readResponseWith B.unpack readElaboratedBytes readInterfaceBytes

readResponseWith :: (l -> String) -> ([l] -> Result Elaborated String) -> ([l] -> Result ModuleInterface String) -> [l] -> Result Response String
readResponseWith text elaborated interface ls = case map text (take 3 ls) of
    ["tersus-elaborated 1", line] -> strictTokenize line `bindResult` \ts -> case ts of
        [Word "refused", Str message] -> Ok (Refused message)
        [Word "interfaceRefused", Str message] -> Ok (RefusedInterface message)
        [Word "unresolved", Str message] -> Ok (Unresolved message)
        [Word "unmodelled", Str what] -> Ok (NotModelled what)
        _ -> Error "ElaborateRequest: malformed response"
    "tersus-elaborated 1" : "accepted" : _ ->
        blocksWith text 1 (drop 2 ls) `bindResult` \(astTexts, rest') -> case (astTexts, map text (take 1 rest')) of
            ([ast], ["interface none"]) -> librariesOf (map text (drop 1 rest')) `bindResult` \libraries -> elaborated ast `bindResult` \e -> Ok (Accepted e Nothing libraries)
            ([ast], ["interface"]) ->
                blocksWith text 1 (drop 1 rest') `bindResult` \(ifaceTexts, rest'') -> case ifaceTexts of
                    [ifaceText] -> librariesOf (map text rest'') `bindResult` \libraries -> elaborated ast `bindResult` \e -> interface ifaceText `bindResult` \i -> Ok (Accepted e (Just i) libraries)
                    _ -> Error "ElaborateRequest: malformed interface"
            _ -> Error "ElaborateRequest: malformed response"
    _ -> Error "ElaborateRequest: not an elaboration response"

-- `libraries N "NAME"...`, which ends an accepted response when the elaborator selected compiler libraries
librariesLine :: [String] -> [String]
librariesLine [] = []
librariesLine names = [unwords (["libraries", show (length names)] ++ map quote names)]

librariesOf :: [String] -> Result [String] String
librariesOf [] = Ok []
librariesOf [line] = strictTokenize line `bindResult` \ts -> case ts of
    Word "libraries" : Word count : names | Ok n <- countOf count, n > 0, length names == n, Just ns <- mapM str names -> Ok ns
    _ -> Error "ElaborateRequest: malformed libraries"
  where
    str (Str t) = Just t
    str _ = Nothing
librariesOf _ = Error "ElaborateRequest: malformed libraries"

-- What a single-file program needs of a response: the elaboration, or why there is none
acceptedElaboration :: Response -> Result Elaborated String
acceptedElaboration response = case response of
    Accepted e _ _ -> Ok e
    Refused message -> Error message
    RefusedInterface message -> Error message
    Unresolved message -> Error message
    NotModelled what -> Error ("the elaborator does not handle this program yet: " ++ what)

boolWord :: Bool -> String
boolWord b = if b then "true" else "false"

extractionWord :: Extraction -> String
extractionWord e = case e of
    NoInterface -> "none"
    ModuleInterfaceOf -> "module"
    LibInterfaceOf -> "lib"

wordAfter :: String -> String -> Result String String
wordAfter key line = case words line of
    [k, w] | k == key && line == key ++ " " ++ w -> Ok w
    _ -> Error ("ElaborateRequest: expected " ++ key)

-- A count is written as `show` writes it: no sign, no leading zero
countOf :: String -> Result Int String
countOf text = case reads text of
    [(n, "")] | n >= 0 && show n == text -> Ok n
    _ -> Error "ElaborateRequest: malformed count"

block :: [String] -> [String]
block ls = ("data " ++ show (length ls)) : ls

-- n blocks, each `data <line count>` and that many lines, and the lines after them
blocks :: Int -> [String] -> Result ([[String]], [String]) String
blocks = blocksWith id

blocksWith :: (l -> String) -> Int -> [l] -> Result ([[l]], [l]) String
blocksWith _ 0 rest = Ok ([], rest)
blocksWith text n (header : rest) =
    wordAfter "data" (text header) `bindResult` countOf `bindResult` \count ->
        let (taken, after) = splitAt count rest
         in if length taken < count
                then Error "ElaborateRequest: a block is cut short"
                else blocksWith text (n - 1) after `bindResult` \(more, rest') -> Ok (taken : more, rest')
blocksWith _ _ [] = Error "ElaborateRequest: missing data block"

firstLine :: [String] -> Result (String, [String]) String
firstLine ls = case ls of
    l : rest -> Ok (l, rest)
    [] -> Error "ElaborateRequest: the request ends early"

mapAll :: (a -> Result b String) -> [a] -> Result [b] String
mapAll f = foldr (\x rest -> f x `bindResult` \y -> rest `bindResult` \ys -> Ok (y : ys)) (Ok [])

requestHeader :: String
requestHeader = "tersus-elaborate 1"

responseHeader :: String
responseHeader = "tersus-elaborated 1"
