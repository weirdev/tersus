{-# LANGUAGE PatternSynonyms #-}
-- The elaborator's request and response (AST_DATA.md, "Elaboration requests"): what a host gives an
-- elaborator to elaborate one module, and what it gets back (ElaboratorTool runs the elaborator written in Tersus).
module ElaborateRequest
    ( Elaborator
    , Extraction (..)
    , Request (Request, RequestData, rqModule, rqPredeclare, rqLibrary, rqExtraction, rqInterfaces, rqDefinitions, rqLibraries, rqStatements, rqProtocols)
    , Library (..)
    , Response (Accepted, AcceptedData, Refused, RefusedInterface, Unresolved, NotModelled)
    , acceptedOwnership
    , transportMatches
    , loadTransportMatches
    , MirAnswer (..)
    , writeRequest
    , readRequest
    , writeResponse
    , readResponse
    , readResponseLines
    , readResponseBytes
    , acceptedResponse
    , requestHeader
    , responseHeader
    , LoadKind (..)
    , LoadRequest (LoadRequest, LoadRequestData, lrKind, lrReserving, lrResolver, lrEntry, lrSources, lrLibraries, lrProtocols)
    , LoadResponse (..)
    , LibraryAnswer (..)
    , Graph (..)
    , GraphModule (..)
    , GraphFile (..)
    , writeLoadRequest
    , readLoadResponseBytes
    ) where

import qualified Data.ByteString.Char8 as B
import qualified Data.Set as Set
import qualified Data.Map as Map

import AstData (readOwnershipFactsBytes, readParsedLines, writeOwnershipFactsLines, writeParsedLines)
import BuiltinTable (builtinTableLines)
import DataCodec (Token (..), quote, strictTokenize)
import Interface (ModuleInterface (..))
import InterfaceData (readInterfaceBytes, readInterfaceLines, writeInterfaceLines)
import PackageData (ImportLevel (..), LoadOptions (..), ModuleId (..), Resolver (..))
import ParsedFile (Import (..))
import Syntax (Statement)
import Types (Name, OwnershipTransport, validProtocolProviders)
import Utils

-- Which interface to return: ordinary modules share one template export policy;
-- compiler-library extraction additionally retains physical constructor views.
data Extraction = NoInterface | ModuleInterfaceOf | LibInterfaceOf
    deriving (Show, Eq)

-- The module, whether it predeclares its own types (a package module does), whether it is a module of the
-- compiler libraries (which see a generic struct's constructor as the struct it builds), the interface to
-- give back, the interfaces of the modules it imports, checked defining dependencies, the compiler libraries it
-- may be given (the elaborator selects among them), the statements as read: one list for each of the module's files
-- in the package's order, or one for a program.
data Request = RequestData
    { rqModule :: ModuleId
    , rqPredeclare :: Bool
    , rqLibrary :: Bool
    , rqExtraction :: Extraction
    , rqInterfaces :: [ModuleInterface]
    , rqDefinitions :: [[ModuleInterface]]
    , rqLibraries :: [Library]
    , rqStatements :: [[Statement]]
    , rqProtocols :: Maybe (Map.Map Name [Name])
    }
    deriving (Show, Eq)

pattern Request :: ModuleId -> Bool -> Bool -> Extraction -> [ModuleInterface] -> [[ModuleInterface]] -> [Library] -> [[Statement]] -> Request
pattern Request modu predeclaring library extraction interfaces definitions libraries statements <- RequestData modu predeclaring library extraction interfaces definitions libraries statements _
  where Request modu predeclaring library extraction interfaces definitions libraries statements = RequestData modu predeclaring library extraction interfaces definitions libraries statements Nothing

{-# COMPLETE Request #-}

data Library = Library
    { libraryName :: String
    , libraryImports :: [String]
    , libraryInterface :: ModuleInterface
    }
    deriving (Show, Eq)

data Response
    = -- with the compiler libraries the elaborator selected for the module, its MIR, and under version 2 its checked
      -- ownership facts
      AcceptedData (Maybe ModuleInterface) [String] MirAnswer (Maybe OwnershipTransport)
    | -- the module does not check
      Refused String
    | -- it checks, but its interface cannot be given (Interface.extractInterface)
      RefusedInterface String
    | -- its names do not resolve, or the libraries it calls for cannot be given it; the message is whole
      Unresolved String
    | -- the elaborator does not handle the program yet, which is not a verdict on it
      NotModelled String
    deriving (Show)

pattern Accepted :: Maybe ModuleInterface -> [String] -> MirAnswer -> Response
pattern Accepted iface libraries mir <- AcceptedData iface libraries mir _
  where Accepted iface libraries mir = AcceptedData iface libraries mir Nothing

{-# COMPLETE Accepted, Refused, RefusedInterface, Unresolved, NotModelled #-}

acceptedOwnership :: Response -> Maybe OwnershipTransport
acceptedOwnership response = case response of
    AcceptedData _ _ _ facts -> facts
    _ -> Nothing

-- An accepted answer to a version 2 request carries its ownership facts, and one to a version 1 request none
transportMatches :: Bool -> Response -> Result Response String
transportMatches checked response = case response of
    AcceptedData _ _ _ facts | checked /= (facts /= Nothing) ->
        Error (if checked then "ElaborateRequest: a version 2 answer without its ownership facts" else "ElaborateRequest: ownership facts in a version 1 answer")
    _ -> Ok response

loadTransportMatches :: Bool -> LoadResponse -> Result LoadResponse String
loadTransportMatches checked loadResponse = case loadResponse of
    LoadedModules answers -> allMatch [r | (_, _, r) <- answers]
    LoadedProgram r -> allMatch [r]
    AssembledPackage _ _ answers -> allMatch [r | (_, _, r) <- answers]
    AssembledProgram _ r -> allMatch [r]
    LoadedLibraries answers _ -> allMatch (map laResponse answers)
    _ -> Ok loadResponse
  where
    allMatch = foldr (\r rest -> transportMatches checked r `bindResult` \_ -> rest) (Ok loadResponse)

-- The `mir` section of an accepted response (AST_DATA.md): the lines of the module's lowered unit (`tersus-mir 3`,
-- MIR.md), which MirData.readLoweredBytes reads, or the message of the lowering's refusal
data MirAnswer = MirLowered [B.ByteString] | MirRefused String
    deriving (Show)

type Elaborator = Request -> Response

writeRequest :: Request -> Result String String
writeRequest rq =
    syntax `bindResult` \() ->
    protocolRecords (rqProtocols rq) `bindResult` \protocols ->
    builtinTableLines `bindResult` \builtins ->
    mapAll linesOf (rqInterfaces rq) `bindResult` \ifaces ->
        mapAll writeDefinition (rqDefinitions rq) `bindResult` \definitions ->
        mapAll writeLibrary (rqLibraries rq) `bindResult` \libraries ->
        mapAll writeParsedLines (rqStatements rq) `bindResult` \asts ->
            Ok $
                unlines
                    ( [ if rqProtocols rq == Nothing then requestHeader else "tersus-elaborate 2"
                      , unwords ["module", quote pkg, maybe "none" quote modu]
                      , "predeclare " ++ boolWord (rqPredeclare rq)
                      , "library " ++ boolWord (rqLibrary rq)
                      , "extract " ++ extractionWord (rqExtraction rq)
                      ] ++ protocols ++
                      [ "builtins"
                      ]
                        ++ block builtins
                        ++ ["interfaces " ++ show (length ifaces)]
                        ++ concatMap block ifaces
                        ++ ["definitions " ++ show (length definitions)]
                        ++ concat definitions
                        ++ (if null libraries then [] else ("libraries " ++ show (length libraries)) : concat libraries)
                        ++ concatMap block asts
                    )
  where
    syntax
        | length (rqStatements rq) /= 1 = Error "ElaborateRequest: the syntax is not one block"
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

levelWord :: ImportLevel -> String
levelWord level = case level of
    LevelModule -> "module"
    LevelFile -> "file"
    LevelSymbol -> "symbol"

readRequest :: String -> Result Request String
readRequest text = requestEnvelope (lines text) `bindResult` \(protocols, records) -> readRequestRecords protocols records

protocolRecords :: Maybe (Map.Map Name [Name]) -> Result [String] String
protocolRecords Nothing = Ok []
protocolRecords (Just protocols)
    | any (not . uncurry validProtocolProviders) (Map.toList protocols) = Error "ElaborateRequest: malformed protocol providers"
    | otherwise = Ok (("protocols " ++ show (Map.size protocols)) : [unwords (["protocol", quote role, show (length providers)] ++ map quote providers) | (role, providers) <- Map.toAscList protocols])

requestEnvelope :: [String] -> Result (Maybe (Map.Map Name [Name]), [String]) String
requestEnvelope records@(header : _)
    | header == "tersus-elaborate 1" = Ok (Nothing, records)
requestEnvelope ("tersus-elaborate 2" : modu : predeclaring : library : extraction : countLine : rest) =
    wordAfter "protocols" countLine `bindResult` countOf `bindResult` \count -> parseProtocols count rest `bindResult` \(pairs, remaining) ->
        let protocols = Map.fromList pairs
         in protocolRecords (Just protocols) `bindResult` \_ ->
            if and (zipWith (<) (map fst pairs) (drop 1 (map fst pairs)))
                then Ok (Just protocols, "tersus-elaborate 1" : modu : predeclaring : library : extraction : remaining)
                else Error "ElaborateRequest: protocol roles out of order or repeated"
  where
    parseProtocols 0 remaining = Ok ([], remaining)
    parseProtocols n (line : remaining) = strictTokenize line `bindResult` \tokens -> case tokens of
        Word "protocol" : Str role : Word k : names | n > 0 -> countOf k `bindResult` \size ->
            if length names == size && all (\token -> case token of Str _ -> True; _ -> False) names
                then parseProtocols (n-1) remaining `bindResult` \(more, after) -> Ok ((role, [name | Str name <- names]) : more, after)
                else Error "ElaborateRequest: malformed protocol binding"
        _ -> Error "ElaborateRequest: malformed protocol binding"
    parseProtocols _ [] = Error "ElaborateRequest: missing protocol binding"
requestEnvelope _ = Error "ElaborateRequest: not an elaboration request"

readRequestRecords :: Maybe (Map.Map Name [Name]) -> [String] -> Result Request String
readRequestRecords protocols records = case records of
    "tersus-elaborate 1" : moduleLine : predeclareLine : libraryLine : extractLine : builtinsLine : afterBuiltins ->
        (if builtinsLine == "builtins" then Ok () else Error "ElaborateRequest: expected builtins") `bindResult` \() ->
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
        blocks 1 afterLibraries `bindResult` \(astTexts, rest'') ->
            if not (null rest'')
                then Error "ElaborateRequest: records after the module's syntax"
                else if null astTexts then Error "ElaborateRequest: no syntax"
                else mapAll readParsedLines astTexts `bindResult` \stmts -> Ok ((Request modu flag libraryFlag extraction ifaces definitions libraries stmts){rqProtocols = protocols})
    _ -> Error "ElaborateRequest: not an elaboration request"
  where
    definitionBlocks (line : rest) = wordAfter "definitions" line `bindResult` countOf `bindResult` \count -> contexts count rest
    definitionBlocks [] = Error "ElaborateRequest: missing defining interfaces"
    contexts 0 rest = Ok ([], rest)
    contexts n (line : rest) = wordAfter "definition" line `bindResult` countOf `bindResult` \count ->
        if count == 0 then Error "ElaborateRequest: empty defining context" else
        blocks count rest `bindResult` \(context, remaining) -> contexts (n - 1) remaining `bindResult` \(more, syntax) -> Ok (context : more, syntax)
    contexts _ [] = Error "ElaborateRequest: missing defining context"
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
    strOf (Str text) = Just text
    strOf _ = Nothing
    boolOf w = case w of
        "true" -> Ok True
        "false" -> Ok False
        _ -> Error "ElaborateRequest: malformed flag"
    extractionOf w = case [e | e <- [NoInterface, ModuleInterfaceOf, LibInterfaceOf], extractionWord e == w] of
        [e] -> Ok e
        _ -> Error "ElaborateRequest: unknown extraction"

writeResponse :: Response -> Result String String
writeResponse response = case response of
    AcceptedData iface libraries mir facts ->
        maybe (Ok Nothing) (mapResult Just . writeInterfaceLines) iface `bindResult` \ifaceLines ->
        maybe (Ok []) (mapResult (\t -> "ownership" : block t) . writeOwnershipFactsLines) facts `bindResult` \factLines ->
            Ok (unlines ([responseHeader, "accepted"] ++ maybe ["interface none"] (\t -> "interface" : block t) ifaceLines ++ mirLines mir ++ factLines ++ librariesLine libraries))
    Refused message -> Ok (unlines [responseHeader, "refused " ++ quote message])
    RefusedInterface message -> Ok (unlines [responseHeader, "interfaceRefused " ++ quote message])
    Unresolved message -> Ok (unlines [responseHeader, "unresolved " ++ quote message])
    NotModelled what -> Ok (unlines [responseHeader, "unmodelled " ++ quote what])

readResponse :: String -> Result Response String
readResponse = readResponseLines . lines

readResponseLines :: [String] -> Result Response String
readResponseLines = readResponseWith id B.pack readInterfaceLines

readResponseBytes :: [B.ByteString] -> Result Response String
readResponseBytes = readResponseWith B.unpack id readInterfaceBytes

readResponseWith :: (l -> String) -> (l -> B.ByteString) -> ([l] -> Result ModuleInterface String) -> [l] -> Result Response String
readResponseWith text bytes interface ls = case map text (take 3 ls) of
    ["tersus-elaborated 1", line] -> strictTokenize line `bindResult` \ts -> case ts of
        [Word "refused", Str message] -> Ok (Refused message)
        [Word "interfaceRefused", Str message] -> Ok (RefusedInterface message)
        [Word "unresolved", Str message] -> Ok (Unresolved message)
        [Word "unmodelled", Str what] -> Ok (NotModelled what)
        _ -> Error "ElaborateRequest: malformed response"
    "tersus-elaborated 1" : "accepted" : _ ->
        case map text (take 1 (drop 2 ls)) of
            ["interface none"] -> mirFactsOf text bytes (drop 3 ls) `bindResult` \((mir, facts), after) -> librariesOf (map text after) `bindResult` \libraries -> Ok (AcceptedData Nothing libraries mir facts)
            ["interface"] ->
                blocksWith text 1 (drop 3 ls) `bindResult` \(ifaceTexts, rest'') -> case ifaceTexts of
                    [ifaceText] -> mirFactsOf text bytes rest'' `bindResult` \((mir, facts), after) -> librariesOf (map text after) `bindResult` \libraries -> interface ifaceText `bindResult` \i -> Ok (AcceptedData (Just i) libraries mir facts)
                    _ -> Error "ElaborateRequest: malformed interface"
            _ -> Error "ElaborateRequest: malformed response"
    _ -> Error "ElaborateRequest: not an elaboration response"

-- The `mir` section, which follows the interface of an accepted response: `mir N` and the N lines of the module's
-- unit, or `mir refused "MESSAGE"`
mirLines :: MirAnswer -> [String]
mirLines mir = case mir of
    MirRefused message -> ["mir refused " ++ quote message]
    MirLowered ls -> ("mir " ++ show (length ls)) : map B.unpack ls

-- The `mir` section and, under version 2, the `ownership` section after it: `ownership`, `data N` and the N lines of the
-- facts (AstData.readOwnershipFactsBytes)
mirFactsOf :: (l -> String) -> (l -> B.ByteString) -> [l] -> Result ((MirAnswer, Maybe OwnershipTransport), [l]) String
mirFactsOf text bytes ls = mirOf text bytes ls `bindResult` \(mir, rest) -> case rest of
    line : countLine : more | text line == "ownership" -> wordAfter "data" (text countLine) `bindResult` countOf `bindResult` \n ->
        if length (take n more) /= n then Error "ElaborateRequest: the ownership section ends early" else
        readOwnershipFactsBytes (map bytes (take n more)) `bindResult` \facts -> Ok ((mir, Just facts), drop n more)
    _ -> Ok ((mir, Nothing), rest)

mirOf :: (l -> String) -> (l -> B.ByteString) -> [l] -> Result (MirAnswer, [l]) String
mirOf text bytes ls = case ls of
    line : rest | take 4 (text line) == "mir " -> strictTokenize (text line) `bindResult` \ts -> case ts of
        [Word "mir", Word "refused", Str message] -> Ok (MirRefused message, rest)
        [Word "mir", Word count] | Ok n <- countOf count, length (take n rest) == n -> Ok (MirLowered (map bytes (take n rest)), drop n rest)
        _ -> Error "ElaborateRequest: malformed mir section"
    _ -> Error "ElaborateRequest: an accepted response without its mir section"

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

-- An accepted response, or why the program was not accepted
acceptedResponse :: Response -> Result Response String
acceptedResponse response = case response of
    Accepted{} -> Ok response
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

-- ---------------------------------------------------------------------------
-- Loading (AST_DATA.md, "Loading"): the snapshot the host read, answered as a whole by the loader written in Tersus

-- graph: the module graph and each file as read (Modules.LoadResult); package: every module of the package elaborated in
-- order; program and parse: a single file, elaborated or only read (SourceParse); equality: a file read with the type,
-- clone and equality libraries in front of it (Compile.parseWithEquality); libraries: the compiler libraries elaborated
data LoadKind
    = LoadGraph | LoadPackage | LoadProgram | LoadParse | LoadEquality | LoadLibraries
    | LoadPackageAssembly ModuleId | LoadProgramAssembly
    deriving (Show, Eq)

-- The entry is a file of the snapshot, read from the filesystem or given as source (standard input, a program's text);
-- lrProtocols asks for version 2 (checked ownership transport) for every unit the load elaborates, as rqProtocols does
data LoadRequest = LoadRequestData
    { lrKind :: LoadKind
    , lrReserving :: Bool
    , lrResolver :: Resolver
    , lrEntry :: Maybe (FilePath, Bool)
    , lrSources :: [(String, Bool, String)]
    , lrLibraries :: [Library]
    , lrProtocols :: Maybe (Map.Map Name [Name])
    }
    deriving (Show, Eq)

pattern LoadRequest :: LoadKind -> Bool -> Resolver -> Maybe (FilePath, Bool) -> [(String, Bool, String)] -> [Library] -> LoadRequest
pattern LoadRequest kind reserving resolver entry sources libraries <- LoadRequestData kind reserving resolver entry sources libraries _
  where LoadRequest kind reserving resolver entry sources libraries = LoadRequestData kind reserving resolver entry sources libraries Nothing

{-# COMPLETE LoadRequest #-}

data GraphFile = GraphFile
    { gfName :: String
    , gfStem :: String
    , gfPath :: FilePath
    , gfDeclNames :: [String]
    , gfImports :: [(Import, ImportLevel, ModuleId, Maybe String, Maybe String, String)]
    , gfBody :: [Statement]
    }
    deriving (Show, Eq)

data GraphModule = GraphModule
    { gmId :: ModuleId
    , gmNoPrelude :: Bool
    , gmDependencies :: [ModuleId]
    , gmFiles :: [GraphFile]
    }
    deriving (Show, Eq)

data Graph = Graph
    { graphRoot :: FilePath
    , graphName :: String
    , graphEntry :: FilePath
    , graphEntryModule :: ModuleId
    , graphModules :: [GraphModule]
    , graphSources :: [FilePath]
    , graphPolicies :: [(String, FilePath, Bool)]
    }
    deriving (Show, Eq)

data LibraryAnswer = LibraryAnswer
    { laName :: String
    , laImports :: [String]
    , laStatements :: [Statement]
    , laResponse :: Response
    }
    deriving (Show)

type ModuleAnswer = (ModuleId, [ModuleId], Response)

data LoadResponse
    = -- the load refuses, in the loader's words
      NotLoaded String
    | LoadedStandalone FilePath [Statement]
    | LoadedGraph Graph
    | -- each module in order with the modules of the interfaces its lowering takes; the last may be a refusal
      LoadedModules [ModuleAnswer]
    | LoadedProgram Response
    | AssembledPackage ModuleId [(String, ModuleId)] [ModuleAnswer]
    | AssembledProgram [String] Response
    | -- the file does not read, in the reader's words, whole
      Unparsed String
    | -- the libraries the file was read with, their statements as read in their order, and its statements
      ParsedSource [String] [Statement] [Statement]
    | -- the libraries in order, then the native storage helpers; a failure to read them ends the list
      LoadedLibraries [LibraryAnswer] (Maybe String)
    deriving (Show)

loadKindWord :: LoadKind -> String
loadKindWord kind = case kind of
    LoadGraph -> "graph"
    LoadPackage -> "package"
    LoadProgram -> "program"
    LoadParse -> "parse"
    LoadEquality -> "equality"
    LoadLibraries -> "libraries"
    LoadPackageAssembly _ -> "package assembly"
    LoadProgramAssembly -> "program assembly"

writeLoadRequest :: LoadRequest -> Result String String
writeLoadRequest rq =
    checkAssemblyCatalog rq `bindResult` \() ->
    protocolRecords (lrProtocols rq) `bindResult` \protocols ->
    builtinTableLines `bindResult` \builtins ->
    mapAll writeLibrary (lrLibraries rq) `bindResult` \libraries ->
        Ok $ concat
            ( map (++ "\n")
                ( [ if lrProtocols rq == Nothing then requestHeader else "tersus-elaborate 2"
                  , "load " ++ loadKindWord (lrKind rq)
                  ] ++ protocols ++
                  [ "noPrelude " ++ boolWord (noPrelude options)
                  , "reserving " ++ boolWord (lrReserving rq)
                  , unwords (["roots", show (length roots)] ++ concat [[quote name, quote root] | (name, root) <- roots])
                  , "std " ++ maybe "none" quote (installedStdRoot options)
                  , "entry " ++ maybe "none" (\(path, source) -> quote path ++ (if source then " source" else " file")) (lrEntry rq)
                  , unwords (["canonical", show (Map.size canonical)] ++ concat [[quote from, quote to] | (from, to) <- Map.toList canonical])
                  , "dirs " ++ show (Map.size dirs)
                  ]
                    ++ [unwords (["dir", quote dir, show (length subdirs)] ++ map quote subdirs ++ [show (length files)] ++ map quote files) | (dir, (subdirs, files)) <- Map.toList dirs]
                    ++ ["files " ++ show (Map.size (resolverFiles resolver))]
                )
                ++ [counted ("file " ++ quote path) text | (path, text) <- Map.toList (resolverFiles resolver)]
                ++ map (++ "\n") ["sources " ++ show (length (lrSources rq))]
                ++ [counted ("source " ++ quote name ++ (if native then " native" else " implicit")) text | (name, native, text) <- lrSources rq]
                ++ map (++ "\n") (["builtins"] ++ block builtins ++ (if null libraries then [] else ("libraries " ++ show (length libraries)) : concat libraries))
            )
  where
    resolver = lrResolver rq
    options = resolverOptions resolver
    roots = Map.toList (packageRoots options)
    canonical = resolverCanonical resolver
    dirs = resolverDirs resolver
    counted header text = let bytes = encodeUtf8 text in header ++ " " ++ show (length bytes) ++ "\n" ++ bytes ++ "\n"
    writeLibrary (Library name imports iface) = writeInterfaceLines iface `bindResult` \t -> Ok (unwords (["library", quote name, show (length imports)] ++ map quote imports) : block t)

checkAssemblyCatalog :: LoadRequest -> Result () String
checkAssemblyCatalog rq = case lrKind rq of
    LoadPackageAssembly _ -> unique
    LoadProgramAssembly -> unique
    _ -> Ok ()
  where
    names = map libraryName (lrLibraries rq)
    unique
        | Set.size (Set.fromList names) == length names = Ok ()
        | otherwise = Error "ElaborateRequest: duplicate assembly catalog identity"

readLoadResponseBytes :: LoadRequest -> [B.ByteString] -> Result LoadResponse String
readLoadResponseBytes rq ls = checkAssemblyCatalog rq `bindResult` \() -> case ls of
    header : rest | B.unpack header == responseHeader -> case lrKind rq of
        LoadGraph -> graphOf rest
        LoadPackage -> packageAnswers Nothing rest
        LoadPackageAssembly entry -> packageAnswers (Just entry) rest
        LoadProgram -> programAnswer False rest
        LoadProgramAssembly -> programAnswer True rest
        LoadParse -> parsedOf rest
        LoadEquality -> parsedOf rest
        LoadLibraries -> librariesAnswer rest
    _ -> Error "ElaborateRequest: not a load response"
  where
    text = B.unpack
    tokens line = strictTokenize (text line)
    notLoaded line = case tokens line of
        Ok [Word "notLoaded", Str message] -> Just (NotLoaded message)
        Ok [Word "unparsed", Str message] -> Just (Unparsed message)
        _ -> Nothing
    graphOf (line : rest) | Just r <- notLoaded line = if null rest then Ok r else Error "ElaborateRequest: records after a refusal"
    graphOf (line : rest) = tokens line `bindResult` \ts -> case ts of
        [Word "standalone", Str path] -> blocksWith text 1 rest `bindResult` \(asts, after) -> case (asts, after) of
            ([ast], []) -> readParsedLines (map text ast) `bindResult` \body -> Ok (LoadedStandalone path body)
            _ -> Error "ElaborateRequest: malformed standalone answer"
        [Word "package", Str root, Str name, Str entry, p, m] -> moduleIdOf p m `bindResult` \entryId ->
            case rest of
                countLine : more -> wordAfter "modules" (text countLine) `bindResult` countOf `bindResult` \n ->
                    readGraphModules n more `bindResult` \(modules, after) -> trailer after `bindResult` \(sources, policies) ->
                        Ok (LoadedGraph (Graph root name entry entryId modules sources policies))
                [] -> Error "ElaborateRequest: missing modules"
        _ -> Error "ElaborateRequest: malformed graph"
    graphOf [] = Error "ElaborateRequest: empty graph answer"
    readGraphModules :: Int -> [B.ByteString] -> Result ([GraphModule], [B.ByteString]) String
    readGraphModules 0 rest = Ok ([], rest)
    readGraphModules n (line : rest) = tokens line `bindResult` \ts -> case ts of
        Word "module" : p : m : Word prelude : Word fileCount : Word depCount : deps
            | Ok f <- countOf fileCount, Ok d <- countOf depCount, length deps == 2 * d ->
                moduleIdOf p m `bindResult` \modu -> boolOf prelude `bindResult` \flag -> pairs deps `bindResult` \depIds ->
                    graphFiles f rest `bindResult` \(files, after) -> readGraphModules (n - 1) after `bindResult` \(more, after') ->
                        Ok (GraphModule modu flag depIds files : more, after')
        _ -> Error "ElaborateRequest: malformed graph module"
    readGraphModules _ [] = Error "ElaborateRequest: missing graph module"
    pairs (p : m : rest) = moduleIdOf p m `bindResult` \modu -> pairs rest `bindResult` \more -> Ok (modu : more)
    pairs [] = Ok []
    pairs _ = Error "ElaborateRequest: malformed module pair"
    graphFiles :: Int -> [B.ByteString] -> Result ([GraphFile], [B.ByteString]) String
    graphFiles 0 rest = Ok ([], rest)
    graphFiles n (line : rest) = tokens line `bindResult` \ts -> case ts of
        Word "file" : Str name : Str stem : Str path : Word declCount : more
            | Ok d <- countOf declCount, length more == d + 1, Just decls <- mapM strOf (take d more), [Word importCount] <- drop d more, Ok k <- countOf importCount ->
                mapAll importOf (take k rest) `bindResult` \imports ->
                    blocksWith text 1 (drop k rest) `bindResult` \(asts, after) -> case asts of
                        [ast] -> readParsedLines (map text ast) `bindResult` \body -> graphFiles (n - 1) after `bindResult` \(files, after') ->
                            Ok (GraphFile name stem path decls imports body : files, after')
                        _ -> Error "ElaborateRequest: malformed graph file"
        _ -> Error "ElaborateRequest: malformed graph file"
    graphFiles _ [] = Error "ElaborateRequest: missing graph file"
    importOf line = tokens line `bindResult` \ts -> case ts of
        Word "import" : Word l : Word c : Word segmentCount : more
            | Ok lineNo <- countOf l, Ok col <- countOf c, Ok k <- countOf segmentCount, Just segments <- mapM strOf (take k more) -> importRest (Import segments) lineNo col (drop k more)
        _ -> Error "ElaborateRequest: malformed graph import"
    importRest mk lineNo col more = case more of
        alias : rest -> optionalOf alias `bindResult` \a -> case rest of
            Word "none" : rest' -> targetOf (mk a Nothing lineNo col) rest'
            Word count : rest' | Ok k <- countOf count, Just names <- mapM strOf (take k rest') -> targetOf (mk a (Just names) lineNo col) (drop k rest')
            _ -> Error "ElaborateRequest: malformed graph import names"
        [] -> Error "ElaborateRequest: malformed graph import"
    targetOf imp rest = case rest of
        [Word level, p, m, file, symbol, Str canonical] | Just l <- lookup level [(levelWord v, v) | v <- [minBound ..]] ->
            moduleIdOf p m `bindResult` \target -> optionalOf file `bindResult` \f -> optionalOf symbol `bindResult` \sym -> Ok (imp, l, target, f, sym, canonical)
        _ -> Error "ElaborateRequest: malformed graph import target"
    trailer (sourcesLine : policiesLine : rest) = tokens sourcesLine `bindResult` \ts -> case ts of
        Word "sources" : Word count : paths | Ok n <- countOf count, length paths == n, Just ps <- mapM strOf paths ->
            wordAfter "policies" (text policiesLine) `bindResult` countOf `bindResult` \k ->
                if length rest /= k then Error "ElaborateRequest: malformed policies" else
                mapAll policyOf rest `bindResult` \policies -> Ok (ps, policies)
        _ -> Error "ElaborateRequest: malformed sources"
    trailer _ = Error "ElaborateRequest: missing sources"
    policyOf line = tokens line `bindResult` \ts -> case ts of
        [Word "policy", Str name, Str root, Word flag] -> boolOf flag `bindResult` \b -> Ok (name, root, b)
        _ -> Error "ElaborateRequest: malformed policy"
    packageAnswers _ (line : rest) | Just r <- notLoaded line = if null rest then Ok r else Error "ElaborateRequest: records after a refusal"
    packageAnswers expected ls' = modulesOf (expected /= Nothing) ls' `bindResult` \(answers, after) -> case expected of
        Nothing | null after -> Ok (LoadedModules answers)
                | otherwise -> Error "ElaborateRequest: records after the end"
        Just entry ->
            let ids = [m | (m, _, _) <- answers]
                complete = entry `elem` ids && all (\(_, _, r) -> packageLowered r) answers
             in if Set.size (Set.fromList ids) /= length ids
                    then Error "ElaborateRequest: repeated module answer"
                    else if complete
                        then packageRecipe entry ids after `bindResult` \rows -> Ok (AssembledPackage entry rows answers)
                        else if null after then Ok (LoadedModules answers) else Error "ElaborateRequest: assembly after an incomplete package"
    packageLowered (Accepted (Just _) _ MirLowered{}) = True
    packageLowered _ = False
    packageRecipe entry ids (line : rest) = tokens line `bindResult` \ts -> case ts of
        [Word "assembly", p, m, Word count] | Ok n <- countOf count, length rest == n ->
            moduleIdOf p m `bindResult` \reported ->
                if reported /= entry || last ids /= entry then Error "ElaborateRequest: unknown or misordered assembly entry" else
                mapAll (libraryRow (ranks ids)) rest `bindResult` \rows ->
                    let order = map snd rows
                        names = [name | ((name, _), _) <- rows]
                     in if Set.size (Set.fromList names) /= n || not (ascending order)
                            then Error "ElaborateRequest: repeated or misordered assembly library"
                            else Ok (map fst rows)
        _ -> Error "ElaborateRequest: malformed package assembly"
    packageRecipe _ _ [] = Error "ElaborateRequest: missing package assembly"
    libraryRow contributors line = tokens line `bindResult` \ts -> case ts of
        [Word "library", Str name, p, m] -> moduleIdOf p m `bindResult` \modu ->
            case (Map.lookup name catalog, Map.lookup modu contributors) of
                (Just li, Just mi) -> Ok ((name, modu), (mi, li))
                _ -> Error "ElaborateRequest: unknown assembly library or contributor"
        _ -> Error "ElaborateRequest: malformed assembly library"
    programAnswer assembly ls' = sourceOf ls' `bindResult` \answer -> case answer of
        Left response -> Ok response
        Right (response@(Accepted _ _ MirLowered{}), after) | assembly ->
            programRecipe after `bindResult` \names -> Ok (AssembledProgram names response)
        Right (response, []) -> Ok (LoadedProgram response)
        Right _ -> Error "ElaborateRequest: records after the program's answer"
    programRecipe [line] = tokens line `bindResult` \ts -> case ts of
        Word "assembly" : Word count : names | Ok n <- countOf count, length names == n, Just ns <- mapM strOf names ->
            case mapM (`Map.lookup` catalog) ns of
                Just order | ascending order -> Ok ns
                _ -> Error "ElaborateRequest: unknown, repeated or misordered assembly library"
        _ -> Error "ElaborateRequest: malformed program assembly"
    programRecipe _ = Error "ElaborateRequest: missing assembly or records after it"
    catalog = ranks (map libraryName (lrLibraries rq))
    ranks xs = Map.fromList (zip xs [0 :: Int ..])
    ascending xs = and (zipWith (<) xs (drop 1 xs))
    modulesOf _ (line : rest) | text line == "end" = Ok ([], rest)
    modulesOf strict (line : loweringLine : rest) = tokens line `bindResult` \ts -> case ts of
        [Word "module", p, m] -> moduleIdOf p m `bindResult` \modu -> tokens loweringLine `bindResult` \lts -> case lts of
            Word "lowering" : Word count : ids | Ok n <- countOf count, even (length ids), length ids `div` 2 == n -> pairs ids `bindResult` \lowering ->
                answerOf rest `bindResult` \(response, after) -> case response of
                    Accepted{} -> continue modu lowering response after
                    _ | not strict -> continue modu lowering response after
                      | end : trailer' <- after, text end == "end" -> Ok ([(modu, lowering, response)], trailer')
                      | otherwise -> Error "ElaborateRequest: expected end after a module refusal"
            _ -> Error "ElaborateRequest: malformed lowering"
        _ -> Error "ElaborateRequest: malformed module answer"
      where
        continue modu lowering response after = modulesOf strict after `bindResult` \(more, trailer') -> Ok ((modu, lowering, response) : more, trailer')
    modulesOf _ _ = Error "ElaborateRequest: the answers end early"
    sourceOf (line : rest) | Just r <- notLoaded line = if null rest then Ok (Left r) else Error "ElaborateRequest: records after a refusal"
    sourceOf ls' = mapResult Right (answerOf ls')
    parsedOf (line : rest) | Just r <- notLoaded line = if null rest then Ok r else Error "ElaborateRequest: records after a refusal"
    parsedOf (line : librariesLine' : rest) | text line == "parsed" = tokens librariesLine' `bindResult` \ts -> case ts of
        Word "libraries" : Word count : names | Ok n <- countOf count, length names == n, Just ns <- mapM strOf names ->
            blocksWith text (n + 1) rest `bindResult` \(asts, after) -> case (reverse asts, after) of
                (ast : libraries, []) -> mapAll (readParsedLines . map text) (reverse libraries) `bindResult` \stmts ->
                    readParsedLines (map text ast) `bindResult` \body -> Ok (ParsedSource ns (concat stmts) body)
                _ -> Error "ElaborateRequest: malformed parse answer"
        _ -> Error "ElaborateRequest: malformed parse answer"
    parsedOf _ = Error "ElaborateRequest: malformed parse answer"
    librariesAnswer (line : rest) = tokens line `bindResult` \ts -> case ts of
        [Word "librariesFailed", Str message] | null rest -> Ok (LoadedLibraries [] (Just message))
        [Word "nativesFailed", Str message] | null rest -> Ok (LoadedLibraries [] (Just message))
        [Word "end"] | null rest -> Ok (LoadedLibraries [] Nothing)
        Word "library" : Str name : Word count : imports | Ok n <- countOf count, length imports == n, Just is <- mapM strOf imports ->
            blocksWith text 1 rest `bindResult` \(asts, after) -> case asts of
                [ast] -> readParsedLines (map text ast) `bindResult` \stmts -> answerOf after `bindResult` \(response, after') ->
                    librariesAnswer after' `bindResult` \more -> case more of
                        LoadedLibraries answers failure -> Ok (LoadedLibraries (LibraryAnswer name is stmts response : answers) failure)
                        _ -> Error "ElaborateRequest: malformed libraries answer"
                _ -> Error "ElaborateRequest: malformed library"
        _ -> Error "ElaborateRequest: malformed libraries answer"
    librariesAnswer [] = Error "ElaborateRequest: the libraries answer ends early"
    -- one module's answer, as a module response gives it after its header, and the records after it
    answerOf :: [B.ByteString] -> Result (Response, [B.ByteString]) String
    answerOf (line : rest) = case text line of
        "accepted" -> case map text (take 1 rest) of
            ["interface none"] -> mirFactsOf text id (drop 1 rest) `bindResult` \((mir, facts), afterMir) -> withLibraries afterMir `bindResult` \(libs, after') -> Ok (AcceptedData Nothing libs mir facts, after')
            ["interface"] -> blocksWith text 1 (drop 1 rest) `bindResult` \(ifaces, after') -> case ifaces of
                [ifaceText] -> mirFactsOf text id after' `bindResult` \((mir, facts), afterMir) -> withLibraries afterMir `bindResult` \(libs, after'') -> readInterfaceBytes ifaceText `bindResult` \i -> Ok (AcceptedData (Just i) libs mir facts, after'')
                _ -> Error "ElaborateRequest: malformed interface"
            _ -> Error "ElaborateRequest: malformed answer"
        _ -> tokens line `bindResult` \ts -> case ts of
            [Word "refused", Str message] -> Ok (Refused message, rest)
            [Word "interfaceRefused", Str message] -> Ok (RefusedInterface message, rest)
            [Word "unresolved", Str message] -> Ok (Unresolved message, rest)
            [Word "unmodelled", Str what] -> Ok (NotModelled what, rest)
            _ -> Error "ElaborateRequest: malformed answer"
    answerOf [] = Error "ElaborateRequest: missing answer"
    withLibraries (line : rest) | take 10 (text line) == "libraries " = librariesOf [text line] `bindResult` \libs -> Ok (libs, rest)
    withLibraries rest = Ok ([], rest)
    moduleIdOf (Str pkg) (Word "none") = Ok (ModuleId pkg Nothing)
    moduleIdOf (Str pkg) (Str modu) = Ok (ModuleId pkg (Just modu))
    moduleIdOf _ _ = Error "ElaborateRequest: malformed module"
    strOf (Str t) = Just t
    strOf _ = Nothing
    optionalOf (Word "none") = Ok Nothing
    optionalOf (Str t) = Ok (Just t)
    optionalOf _ = Error "ElaborateRequest: malformed optional name"
    boolOf w = case w of
        "true" -> Ok True
        "false" -> Ok False
        _ -> Error "ElaborateRequest: malformed flag"
