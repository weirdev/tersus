-- The elaborator's request and response (AST_DATA.md, "Elaboration requests"): what a host gives an
-- elaborator to elaborate one module, and what it gets back (ElaboratorTool runs the elaborator written in Tersus).
module ElaborateRequest
    ( Elaborator
    , Extraction (..)
    , Request (..)
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
import Modules (ModuleId (..))
import Syntax (Elaborated (..), Statement)
import Utils

-- Which interface to return: ordinary modules share one template export policy;
-- compiler-library extraction additionally retains physical constructor views.
data Extraction = NoInterface | ModuleInterfaceOf | LibInterfaceOf
    deriving (Show, Eq)

-- The module, whether it predeclares its own types (a package module does), whether it is a module of the
-- compiler libraries (which see a generic struct's constructor as the struct it builds), the interface to
-- give back, caller-visible interfaces, checked defining dependencies, and statements as read.
data Request = Request
    { rqModule :: ModuleId
    , rqPredeclare :: Bool
    , rqLibrary :: Bool
    , rqExtraction :: Extraction
    , rqInterfaces :: [ModuleInterface]
    , rqDefinitions :: [[ModuleInterface]]
    , rqStatements :: [Statement]
    }
    deriving (Show, Eq)

data Response
    = Accepted Elaborated (Maybe ModuleInterface)
    | -- the module does not check
      Refused String
    | -- it checks, but its interface cannot be given (Interface.extractInterface)
      RefusedInterface String
    | -- the elaborator does not handle the program yet, which is not a verdict on it
      NotModelled String
    deriving (Show)

type Elaborator = Request -> Response

writeRequest :: Request -> Result String String
writeRequest rq =
    builtinTableLines `bindResult` \builtins ->
    mapAll linesOf (rqInterfaces rq) `bindResult` \ifaces ->
        mapAll writeDefinition (rqDefinitions rq) `bindResult` \definitions ->
        writeParsedLines (rqStatements rq) `bindResult` \ast ->
            Ok $
                unlines
                    ( [ requestHeader
                      , unwords ["module", quote pkg, maybe "none" quote modu]
                      , "predeclare " ++ boolWord (rqPredeclare rq)
                      , "library " ++ boolWord (rqLibrary rq)
                      , "extract " ++ extractionWord (rqExtraction rq)
                      , "builtins"
                      ]
                        ++ block builtins
                        ++ ["interfaces " ++ show (length ifaces)]
                        ++ concatMap block ifaces
                        ++ ["definitions " ++ show (length definitions)]
                        ++ concat definitions
                        ++ block ast
                    )
  where
    writeDefinition [] = Error "ElaborateRequest: empty defining context"
    writeDefinition context = mapAll linesOf context `bindResult` \texts -> Ok (("definition " ++ show (length texts)) : concatMap block texts)
    -- (a defining context repeats the interfaces of the modules it depends on, so each is written once)
    written = Map.fromList [(ifModule i, (i, writeInterfaceLines i)) | i <- rqInterfaces rq ++ concat (rqDefinitions rq)]
    linesOf iface = case Map.lookup (ifModule iface) written of
        Just (known, ls) | known == iface -> ls
        _ -> writeInterfaceLines iface
    ModuleId pkg modu = rqModule rq

readRequest :: String -> Result Request String
readRequest text = case lines text of
    "tersus-elaborate 1" : moduleLine : predeclareLine : libraryLine : extractLine : "builtins" : afterBuiltins ->
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
        definitionBlocks rest' `bindResult` \(definitionTexts, syntax) ->
        mapAll (mapAll readInterfaceLines) definitionTexts `bindResult` \definitions ->
        blocks 1 syntax `bindResult` \(astTexts, rest'') ->
            if not (null rest'')
                then Error "ElaborateRequest: records after the module's syntax"
                else case astTexts of
                    [ast] -> readParsedLines ast `bindResult` \stmts -> Ok (Request modu flag libraryFlag extraction ifaces definitions stmts)
                    _ -> Error "ElaborateRequest: no syntax"
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
    boolOf w = case w of
        "true" -> Ok True
        "false" -> Ok False
        _ -> Error "ElaborateRequest: malformed flag"
    extractionOf w = case [e | e <- [NoInterface, ModuleInterfaceOf, LibInterfaceOf], extractionWord e == w] of
        [e] -> Ok e
        _ -> Error "ElaborateRequest: unknown extraction"

writeResponse :: Response -> Result String String
writeResponse response = case response of
    Accepted elaborated iface ->
        writeElaboratedLines elaborated `bindResult` \ast ->
            maybe (Ok Nothing) (mapResult Just . writeInterfaceLines) iface `bindResult` \ifaceLines ->
                Ok (unlines ([responseHeader, "accepted"] ++ block ast ++ maybe ["interface none"] (\t -> "interface" : block t) ifaceLines))
    Refused message -> Ok (unlines [responseHeader, "refused " ++ quote message])
    RefusedInterface message -> Ok (unlines [responseHeader, "interfaceRefused " ++ quote message])
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
        [Word "unmodelled", Str what] -> Ok (NotModelled what)
        _ -> Error "ElaborateRequest: malformed response"
    "tersus-elaborated 1" : "accepted" : _ ->
        blocksWith text 1 (drop 2 ls) `bindResult` \(astTexts, rest') -> case (astTexts, map text (take 2 rest')) of
            ([ast], ["interface none"]) -> elaborated ast `bindResult` \e -> Ok (Accepted e Nothing)
            ([ast], "interface" : _) ->
                blocksWith text 1 (drop 1 rest') `bindResult` \(ifaceTexts, rest'') -> case (ifaceTexts, rest'') of
                    ([ifaceText], []) -> elaborated ast `bindResult` \e -> interface ifaceText `bindResult` \i -> Ok (Accepted e (Just i))
                    _ -> Error "ElaborateRequest: malformed interface"
            _ -> Error "ElaborateRequest: malformed response"
    _ -> Error "ElaborateRequest: not an elaboration response"

-- What a single-file program needs of a response: the elaboration, or why there is none
acceptedElaboration :: Response -> Result Elaborated String
acceptedElaboration response = case response of
    Accepted e _ -> Ok e
    Refused message -> Error message
    RefusedInterface message -> Error message
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
