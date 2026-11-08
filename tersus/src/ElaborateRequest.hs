-- The elaborator's request and response (AST_DATA.md, "Elaboration requests"): what a host gives an
-- elaborator to elaborate one module, and what it gets back. `respond` is the Haskell elaborator answering
-- a request, the reference any other elaborator is compared with.
module ElaborateRequest
    ( Elaborator
    , Extraction (..)
    , Request (..)
    , Response (..)
    , writeRequest
    , readRequest
    , writeResponse
    , readResponse
    , respond
    , acceptedElaboration
    ) where

import qualified Data.Map as Map

import AstData (readElaborated, readParsed, writeElaborated, writeParsed)
import BuiltinTable (builtinTableText)
import DataCodec (Token (..), quote, strictTokenize)
import Interface (ModuleInterface (..), extractInterface, extractLibInterface, mergeInterfacesImportEnv, predeclareOwnEnv)
import InterfaceData (readInterface, writeInterface)
import Modules (ModuleId (..))
import Syntax (Elaborated (..), Statement)
import TypeCheck (ImportEnv (..), elaborateWith)
import Utils

-- Which interface of the module the elaborator also gives back: none (a single-file program), the
-- interface of a package module (Interface.extractInterface) or of a compiler-library module
-- (Interface.extractLibInterface)
data Extraction = NoInterface | ModuleInterfaceOf | LibInterfaceOf
    deriving (Show, Eq)

-- The module, whether it predeclares its own types (a package module does), whether it is a module of the
-- compiler libraries (which see a generic struct's constructor as the struct it builds), the interface to
-- give back, the interfaces it sees in the order they are merged (the first wins a name), and its
-- statements as read
data Request = Request
    { rqModule :: ModuleId
    , rqPredeclare :: Bool
    , rqLibrary :: Bool
    , rqExtraction :: Extraction
    , rqInterfaces :: [ModuleInterface]
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

-- How a module is elaborated: `respond` in process, or another elaborator answering the same request
type Elaborator = Request -> Response

writeRequest :: Request -> Result String String
writeRequest rq =
    builtinTableText `bindResult` \builtins ->
    mapAll writeInterface (rqInterfaces rq) `bindResult` \ifaces ->
        writeParsed (rqStatements rq) `bindResult` \ast ->
            Ok $
                unlines
                    ( [ "tersus-elaborate 1"
                      , unwords ["module", quote pkg, maybe "none" quote modu]
                      , "predeclare " ++ boolWord (rqPredeclare rq)
                      , "library " ++ boolWord (rqLibrary rq)
                      , "extract " ++ extractionWord (rqExtraction rq)
                      , "builtins"
                      ]
                        ++ block builtins
                        ++ ["interfaces " ++ show (length ifaces)]
                        ++ concatMap block ifaces
                    )
                    ++ block' ast
  where
    ModuleId pkg modu = rqModule rq
    block text = lines (block' text)
    block' text = unlines (("data " ++ show (length (lines text))) : lines text)

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
        builtinTableText `bindResult` \table ->
        (if map lines builtinTexts == [lines table] then Ok () else Error "ElaborateRequest: the request's builtin table is not this compiler's") `bindResult` \() ->
        firstLine afterTable `bindResult` \(countLine, rest) ->
        wordAfter "interfaces" countLine `bindResult` \countText ->
        countOf countText `bindResult` \count ->
        blocks count rest `bindResult` \(ifaceTexts, rest') ->
        mapAll readInterface ifaceTexts `bindResult` \ifaces ->
        blocks 1 rest' `bindResult` \(astTexts, rest'') ->
            if not (null rest'')
                then Error "ElaborateRequest: records after the module's syntax"
                else case astTexts of
                    [ast] -> readParsed ast `bindResult` \stmts -> Ok (Request modu flag libraryFlag extraction ifaces stmts)
                    _ -> Error "ElaborateRequest: no syntax"
    _ -> Error "ElaborateRequest: not an elaboration request"
  where
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
        writeElaborated elaborated `bindResult` \ast ->
            maybe (Ok Nothing) (mapResult Just . writeInterface) iface `bindResult` \ifaceText ->
                Ok (unlines (["tersus-elaborated 1", "accepted"] ++ block ast ++ maybe ["interface none"] (\t -> "interface" : block t) ifaceText))
    Refused message -> Ok (unlines ["tersus-elaborated 1", "refused " ++ quote message])
    RefusedInterface message -> Ok (unlines ["tersus-elaborated 1", "interfaceRefused " ++ quote message])
    NotModelled what -> Ok (unlines ["tersus-elaborated 1", "unmodelled " ++ quote what])
  where
    block text = ("data " ++ show (length (lines text))) : lines text

readResponse :: String -> Result Response String
readResponse text = case lines text of
    ["tersus-elaborated 1", line] -> strictTokenize line `bindResult` \ts -> case ts of
        [Word "refused", Str message] -> Ok (Refused message)
        [Word "interfaceRefused", Str message] -> Ok (RefusedInterface message)
        [Word "unmodelled", Str what] -> Ok (NotModelled what)
        _ -> Error "ElaborateRequest: malformed response"
    "tersus-elaborated 1" : "accepted" : rest ->
        blocks 1 rest `bindResult` \(astTexts, rest') -> case (astTexts, rest') of
            ([ast], ["interface none"]) -> readElaborated ast `bindResult` \e -> Ok (Accepted e Nothing)
            ([ast], "interface" : more) ->
                blocks 1 more `bindResult` \(ifaceTexts, rest'') -> case (ifaceTexts, rest'') of
                    ([ifaceText], []) -> readElaborated ast `bindResult` \e -> readInterface ifaceText `bindResult` \i -> Ok (Accepted e (Just i))
                    _ -> Error "ElaborateRequest: malformed interface"
            _ -> Error "ElaborateRequest: malformed response"
    _ -> Error "ElaborateRequest: not an elaboration response"

-- The Haskell elaborator answering a request, as PackageCompile, LibPackage and Compile elaborate a module
respond :: Request -> Response
respond rq = case elaborateWith env (rqStatements rq) of
    Error e -> Refused e
    Ok (elaborated@(Elaborated stmts _), state) -> case rqExtraction rq of
        NoInterface -> Accepted elaborated Nothing
        ModuleInterfaceOf -> extracted extractInterface stmts state elaborated
        LibInterfaceOf -> extracted extractLibInterface stmts state elaborated
  where
    merged = mergeInterfacesImportEnv (rqInterfaces rq)
    -- (a generic constructor's owner is a compiler-only physical view, not something a program imports)
    owners = Map.fromList [(owner, [ctor]) | iface <- rqInterfaces rq, (ctor, (owner, _)) <- Map.toList (ifCtors iface), ctor == owner]
    viewed = if rqLibrary rq then merged{ieTypes = Map.union (ieTypes merged) owners} else merged
    env = if rqPredeclare rq then predeclareOwnEnv viewed else viewed
    extracted extract stmts state elaborated = case extract (rqModule rq) (rqStatements rq) stmts state of
        Error e -> RefusedInterface e
        Ok iface -> Accepted elaborated (Just iface)

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

-- n blocks, each `data <line count>` and that many lines, and the lines after them
blocks :: Int -> [String] -> Result ([String], [String]) String
blocks 0 rest = Ok ([], rest)
blocks n (header : rest) =
    wordAfter "data" header `bindResult` countOf `bindResult` \count ->
        let (block, after) = splitAt count rest
         in if length block < count
                then Error "ElaborateRequest: a block is cut short"
                else blocks (n - 1) after `bindResult` \(more, rest') -> Ok (unlines block : more, rest')
blocks _ [] = Error "ElaborateRequest: missing data block"

firstLine :: [String] -> Result (String, [String]) String
firstLine ls = case ls of
    l : rest -> Ok (l, rest)
    [] -> Error "ElaborateRequest: the request ends early"

mapAll :: (a -> Result b String) -> [a] -> Result [b] String
mapAll f = foldr (\x rest -> f x `bindResult` \y -> rest `bindResult` \ys -> Ok (y : ys)) (Ok [])
