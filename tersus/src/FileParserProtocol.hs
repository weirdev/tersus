module FileParserProtocol
    ( writeFileRequest
    , readFileRequest
    , writeParsedFile
    , readParsedFile
    , writeImportPrefixRequest
    , writeDeclarationNamesRequest
    , readImportPrefix
    , readDeclarationNames
    ) where

import Control.Monad (replicateM, unless)
import qualified Data.Map.Strict as Map
import qualified Text.Parsec as Reader

import qualified AstData
import DataCodec
import Parse (Decls (..), Import (..), ParsedFile (..), emptyDecls)
import Types
import Utils (Result (..), bindResult, decodeUtf8, encodeUtf8, flatResultMap, mapResult)

type Records = Reader.Parsec String ()

writeFileRequest :: Decls -> String -> Result String String
writeFileRequest = writeRequest "tersus-file-parse 1"

writeImportPrefixRequest :: String -> Result String String
writeImportPrefixRequest = writeRequest "tersus-import-prefix 1" emptyDecls

writeDeclarationNamesRequest :: String -> Result String String
writeDeclarationNamesRequest = writeRequest "tersus-declaration-names 1" emptyDecls

writeRequest :: String -> Decls -> String -> Result String String
writeRequest tag decls source =
    writeDecls decls `bindResult` \declRecords ->
    let bytes = encodeUtf8 source
     in validUtf8 bytes `bindResult` \_ ->
        Ok (tag ++ "\n" ++ declRecords ++ "source " ++ show (length bytes) ++ "\n" ++ bytes)

readImportPrefix :: String -> Result [Import] String
readImportPrefix = readEnvelope (header "tersus-imports 1" >> records "imports" importP)

readDeclarationNames :: String -> Result [Name] String
readDeclarationNames = readEnvelope (header "tersus-names 1" >> records "names" (expect "name" >> name))

readFileRequest :: String -> Result (Decls, String) String
readFileRequest = readEnvelope $ do
    header "tersus-file-parse 1"
    decls <- readDecls
    source <- body "source" >>= fromResult . validUtf8
    pure (decls, source)

writeParsedFile :: ParsedFile -> Decls -> Result String String
writeParsedFile parsed decls =
    writeDecls decls `bindResult` \declRecords ->
    validatedImports (fileImports parsed) `bindResult` \imports ->
    AstData.writeParsed (fileBody parsed) `bindResult` \ast ->
    Ok ("tersus-file 1\nimports " ++ show (length imports) ++ "\n" ++ unlines imports ++ declRecords ++ "ast\n" ++ ast)
  where
    validatedImports = flatResultMap $ \imp ->
        let line = unwords ("import" : show (importLine imp) : show (importColumn imp) : namesTokens (importPath imp) ++ optionalTokens quoteOne (importAlias imp) ++ optionalTokens namesTokens (importNames imp))
         in parseRecord importP line `bindResult` \_ -> Ok line
    quoteOne n = [quote n]

readParsedFile :: String -> Result (ParsedFile, Decls) String
readParsedFile = readEnvelope $ do
    header "tersus-file 1"
    imports <- records "imports" importP
    decls <- readDecls
    record (expect "ast")
    payload <- Reader.getInput
    ast <- fromResult (AstData.readParsed payload)
    Reader.setInput ""
    pure (ParsedFile imports ast, decls)

namesTokens :: [String] -> [String]
namesTokens ns = show (length ns) : map quote ns

optionalTokens :: (a -> [String]) -> Maybe a -> [String]
optionalTokens _ Nothing = ["none"]
optionalTokens put (Just value) = "some" : put value

writeDecls :: Decls -> Result String String
writeDecls decls =
    let text = unlines $
            ["decls"]
            ++ mapRecords "ctors" "ctor" namesTokens (declCtors decls)
            ++ mapRecords "types" "type" namesTokens (declTypes decls)
            ++ [unwords ("self" : optionalTokens (pure . quote) (declSelf decls))]
            ++ [unwords ("selfType" : optionalTokens typeTokens (declSelfType decls))]
            ++ [unwords ("typeParams" : namesTokens (declTypeParams decls))]
            ++ mapRecords "generics" "generic" namesTokens (declGenerics decls)
            ++ [unwords ("implParams" : namesTokens (declImplParams decls))]
            ++ ["ownClone " ++ boolToken (declOwnClone decls), "locate " ++ boolToken (declLocate decls)]
            ++ mapRecords "fieldTypes" "fields" fieldsTokens (declFieldTypes decls)
            ++ ["endDecls"]
     in readEnvelope readDecls text `bindResult` \_ -> Ok text
  where
    mapRecords label tag put values =
        (label ++ " " ++ show (Map.size values)) : [unwords (tag : quote key : put value) | (key, value) <- Map.toAscList values]
    fieldsTokens fields = show (length fields) : concat [quote field : typeTokens ty | (field, ty) <- fields]
    boolToken True = "true"
    boolToken False = "false"

readDecls :: Records Decls
readDecls = do
    record (expect "decls")
    ctors <- mapping "ctors" "ctor" namesP
    types <- mapping "types" "type" namesP
    self <- record (expect "self" >> optionalP name)
    selfType <- record (expect "selfType" >> optionalP safeTypeP)
    typeParams <- record (expect "typeParams" >> namesP)
    generics <- mapping "generics" "generic" namesP
    implParams <- record (expect "implParams" >> namesP)
    ownClone <- record (expect "ownClone" >> boolP)
    locate <- record (expect "locate" >> boolP)
    fieldTypes <- mapping "fieldTypes" "fields" (listP ((,) <$> name <*> safeTypeP))
    record (expect "endDecls")
    pure (Decls ctors types self selfType typeParams generics implParams ownClone locate fieldTypes)

mapping :: String -> String -> P a -> Records (Map.Map Name a)
mapping label tag valueP = do
    entries <- records label (expect tag >> ((,) <$> name <*> valueP))
    let values = Map.fromList entries
    unless (Map.size values == length entries) (Reader.parserFail ("duplicate key in " ++ label))
    pure values

importP :: P Import
importP = do
    expect "import"
    line <- positiveP
    column <- positiveP
    path <- nonemptyNamesP
    alias <- optionalP name
    names <- optionalP nonemptyNamesP
    pure (Import path alias names line column)

namesP :: P [Name]
namesP = listP name

nonemptyNamesP :: P [Name]
nonemptyNamesP = do
    ns <- namesP
    if null ns then failP "an import path or selected-name list must not be empty" else pure ns

optionalP :: P a -> P (Maybe a)
optionalP parser = word >>= \tag -> case tag of
    "none" -> pure Nothing
    "some" -> Just <$> parser
    _ -> failP "expected none or some"

boolP :: P Bool
boolP = word >>= \tag -> case tag of
    "true" -> pure True
    "false" -> pure False
    _ -> failP "expected true or false"

nonnegativeP :: P Int
nonnegativeP = do
    n <- integer
    if n >= 0 && n <= toInteger (maxBound :: Int)
        then pure (fromInteger n)
        else failP "negative or overflowing count/index"

positiveP :: P Int
positiveP = do
    n <- nonnegativeP
    if n > 0 then pure n else failP "a source position must be positive"

listP :: P a -> P [a]
listP parser = do
    n <- nonnegativeP
    P $ \ts -> if n > length ts
        then Error "count exceeds available tokens"
        else runP (replicateM n parser) ts

safeTypeP :: P Type
safeTypeP = word >>= \tag -> case tag of
    "list" -> TList <$> safeTypeP
    "array" -> TArrayOf <$> safeTypeP <*> safeSizeP
    "box" -> TBox <$> safeTypeP
    "addr" -> TAddr <$> safeTypeP
    "uninit" -> TUninit <$> safeTypeP
    "block" -> TBlock <$> safeTypeP
    "fn" -> TFn <$> listP safeTypeP <*> safeTypeP
    "named" -> TNamed <$> name <*> listP safeArgP
    "variant" -> TVariant <$> name
    "var" -> TVar <$> nonnegativeP
    "forall" -> TForall <$> namesP <*> namesP <*> safeTypeP
    "param" -> TParam <$> name
    "ref" -> TRef <$> safeTypeP
    "mutref" -> TMutRef <$> safeTypeP
    _ -> P $ \ts -> mapResult (\ty -> (ty, ts)) (parseLine typeP [Word tag])

safeArgP :: P Arg
safeArgP = word >>= \tag -> case tag of
    "size" -> ArgSize <$> safeSizeP
    "type" -> ArgType <$> safeTypeP
    _ -> failP ("not an argument: " ++ tag)

safeSizeP :: P Size
safeSizeP = word >>= \tag -> case tag of
    "c" -> SizeConst <$> integer
    "any" -> pure SizeAny
    "p" -> SizeParam <$> name
    "v" -> SizeVar <$> nonnegativeP
    _ -> failP ("not a size: " ++ tag)

records :: String -> P a -> Records [a]
records label parser = do
    n <- record (expect label >> nonnegativeP)
    available <- length <$> Reader.getInput
    if n > available then Reader.parserFail "count exceeds available records" else replicateM n (record parser)

body :: String -> Records String
body label = do
    n <- record (expect label >> nonnegativeP)
    remaining <- Reader.getInput
    let (bytes, rest) = splitAt n remaining
    unless (length bytes == n) (Reader.parserFail ("truncated " ++ label ++ " body"))
    Reader.setInput rest
    pure bytes

header :: String -> Records ()
header expected = do
    _ <- Reader.string (expected ++ "\n")
    pure ()

record :: P a -> Records a
record parser = do
    remaining <- Reader.getInput
    let (line, rest) = break (== '\n') remaining
    unless (length (take 1000001 line) <= 1000000) (Reader.parserFail "oversized metadata record")
    case rest of
        '\n' : more -> do
            Reader.setInput more
            fromResult (parseRecord parser line)
        _ -> Reader.parserFail "unterminated metadata record"

parseRecord :: P a -> String -> Result a String
parseRecord parser line
    | null line || length (take 1000001 line) > 1000000 = Error "empty or oversized metadata record"
    | otherwise = strictTokenize line `bindResult` parseLine parser

validUtf8 :: String -> Result String String
validUtf8 bytes
    | any ((> 255) . fromEnum) bytes || encodeUtf8 text /= bytes = Error "invalid UTF-8 source bytes"
    | otherwise = Ok text
  where
    text = decodeUtf8 bytes

fromResult :: Result a String -> Records a
fromResult (Ok value) = pure value
fromResult (Error err) = Reader.parserFail err

readEnvelope :: Records a -> String -> Result a String
readEnvelope parser input = case Reader.parse (parser <* Reader.eof) "FileParserProtocol" input of
    Left err -> Error (show err)
    Right value -> Ok value
