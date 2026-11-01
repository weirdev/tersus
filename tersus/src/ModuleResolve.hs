module ModuleResolve
    ( DeclKind (..)
    , DeclInfo (..)
    , packageDecls
    , fileDecls
    , canonicalForFile
    , rewriteFileReferences
    ) where

import Data.List (intercalate, isInfixOf, isPrefixOf, nub, stripPrefix)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Modules
import Parse (Import (..), ParsedFile (..), splitPath)
import TersusTypes

data DeclKind = KindType | KindVariant | KindTrait | KindFunction | KindAxiom | KindProof
    deriving (Eq, Show)

data DeclInfo = DeclInfo
    { diCanonical :: Name
    , diKind :: DeclKind
    , diLocal :: Name
    , diFileStem :: String
    , diModule :: ModuleId
    , diTraitFns :: [Name]
    }
    deriving (Eq, Show)

splitOn :: String -> String -> [String]
splitOn needle = go
  where
    go text
        | needle `isPrefixOf` text = "" : go (drop (length needle) text)
        | otherwise = case text of
            c : rest -> case go rest of
                [] -> [[c]]
                chunk : chunks -> (c : chunk) : chunks
            [] -> [[]]

canonicalForFile :: LoadedPackage -> LoadedFile -> Name -> Name
canonicalForFile pkg file local = canonicalName (fileIdentity pkg file) local

fileIdentity :: LoadedPackage -> LoadedFile -> ModuleIdentity
fileIdentity pkg file = fileModuleIdentity (packagePackageName pkg) (maybe "" id (moduleName (loadedFileModule file))) (loadedFileStem file ++ ".tersus")

variantCanonical :: LoadedPackage -> LoadedFile -> Name -> Name
variantCanonical pkg file variant = case splitOn "::" variant of
    owner : rest@(_ : _) -> canonicalForFile pkg file owner ++ "::" ++ intercalate "::" rest
    _ -> canonicalForFile pkg file variant

implCanonical :: LoadedPackage -> LoadedFile -> Name -> Name
implCanonical pkg file name = case stripPrefix "<" name of
    Just rest ->
        let (inside, after) = break (== '>') rest
            function = drop 3 after
         in case breakOn " as " inside of
                Just (owner, trait) -> implFunctionName (canonicalOwner owner) (Just (canonicalForFile pkg file trait)) function
                Nothing -> implFunctionName (canonicalOwner inside) Nothing function
    Nothing -> canonicalForFile pkg file name
  where
    canonicalOwner owner = case instanceOf owner of
        Just (base, _) -> canonicalForFile pkg file base
        Nothing -> canonicalForFile pkg file owner
    breakOn needle = go ""
      where
        go acc text
            | needle `isPrefixOf` text = Just (reverse acc, drop (length needle) text)
            | otherwise = case text of
                c : rest' -> go (c : acc) rest'
                [] -> Nothing

fileDecls :: LoadedPackage -> LoadedFile -> [DeclInfo]
fileDecls pkg file = concatMap top (fileBody (loadedParsed file))
  where
    modu = loadedFileModule file
    stem = loadedFileStem file
    info kind local canonical = DeclInfo canonical kind local stem modu []
    top stmt = case stmt of
        StructDef name _ _ _ -> [info KindType name (canonicalForFile pkg file name)]
        EnumDef name variants -> info KindType name (canonicalForFile pkg file name) : [info KindVariant variant (variantCanonical pkg file variant) | (variant, _) <- variants]
        TraitDef name _ functions -> [DeclInfo (canonicalForFile pkg file name) KindTrait name stem modu (map traitFnName functions)]
        Assign name (Val VFunct{})
            | "<" `isPrefixOf` name -> [info KindFunction name (implCanonical pkg file name)]
            | otherwise -> [info KindFunction name (canonicalForFile pkg file name)]
        BoundedDef _ inner -> top inner
        AxiomDef name _ _ _ -> [info KindAxiom name (canonicalForFile pkg file name)]
        ProofDef name _ _ _ _ -> [info KindProof name (canonicalForFile pkg file name)]
        ImplDef _ _ _ _ _ functions -> concatMap top functions
        _ -> []

packageDecls :: LoadedPackage -> [DeclInfo]
packageDecls pkg = [decl | modu <- packageModules pkg, file <- loadedModuleFiles modu, decl <- fileDecls pkg file]

collapsedStem :: LoadedPackage -> ModuleId -> Maybe String
collapsedStem pkg modu = case [file | m <- packageModules pkg, loadedModuleId m == modu, file <- loadedModuleFiles m] of
    [file] | loadedFileStem file == maybe (packagePackageName pkg) id (moduleName modu) -> Just (loadedFileStem file)
    _ -> Nothing

moduleSegment :: LoadedPackage -> ModuleId -> String
moduleSegment pkg (ModuleId p Nothing) = p
moduleSegment _ (ModuleId _ (Just name)) = name

prefixesFor :: LoadedPackage -> LoadedFile -> DeclInfo -> [[String]]
prefixesFor pkg current decl
    | diModule decl == loadedFileModule current && diFileStem decl == loadedFileStem current = [[]]
    | otherwise = nub (concatMap importPrefixes covering)
  where
    covering = [ri | ri <- loadedImports current, resolvedTargetModule ri == diModule decl, covers ri]
    covers ri = case resolvedLevel ri of
        LevelModule -> True
        LevelFile -> resolvedTargetFile ri == Just (diFileStem decl)
        LevelSymbol -> resolvedTargetSymbol ri == Just (diLocal decl) || resolvedTargetSymbol ri == Just (takeWhile (/= ':') (diLocal decl))
    importPrefixes ri =
        let imp = resolvedImport ri
            localParts = splitPath (diLocal decl)
            fileSeg = diFileStem decl
            modu = diModule decl
            pkgName = modulePackage modu
            modSegs = maybe [] (\name -> [name]) (moduleName modu)
            isCollapsed = collapsedStem pkg modu == Just fileSeg
            alias = importAlias imp
            bareForListed = case importNames imp of
                Just names -> diLocal decl `elem` names || takeWhile (/= ':') (diLocal decl) `elem` names
                Nothing -> False
            levelPrefixes = case resolvedLevel ri of
                LevelSymbol -> [[]]
                LevelFile -> [[fileSeg]] ++ maybe [] (\name -> [[name]]) alias
                LevelModule ->
                    let full = [pkgName] ++ modSegs ++ [fileSeg]
                        shortened = [moduleSegment pkg modu, fileSeg]
                        collapsedFull = [pkgName] ++ modSegs
                        collapsedShort = [moduleSegment pkg modu]
                        bases = [shortened, full] ++ (if isCollapsed then [collapsedShort, collapsedFull] else [])
                        aliased = maybe [] (\name -> [[name, fileSeg]] ++ (if isCollapsed then [[name]] else [])) alias
                     in bases ++ aliased
         in (if bareForListed || resolvedLevel ri == LevelSymbol then [[]] else []) ++ levelPrefixes

spellingsFor :: LoadedPackage -> LoadedFile -> DeclInfo -> [String]
spellingsFor pkg current decl = [intercalate "::" (prefix ++ splitPath (diLocal decl)) | prefix <- prefixesFor pkg current decl]

potentialSpellings :: LoadedPackage -> DeclInfo -> [String]
potentialSpellings pkg decl =
    let modu = diModule decl
        fileSeg = diFileStem decl
        pkgName = modulePackage modu
        modSegs = maybe [] (\name -> [name]) (moduleName modu)
        isCollapsed = collapsedStem pkg modu == Just fileSeg
        prefixes = [[], [fileSeg], [moduleSegment pkg modu, fileSeg], [pkgName] ++ modSegs ++ [fileSeg]] ++ (if isCollapsed then [[moduleSegment pkg modu], [pkgName] ++ modSegs] else [])
     in [intercalate "::" (prefix ++ splitPath (diLocal decl)) | prefix <- nub prefixes]

data Maps = Maps
    { mapTypes :: Map.Map String (Name, Bool)
    , mapTraits :: Map.Map String Name
    , mapFns :: Map.Map String Name
    , mapProofFns :: Map.Map String Name
    , mapCtors :: Map.Map String Name
    , potentialTypes :: Map.Map String Name
    , potentialFns :: Map.Map String Name
    , potentialCtors :: Map.Map String Name
    }

type Build a = Either String a

insertChecked :: String -> String -> Name -> Map.Map String Name -> Build (Map.Map String Name)
insertChecked what spelling canonical existing = case Map.lookup spelling existing of
    Just other
        | other == canonical -> Right existing
        | otherwise -> Left ("name " ++ spelling ++ " is ambiguous in this file: it names both " ++ other ++ " and " ++ canonical ++ " (" ++ what ++ "); rename one or import only one of them")
    Nothing -> Right (Map.insert spelling canonical existing)

insertTypeChecked :: String -> (Name, Bool) -> Map.Map String (Name, Bool) -> Build (Map.Map String (Name, Bool))
insertTypeChecked spelling value existing = case Map.lookup spelling existing of
    Just other
        | other == value -> Right existing
        | otherwise -> Left ("name " ++ spelling ++ " is ambiguous in this file: it names both " ++ fst other ++ " and " ++ fst value ++ " (types); rename one or import only one of them")
    Nothing -> Right (Map.insert spelling value existing)

insertIfAbsent :: String -> Name -> Map.Map String Name -> Build (Map.Map String Name)
insertIfAbsent spelling canonical existing = Right (Map.insertWith (\old _ -> old) spelling canonical existing)

buildMaps :: LoadedPackage -> LoadedFile -> Build Maps
buildMaps pkg current = do
    let allDecls = packageDecls pkg
        visible = [decl | decl <- allDecls, not (null (prefixesFor pkg current decl))]
    types0 <- foldBuild (\m decl -> foldBuild (\mm spelling -> insertTypeChecked spelling (typeTarget decl) mm) m (spellingsFor pkg current decl)) Map.empty [decl | decl <- visible, diKind decl `elem` [KindType, KindVariant]]
    traits0 <- foldBuild (\m decl -> foldBuild (\mm spelling -> insertChecked "traits" spelling (diCanonical decl) mm) m (spellingsFor pkg current decl)) Map.empty [decl | decl <- visible, diKind decl == KindTrait]
    ctors0 <- foldBuild (\m decl -> foldBuild (\mm spelling -> insertChecked "constructors" spelling (diCanonical decl) mm) m (spellingsFor pkg current decl)) Map.empty [decl | decl <- visible, diKind decl `elem` [KindType, KindVariant]]
    fns0 <- foldBuild addPlain Map.empty visible
    fns1 <- foldBuild addAssociated fns0 visible
    let proofDecls = [decl | decl <- visible, diKind decl `elem` [KindFunction, KindAxiom, KindProof]]
    proofs0 <- foldBuild (\m decl -> foldBuild (\mm spelling -> insertChecked "proof names" spelling (diCanonical decl) mm) m (spellingsFor pkg current decl)) Map.empty proofDecls
    proofs1 <- foldBuild addAssociatedProof proofs0 visible
    potentialsTypes <- foldBuild (\m decl -> foldBuild (\mm spelling -> insertIfAbsent spelling (diCanonical decl) mm) m (potentialSpellings pkg decl)) Map.empty [decl | decl <- allDecls, diKind decl `elem` [KindType, KindVariant]]
    potentialsFns <- foldBuild (\m decl -> foldBuild (\mm spelling -> insertIfAbsent spelling (diCanonical decl) mm) m (potentialSpellings pkg decl)) Map.empty [decl | decl <- allDecls, diKind decl `elem` [KindFunction, KindAxiom, KindProof]]
    potentialsCtors <- foldBuild (\m decl -> foldBuild (\mm spelling -> insertIfAbsent spelling (diCanonical decl) mm) m (potentialSpellings pkg decl)) Map.empty [decl | decl <- allDecls, diKind decl `elem` [KindType, KindVariant]]
    Right (Maps types0 traits0 fns1 proofs1 ctors0 potentialsTypes potentialsFns potentialsCtors)
  where
    typeTarget decl = (diCanonical decl, diKind decl == KindVariant)
    foldBuild _ initial [] = Right initial
    foldBuild f initial (item : rest) = case f initial item of
        Left err -> Left err
        Right next -> foldBuild f next rest
    addPlain m decl
        | diKind decl == KindFunction && not ("<" `isPrefixOf` diLocal decl) = foldBuild (\mm spelling -> insertChecked "functions" spelling (diCanonical decl) mm) m (spellingsFor pkg current decl)
        | otherwise = Right m
    addAssociated m decl = case diKind decl of
        KindTrait -> foldBuild (\mm fnName -> foldBuild (\mmm traitSpelling -> insertChecked "trait functions" (traitSpelling ++ "::" ++ fnName) (diCanonical decl ++ "::" ++ fnName) mmm) mm (spellingsFor pkg current decl)) m (diTraitFns decl)
        KindFunction
            | "<" `isPrefixOf` diLocal decl ->
                let (ownerLocal, fnName) = implOwnerFn (diLocal decl)
                 in case [owner | owner <- allDeclsOf pkg, diKind owner == KindType, diLocal owner == ownerLocal] of
                        ownerDecl : _ -> foldBuild (\mm ownerSpelling -> insertChecked "associated functions" (ownerSpelling ++ "::" ++ fnName) (ownerCanonicalOf (diCanonical decl) ++ "::" ++ fnName) mm) m (spellingsFor pkg current ownerDecl)
                        [] -> Right m
            | otherwise -> Right m
        _ -> Right m
    addAssociatedProof m decl = addAssociated m decl
    allDeclsOf p = packageDecls p
    implOwnerFn localName =
        let inside = drop 1 (takeWhile (/= '>') localName)
            fnName = drop 3 (dropWhile (/= '>') localName)
            owner = case breakOn " as " inside of
                Just (before, _) -> before
                Nothing -> inside
         in (maybe owner fst (instanceOf owner), fnName)
    ownerCanonicalOf canonicalImpl =
        let inside = drop 1 (takeWhile (/= '>') canonicalImpl)
         in case breakOn " as " inside of
                Just (before, _) -> before
                Nothing -> inside
    breakOn needle = go ""
      where
        go acc text
            | needle `isPrefixOf` text = Just (reverse acc, drop (length needle) text)
            | otherwise = case text of
                c : rest -> go (c : acc) rest
                [] -> Nothing

rewriteFileReferences :: LoadedPackage -> LoadedFile -> [Statement] -> Either String [Statement]
rewriteFileReferences pkg current statements = do
    maps <- buildMaps pkg current
    (rewritten, _) <- rewriteStatements maps Set.empty Set.empty statements
    Right rewritten

uncovered :: String -> Name -> Map.Map String Name -> Either String a
uncovered kind name potentials = case Map.lookup name potentials of
    Just canonical -> Left ("name " ++ name ++ " is " ++ canonical ++ ", which is declared in another file or module: use it here only through a covering import (a file import as file::Name, a module import as module::file::Name or fully qualified, or a symbol import as the bare name)")
    Nothing -> Left ("unknown " ++ kind ++ " " ++ name)

lookupTypeTarget :: Maps -> Set.Set Name -> Name -> Either String (Name, Bool)
lookupTypeTarget maps typeParams name
    | name == "Self" = Right (name, False)
    | baseOf name `Set.member` typeParams = Right (name, False)
    | otherwise = case Map.lookup name (mapTypes maps) of
        Just target -> Right target
        Nothing -> case Map.lookup (baseOf name) (mapTypes maps) of
            Just (canonical, isVariant) -> Right (rebuild canonical isVariant)
            Nothing
                | "::" `isInfixOf` name || name `Map.member` potentialTypes maps -> uncovered "type" name (potentialTypes maps)
                | otherwise -> Right (name, False)
  where
    baseOf text = maybe text fst (instanceOf text)
    rebuild canonical isVariant = case instanceOf name of
        Just (_, args) -> (instanceName canonical args, isVariant)
        Nothing -> (canonical, isVariant)

rewriteType :: Maps -> Set.Set Name -> Type -> Either String Type
rewriteType maps typeParams ty = case ty of
    TNamed name -> do
        (canonical, isVariant) <- lookupTypeTarget maps typeParams name
        case instanceOf name of
            Just (_, args) -> do
                args' <- mapM rewriteArg args
                Right (if isVariant then TVariant (instanceName (baseName canonical) args') else TNamed (instanceName (baseName canonical) args'))
            Nothing -> Right (if isVariant then TVariant canonical else TNamed canonical)
      where
        baseName canonical = maybe canonical fst (instanceOf canonical)
        rewriteArg (ArgType inner) = ArgType <$> rewriteType maps typeParams inner
        rewriteArg other = Right other
    TVariant name -> do
        (canonical, isVariant) <- lookupTypeTarget maps typeParams name
        Right (if isVariant then TVariant canonical else TNamed canonical)
    TList inner -> TList <$> rewriteType maps typeParams inner
    TArrayOf inner size -> (\inner' -> TArrayOf inner' size) <$> rewriteType maps typeParams inner
    TBox inner -> TBox <$> rewriteType maps typeParams inner
    TAddr inner -> TAddr <$> rewriteType maps typeParams inner
    TBlock inner -> TBlock <$> rewriteType maps typeParams inner
    TUninit inner -> TUninit <$> rewriteType maps typeParams inner
    TRef inner -> TRef <$> rewriteType maps typeParams inner
    TMutRef inner -> TMutRef <$> rewriteType maps typeParams inner
    TFn args ret -> TFn <$> mapM (rewriteType maps typeParams) args <*> rewriteType maps typeParams ret
    TForall sizes types inner -> rewriteType maps (typeParams `Set.union` Set.fromList types) inner >>= \inner' -> Right (TForall sizes types inner')
    other -> Right other

rewriteNamedString :: Maps -> Set.Set Name -> Name -> Either String Name
rewriteNamedString maps typeParams name = case instanceOf name of
    Just (base, args) -> do
        (canonical, _) <- lookupTypeTarget maps typeParams base
        args' <- mapM rewriteArg args
        Right (instanceName canonical args')
      where
        rewriteArg (ArgType inner) = ArgType <$> rewriteType maps typeParams inner
        rewriteArg other = Right other
    Nothing -> fst <$> lookupTypeTarget maps typeParams name

rewriteTraitName :: Maps -> Name -> Either String Name
rewriteTraitName maps name = case Map.lookup name (mapTraits maps) of
    Just canonical -> Right canonical
    Nothing -> Right name

rewriteCtorName :: Maps -> Name -> Either String Name
rewriteCtorName maps name = case Map.lookup name (mapCtors maps) of
    Just canonical -> Right canonical
    Nothing
        | "::" `isInfixOf` name || name `Map.member` potentialCtors maps -> uncovered "struct or variant" name (potentialCtors maps)
        | otherwise -> Right name

rewriteFnName :: Maps -> Set.Set Variable -> Name -> Either String Name
rewriteFnName maps bound name
    | "." `isPrefixOf` name = Right name
    | "<" `isPrefixOf` name = rewriteImplFull maps name
    | otherwise = case Map.lookup name (mapFns maps) of
        Just canonical
            | not ("::" `isInfixOf` name) && name `Set.member` bound -> Right name
            | otherwise -> Right canonical
        Nothing
            | "::" `isInfixOf` name -> case Map.lookup name (potentialFns maps) of
                Just _ -> uncovered "function" name (potentialFns maps)
                Nothing -> Right name
            | otherwise -> Right name

rewriteImplFull :: Maps -> Name -> Either String Name
rewriteImplFull maps name = case stripPrefix "<" name of
    Just rest ->
        let (inside, after) = break (== '>') rest
            function = drop 3 after
         in case breakOn " as " inside of
                Just (owner, trait) -> do
                    owner' <- rewriteNamedString maps Set.empty owner
                    trait' <- rewriteTraitName maps trait
                    Right (implFunctionName owner' (Just trait') function)
                Nothing -> do
                    owner' <- rewriteNamedString maps Set.empty inside
                    Right (implFunctionName owner' Nothing function)
    Nothing -> Right name
  where
    breakOn needle = go ""
      where
        go acc text
            | needle `isPrefixOf` text = Just (reverse acc, drop (length needle) text)
            | otherwise = case text of
                c : rest' -> go (c : acc) rest'
                [] -> Nothing

rewriteValue :: Maps -> Set.Set Variable -> Set.Set Name -> Value -> Either String Value
rewriteValue maps bound typeParams value = case value of
    VData name fields -> do
        name' <- rewriteCtorName maps name
        fields' <- mapM (\(field, fieldValue) -> (,) field <$> rewriteValue maps bound typeParams fieldValue) fields
        Right (VData name' fields')
    VList values -> VList <$> mapM (rewriteValue maps bound typeParams) values
    VFnRef name -> VFnRef <$> rewriteFnName maps bound name
    VFunct params ins outs body exported -> do
        (ins', outs', body') <- rewriteFunctParts maps bound typeParams params ins outs body
        Right (VFunct params ins' outs' body' exported)
    other -> Right other

rewriteFunctParts :: Maps -> Set.Set Variable -> Set.Set Name -> [Variable] -> [ValidationStatement] -> [ValidationStatement] -> FunctBody -> Either String ([ValidationStatement], [ValidationStatement], FunctBody)
rewriteFunctParts maps bound typeParams params ins outs body = do
    let bound' = bound `Set.union` Set.fromList params
    ins' <- rewriteValidations maps bound' typeParams ins
    outs' <- rewriteValidations maps bound' typeParams outs
    body' <- case body of
        NativeFunct signature termination statements -> do
            signature' <- rewriteSignature maps (typeParams `Set.union` Set.fromList (signatureTypes signature)) signature
            termination' <- rewriteTermination maps bound' typeParams termination
            (statements', _) <- rewriteStatements maps bound' (typeParams `Set.union` Set.fromList (signatureTypes signature)) statements
            Right (NativeFunct signature' termination' statements')
        BuiltinFunct builtin -> case builtin of
            Ctor name fields -> rewriteCtorBuiltin maps name fields
            Field owner field -> do
                owner' <- maybe (Right Nothing) (\name -> Just <$> rewriteNamedString maps typeParams name) owner
                Right (BuiltinFunct (Field owner' field))
            Is name -> do
                name' <- rewriteCtorName maps name
                Right (BuiltinFunct (Is name'))
            Cast name -> do
                name' <- rewriteCtorName maps name
                Right (BuiltinFunct (Cast name'))
            Project name field -> do
                name' <- rewriteCtorName maps name
                Right (BuiltinFunct (Project name' field))
            other -> Right (BuiltinFunct other)
    Right (ins', outs', body')
  where
    signatureTypes (Signature _ _ sizes types _ _) = types ++ sizes
    rewriteCtorBuiltin maps' name fields = do
        name' <- rewriteCtorName maps' name
        Right (BuiltinFunct (Ctor name' fields))

rewriteSignature :: Maps -> Set.Set Name -> Signature -> Either String Signature
rewriteSignature maps typeParams (Signature params ret sizes types writes from) =
    Signature <$> mapM (rewriteType maps typeParams) params <*> rewriteType maps typeParams ret <*> Right sizes <*> Right types <*> Right writes <*> Right from

rewriteTermination :: Maps -> Set.Set Variable -> Set.Set Name -> Maybe Termination -> Either String (Maybe Termination)
rewriteTermination _ _ _ Nothing = Right Nothing
rewriteTermination maps bound typeParams (Just termination) = Just <$> case termination of
    Shrinks expr -> Shrinks <$> rewriteExpr maps bound typeParams expr
    Counting expr -> Counting <$> rewriteExpr maps bound typeParams expr
    Parts expr -> Parts <$> rewriteExpr maps bound typeParams expr
    other -> Right other

rewriteExpr :: Maps -> Set.Set Variable -> Set.Set Name -> Expression -> Either String Expression
rewriteExpr maps bound typeParams expr = case expr of
    Val value -> Val <$> rewriteValue maps bound typeParams value
    Var name -> Var <$> rewriteFnName maps bound name
    F func args -> F <$> rewriteExpr maps bound typeParams func <*> mapM (rewriteExpr maps bound typeParams) args

rewriteProof :: Maps -> Set.Set Variable -> Set.Set Name -> VariableProof -> Either String VariableProof
rewriteProof maps bound typeParams proof = case proof of
    ATerm var
        | var `Set.member` bound -> Right proof
        | otherwise -> case Map.lookup var (mapProofFns maps) of
            Just canonical -> Right (ATerm canonical)
            Nothing
                | "::" `isInfixOf` var -> case Map.lookup var (potentialFns maps) of
                    Just _ -> uncovered "function in a proof" var (potentialFns maps)
                    Nothing -> Right proof
                | otherwise -> Right proof
    BVar _ -> Right proof
    CTerm value -> CTerm <$> rewriteValue maps bound typeParams value
    FApp func args -> do
        func' <- case func of
            ATerm var
                | not (var `Set.member` bound) -> case Map.lookup var (mapProofFns maps) of
                    Just canonical -> Right (ATerm canonical)
                    Nothing -> rewriteProof maps bound typeParams func
            _ -> rewriteProof maps bound typeParams func
        args' <- mapM (rewriteProof maps bound typeParams) args
        Right (FApp func' args')
    Forall index guards body -> do
        let bound' = Set.insert index bound
        guards' <- mapM (rewriteProof maps bound' typeParams) guards
        body' <- rewriteProof maps bound' typeParams body
        Right (Forall index guards' body')

rewriteValidations :: Maps -> Set.Set Variable -> Set.Set Name -> [ValidationStatement] -> Either String [ValidationStatement]
rewriteValidations maps bound typeParams = go bound
  where
    go _ [] = Right []
    go current (stmt : rest) = do
        (stmt', current') <- rewriteValidation maps current typeParams stmt
        rest' <- go current' rest
        Right (stmt' : rest')

rewriteValidation :: Maps -> Set.Set Variable -> Set.Set Name -> ValidationStatement -> Either String (ValidationStatement, Set.Set Variable)
rewriteValidation maps bound typeParams stmt = case stmt of
    ProofAssert proof -> (\proof' -> (ProofAssert proof', bound)) <$> rewriteProof maps bound typeParams proof
    Assume proof -> (\proof' -> (Assume proof', bound)) <$> rewriteProof maps bound typeParams proof
    AssignProofVar var expr -> do
        expr' <- rewriteExpr maps bound typeParams expr
        Right (AssignProofVar var expr', Set.insert var bound)
    Rewrite rule -> (\rule' -> (Rewrite rule', bound)) <$> case rule of
        Refl proof -> Refl <$> rewriteProof maps bound typeParams proof
        CheckGtZero proof -> CheckGtZero <$> rewriteProof maps bound typeParams proof
        CheckRel proof -> CheckRel <$> rewriteProof maps bound typeParams proof
        UserRewrite name proofs -> do
            name' <- case Map.lookup name (mapProofFns maps) of
                Just canonical -> Right canonical
                Nothing -> Right name
            proofs' <- mapM (rewriteProof maps bound typeParams) proofs
            Right (UserRewrite name' proofs')
        other -> Right other

rewriteStatements :: Maps -> Set.Set Variable -> Set.Set Name -> [Statement] -> Either String ([Statement], Set.Set Variable)
rewriteStatements _ bound _ [] = Right ([], bound)
rewriteStatements maps bound typeParams (stmt : rest) = do
    (stmt', bound') <- rewriteStatement maps bound typeParams stmt
    (rest', bound'') <- rewriteStatements maps bound' typeParams rest
    Right (stmt' : rest', bound'')

rewriteStatement :: Maps -> Set.Set Variable -> Set.Set Name -> Statement -> Either String (Statement, Set.Set Variable)
rewriteStatement maps bound typeParams stmt = case stmt of
    StructDef name params fields invariant -> do
        let typeParams' = typeParams `Set.union` Set.fromList params
        fields' <- mapM (\(field, ty) -> (,) field <$> rewriteType maps typeParams' ty) fields
        invariant' <- rewriteValidations maps (bound `Set.union` Set.fromList (map fst fields)) typeParams' invariant
        Right (StructDef name params fields' invariant', bound)
    EnumDef name variants -> do
        variants' <- mapM (\(variant, fields) -> (,) variant <$> mapM (\(field, ty) -> (,) field <$> rewriteType maps typeParams ty) fields) variants
        Right (EnumDef name variants', bound)
    TraitDef name params functions -> do
        functions' <- mapM rewriteTraitFn functions
        Right (TraitDef name params functions', bound)
      where
        rewriteTraitFn fn = do
            signature' <- rewriteSignature maps (typeParams `Set.union` Set.fromList params) (traitFnSignature fn)
            requires' <- rewriteValidations maps (Set.fromList (traitFnParams fn)) (typeParams `Set.union` Set.fromList params) (traitFnRequires fn)
            ensures' <- rewriteValidations maps (Set.fromList (traitFnParams fn)) (typeParams `Set.union` Set.fromList params) (traitFnEnsures fn)
            Right fn{traitFnSignature = signature', traitFnRequires = requires', traitFnEnsures = ensures'}
    ImplDef trait traitArgs typeName selfName bounds functions -> do
        trait' <- maybe (Right Nothing) (\name -> Just <$> rewriteTraitName maps name) trait
        traitArgs' <- mapM rewriteArg traitArgs
        typeName' <- rewriteNamedString maps typeParams typeName
        selfName' <- rewriteNamedString maps typeParams selfName
        bounds' <- mapM (\(param, traitName, args) -> (,,) param <$> rewriteTraitName maps traitName <*> mapM (rewriteType maps typeParams) args) bounds
        (functions', _) <- rewriteStatements maps bound typeParams functions
        Right (ImplDef trait' traitArgs' typeName' selfName' bounds' functions', bound)
      where
        rewriteArg (ArgType ty) = ArgType <$> rewriteType maps typeParams ty
        rewriteArg other = Right other
    BoundedDef bounds inner -> do
        bounds' <- mapM (\(param, traitName, args) -> (,,) param <$> rewriteTraitName maps traitName <*> mapM (rewriteType maps typeParams) args) bounds
        (inner', bound') <- rewriteStatement maps bound typeParams inner
        Right (BoundedDef bounds' inner', bound')
    AxiomDef name args ins outs -> do
        ins' <- rewriteValidations maps (bound `Set.union` Set.fromList args) typeParams ins
        outs' <- rewriteValidations maps (bound `Set.union` Set.fromList args) typeParams outs
        Right (AxiomDef name args ins' outs', bound)
    ProofDef name args ins outs body -> do
        let bound' = bound `Set.union` Set.fromList args
        ins' <- rewriteValidations maps bound' typeParams ins
        outs' <- rewriteValidations maps bound' typeParams outs
        body' <- rewriteValidations maps bound' typeParams body
        Right (ProofDef name args ins' outs' body', bound)
    Assign name (Val funct@(VFunct params ins outs body exported)) -> do
        (ins', outs', body') <- rewriteFunctParts maps bound typeParams params ins outs body
        Right (Assign name (Val (VFunct params ins' outs' body' exported)), Set.insert name bound)
    Assign name expr -> do
        expr' <- rewriteExpr maps bound typeParams expr
        Right (Assign name expr', Set.insert name bound)
    AssignDeref lhs rhs -> do
        lhs' <- rewriteExpr maps bound typeParams lhs
        rhs' <- rewriteExpr maps bound typeParams rhs
        Right (AssignDeref lhs' rhs', bound)
    Let name expr -> do
        expr' <- rewriteExpr maps bound typeParams expr
        Right (Let name expr', Set.insert name bound)
    Return expr -> (\expr' -> (Return expr', bound)) <$> rewriteExpr maps bound typeParams expr
    ValidationStatement validation -> do
        (validation', bound') <- rewriteValidation maps bound typeParams validation
        Right (ValidationStatement validation', bound')
    Block statements -> do
        (statements', _) <- rewriteStatements maps bound typeParams statements
        Right (Block statements', bound)
    If cond thenStatements elseStatements -> do
        cond' <- rewriteExpr maps bound typeParams cond
        (then', _) <- rewriteStatements maps bound typeParams thenStatements
        (else', _) <- rewriteStatements maps bound typeParams elseStatements
        Right (If cond' then' else', bound)
    While cond invariant termination body -> do
        cond' <- rewriteExpr maps bound typeParams cond
        invariant' <- rewriteValidations maps bound typeParams invariant
        termination' <- rewriteTermination maps bound typeParams termination
        (body', _) <- rewriteStatements maps bound typeParams body
        Right (While cond' invariant' termination' body', bound)
    Dissolve var -> Right (Dissolve var, bound)
    LinearDef name -> (\name' -> (LinearDef name', bound)) <$> rewriteNamedString maps typeParams name
    CopyDef name -> (\name' -> (CopyDef name', bound)) <$> rewriteNamedString maps typeParams name
    DropDef name -> (\name' -> (DropDef name', bound)) <$> rewriteNamedString maps typeParams name
    other -> Right (other, bound)
