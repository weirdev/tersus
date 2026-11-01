module AstData (writeParsed, readParsed, writeElaborated, readElaborated) where

import Control.Monad (replicateM)
import qualified Data.Map.Strict as Map
import qualified Data.IntSet as IS
import Data.List (foldl')
import BuiltinRegistry (builtinRegistry, entryInstances)
import DataCodec
import Syntax
import Types
import TypeCheck (Elaborated (..))
import Utils

type Build = (Int, [String])

emit :: String -> [String] -> Build -> (Int, Build)
emit tag fields (n, records) = (n, (n + 1, unwords (tag : fields) : records))

writeParsed :: [Statement] -> Result String String
writeParsed ss = finish "parsed" (putStatements ss (0, []))

writeElaborated :: Elaborated -> Result String String
writeElaborated (Elaborated ss ts) =
    let (s, b) = putStatements ss (0, [])
        (t, b') = putTypes ts b
     in finish "elaborated" (emit "Elaborated" [show s, show t] b')

finish :: String -> (Int, Build) -> Result String String
finish stage (root, (_, records)) =
    checkRecords records `bindResult` \() ->
        Ok (unlines (("tersus-ast 1 " ++ stage) : reverse records ++ ["root " ++ show root]))
  where
    checkRecords [] = Ok ()
    checkRecords (line : rest)
        | null line || length line > 1000000 = Error "AstData: empty or oversized record"
        | otherwise = strictTokenize line `bindResult` \ts ->
            case ts of
                Word "Type" : fields -> parseLine astTypeP fields `bindResult` \_ -> checkRecords rest
                Word "Size" : fields -> parseLine sizeP fields `bindResult` \_ -> checkRecords rest
                _ -> checkRecords rest

putName :: String -> Build -> (Int, Build)
putName s b = foldl' part (emit "NameEnd" [] b) (reverse (chunks s))
  where
    chunks [] = []
    chunks xs = let (a, more) = splitAt 512 xs in a : chunks more
    part (tailId, state) text = emit "NamePart" [quote text, show tailId] state

putType :: Type -> Build -> (Int, Build)
putType t = emit "Type" (typeTokens t)

putSize :: Size -> Build -> (Int, Build)
putSize s = emit "Size" (sizeTokens s)

fixedBuiltins :: [(String, BuiltinFunct)]
fixedBuiltins = [(show b, b) | entry <- builtinRegistry, b <- entryInstances entry, not (parameterized b)]
  where
    parameterized b = case b of
        Ctor{} -> True
        Field{} -> True
        Is{} -> True
        Project{} -> True
        Cast{} -> True
        ToWord{} -> True
        Rel{} -> True
        _ -> False

data Node = NName String | NType Type | NSize Size | NElaborated Elaborated
    | NValue (Value)
    | NBody (FunctBody)
    | NExpression (Expression)
    | NTermination (Termination)
    | NValidation (ValidationStatement)
    | NProof (VariableProof)
    | NRule (RwRule)
    | NStatement (Statement)
    | NSignature (Signature)
    | NTraitFn (TraitFn)
    | NBound (Bound)
    | NField ((Variable, Type))
    | NVariant ((Name, [(Variable, Type)]))
    | NValueField ((Variable, Value))
    | NArg (Arg)
    | NOptName (Maybe Name)
    | NOptTermination (Maybe Termination)
    | NBuiltin (BuiltinFunct)
    | NNames ([String])
    | NValues ([Value])
    | NStatements ([Statement])
    | NExpressions ([Expression])
    | NValidations ([ValidationStatement])
    | NProofs ([VariableProof])
    | NFields ([(Variable, Type)])
    | NVariants ([(Name, [(Variable, Type)])])
    | NValueFields ([(Variable, Value)])
    | NTypes ([Type])
    | NArgs ([Arg])
    | NTraitFns ([TraitFn])
    | NBounds ([Bound])

putValue :: Value -> Build -> (Int, Build)
putValue value b0 = case value of
    VInt n ->
        let (r0, b1) = putName (show n) b0
         in emit "VInt" [show r0] b1
    VList xs ->
        let (r0, b1) = putValues xs b0
         in emit "VList" [show r0] b1
    VBool b -> emit "VBool" [(if b then "true" else "false")] b0
    VData n xs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putValueFields xs b1
         in emit "VData" [show r0, show r1] b2
    VFnRef n ->
        let (r0, b1) = putName n b0
         in emit "VFnRef" [show r0] b1
    VFunct ps ins outs body exports ->
        let (r0, b1) = putNames ps b0
            (r1, b2) = putValidations ins b1
            (r2, b3) = putValidations outs b2
            (r3, b4) = putBody body b3
            (r4, b5) = putProofs exports b4
         in emit "VFunct" [show r0, show r1, show r2, show r3, show r4] b5

putBody :: FunctBody -> Build -> (Int, Build)
putBody value b0 = case value of
    NativeFunct sig term stmts ->
        let (r0, b1) = putSignature sig b0
            (r1, b2) = putOptTermination term b1
            (r2, b3) = putStatements stmts b2
         in emit "NativeFunct" [show r0, show r1, show r2] b3
    BuiltinFunct b ->
        let (r0, b1) = putBuiltin b b0
         in emit "BuiltinFunct" [show r0] b1

putExpression :: Expression -> Build -> (Int, Build)
putExpression value b0 = case value of
    Val v ->
        let (r0, b1) = putValue v b0
         in emit "Val" [show r0] b1
    Var n ->
        let (r0, b1) = putName n b0
         in emit "Var" [show r0] b1
    F f xs ->
        let (r0, b1) = putExpression f b0
            (r1, b2) = putExpressions xs b1
         in emit "F" [show r0, show r1] b2

putTermination :: Termination -> Build -> (Int, Build)
putTermination value b0 = case value of
    Shrinks e ->
        let (r0, b1) = putExpression e b0
         in emit "Shrinks" [show r0] b1
    Counting e ->
        let (r0, b1) = putExpression e b0
         in emit "Counting" [show r0] b1
    Parts e ->
        let (r0, b1) = putExpression e b0
         in emit "Parts" [show r0] b1
    MayDiverge -> emit "MayDiverge" [] b0
    Recursing t ->
        let (r0, b1) = putOptTermination t b0
         in emit "Recursing" [show r0] b1

putValidation :: ValidationStatement -> Build -> (Int, Build)
putValidation value b0 = case value of
    Rewrite r ->
        let (r0, b1) = putRule r b0
         in emit "Rewrite" [show r0] b1
    ProofAssert p ->
        let (r0, b1) = putProof p b0
         in emit "ProofAssert" [show r0] b1
    AssignProofVar n e ->
        let (r0, b1) = putName n b0
            (r1, b2) = putExpression e b1
         in emit "AssignProofVar" [show r0, show r1] b2
    Assume p ->
        let (r0, b1) = putProof p b0
         in emit "Assume" [show r0] b1

putProof :: VariableProof -> Build -> (Int, Build)
putProof value b0 = case value of
    FApp f xs ->
        let (r0, b1) = putProof f b0
            (r1, b2) = putProofs xs b1
         in emit "FApp" [show r0, show r1] b2
    ATerm n ->
        let (r0, b1) = putName n b0
         in emit "ATerm" [show r0] b1
    CTerm v ->
        let (r0, b1) = putValue v b0
         in emit "CTerm" [show r0] b1
    Forall n gs b ->
        let (r0, b1) = putName n b0
            (r1, b2) = putProofs gs b1
            (r2, b3) = putProof b b2
         in emit "Forall" [show r0, show r1, show r2] b3
    BVar n ->
        let (r0, b1) = putName n b0
         in emit "BVar" [show r0] b1

putRule :: RwRule -> Build -> (Int, Build)
putRule value b0 = case value of
    Refl p ->
        let (r0, b1) = putProof p b0
         in emit "Refl" [show r0] b1
    Eval n ->
        let (r0, b1) = putName n b0
         in emit "Eval" [show r0] b1
    EvalAll -> emit "EvalAll" [] b0
    CheckGtZero p ->
        let (r0, b1) = putProof p b0
         in emit "CheckGtZero" [show r0] b1
    CheckRel p ->
        let (r0, b1) = putProof p b0
         in emit "CheckRel" [show r0] b1
    UserRewrite n xs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putProofs xs b1
         in emit "UserRewrite" [show r0, show r1] b2

putStatement :: Statement -> Build -> (Int, Build)
putStatement value b0 = case value of
    Assign n e ->
        let (r0, b1) = putName n b0
            (r1, b2) = putExpression e b1
         in emit "Assign" [show r0, show r1] b2
    AssignDeref a b ->
        let (r0, b1) = putExpression a b0
            (r1, b2) = putExpression b b1
         in emit "AssignDeref" [show r0, show r1] b2
    Let n e ->
        let (r0, b1) = putName n b0
            (r1, b2) = putExpression e b1
         in emit "Let" [show r0, show r1] b2
    Return e ->
        let (r0, b1) = putExpression e b0
         in emit "Return" [show r0] b1
    ValidationStatement v ->
        let (r0, b1) = putValidation v b0
         in emit "ValidationStatement" [show r0] b1
    StructDef n ps fs vs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putNames ps b1
            (r2, b3) = putFields fs b2
            (r3, b4) = putValidations vs b3
         in emit "StructDef" [show r0, show r1, show r2, show r3] b4
    EnumDef n vs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putVariants vs b1
         in emit "EnumDef" [show r0, show r1] b2
    AxiomDef n ps ins outs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putNames ps b1
            (r2, b3) = putValidations ins b2
            (r3, b4) = putValidations outs b3
         in emit "AxiomDef" [show r0, show r1, show r2, show r3] b4
    ProofDef n ps ins outs body ->
        let (r0, b1) = putName n b0
            (r1, b2) = putNames ps b1
            (r2, b3) = putValidations ins b2
            (r3, b4) = putValidations outs b3
            (r4, b5) = putValidations body b4
         in emit "ProofDef" [show r0, show r1, show r2, show r3, show r4] b5
    Block xs ->
        let (r0, b1) = putStatements xs b0
         in emit "Block" [show r0] b1
    If e a b ->
        let (r0, b1) = putExpression e b0
            (r1, b2) = putStatements a b1
            (r2, b3) = putStatements b b2
         in emit "If" [show r0, show r1, show r2] b3
    While e vs t xs ->
        let (r0, b1) = putExpression e b0
            (r1, b2) = putValidations vs b1
            (r2, b3) = putOptTermination t b2
            (r3, b4) = putStatements xs b3
         in emit "While" [show r0, show r1, show r2, show r3] b4
    TraitDef n ps fs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putNames ps b1
            (r2, b3) = putTraitFns fs b2
         in emit "TraitDef" [show r0, show r1, show r2] b3
    ImplDef trait args n ty bs xs ->
        let (r0, b1) = putOptName trait b0
            (r1, b2) = putArgs args b1
            (r2, b3) = putName n b2
            (r3, b4) = putType ty b3
            (r4, b5) = putBounds bs b4
            (r5, b6) = putStatements xs b5
         in emit "ImplDef" [show r0, show r1, show r2, show r3, show r4, show r5] b6
    BoundedDef bs s ->
        let (r0, b1) = putBounds bs b0
            (r1, b2) = putStatement s b1
         in emit "BoundedDef" [show r0, show r1] b2
    Mark line col -> emit "Mark" [show line, show col] b0
    CopyDef n ->
        let (r0, b1) = putName n b0
         in emit "CopyDef" [show r0] b1
    LinearDef n ->
        let (r0, b1) = putName n b0
         in emit "LinearDef" [show r0] b1
    ExternDef n ->
        let (r0, b1) = putName n b0
         in emit "ExternDef" [show r0] b1
    DropDef n ->
        let (r0, b1) = putName n b0
         in emit "DropDef" [show r0] b1
    Dissolve n ->
        let (r0, b1) = putName n b0
         in emit "Dissolve" [show r0] b1

putSignature :: Signature -> Build -> (Int, Build)
putSignature value b0 = case value of
    Signature ts ret ss ps ws fs ->
        let (r0, b1) = putTypes ts b0
            (r1, b2) = putType ret b1
            (r2, b3) = putNames ss b2
            (r3, b4) = putNames ps b3
            (r4, b5) = putNames ws b4
            (r5, b6) = putNames fs b5
         in emit "Signature" [show r0, show r1, show r2, show r3, show r4, show r5] b6

putTraitFn :: TraitFn -> Build -> (Int, Build)
putTraitFn value b0 = case value of
    TraitFn n ps sig ins outs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putNames ps b1
            (r2, b3) = putSignature sig b2
            (r3, b4) = putValidations ins b3
            (r4, b5) = putValidations outs b4
         in emit "TraitFn" [show r0, show r1, show r2, show r3, show r4] b5

putBound :: Bound -> Build -> (Int, Build)
putBound value b0 = case value of
    (p, n, ts) ->
        let (r0, b1) = putName p b0
            (r1, b2) = putName n b1
            (r2, b3) = putTypes ts b2
         in emit "Bound" [show r0, show r1, show r2] b3

putField :: (Variable, Type) -> Build -> (Int, Build)
putField value b0 = case value of
    (n, ty) ->
        let (r0, b1) = putName n b0
            (r1, b2) = putType ty b1
         in emit "Field" [show r0, show r1] b2

putVariant :: (Name, [(Variable, Type)]) -> Build -> (Int, Build)
putVariant value b0 = case value of
    (n, fs) ->
        let (r0, b1) = putName n b0
            (r1, b2) = putFields fs b1
         in emit "Variant" [show r0, show r1] b2

putValueField :: (Variable, Value) -> Build -> (Int, Build)
putValueField value b0 = case value of
    (n, v) ->
        let (r0, b1) = putName n b0
            (r1, b2) = putValue v b1
         in emit "ValueField" [show r0, show r1] b2

putArg :: Arg -> Build -> (Int, Build)
putArg value b0 = case value of
    ArgSize s ->
        let (r0, b1) = putSize s b0
         in emit "ArgSize" [show r0] b1
    ArgType t ->
        let (r0, b1) = putType t b0
         in emit "ArgType" [show r0] b1

putOptName :: Maybe Name -> Build -> (Int, Build)
putOptName value b0 = case value of
    Nothing -> emit "NoName" [] b0
    Just n ->
        let (r0, b1) = putName n b0
         in emit "SomeName" [show r0] b1

putOptTermination :: Maybe Termination -> Build -> (Int, Build)
putOptTermination value b0 = case value of
    Nothing -> emit "NoTermination" [] b0
    Just t ->
        let (r0, b1) = putTermination t b0
         in emit "SomeTermination" [show r0] b1

putBuiltin :: BuiltinFunct -> Build -> (Int, Build)
putBuiltin value b0 = case value of
    Ctor n args fs ->
        let (r0, b1) = putName n b0
            (r1, b2) = putArgs args b1
            (r2, b3) = putNames fs b2
         in emit "Ctor" [show r0, show r1, show r2] b3
    Field owner n ->
        let (r0, b1) = putOptName owner b0
            (r1, b2) = putName n b1
         in emit "FieldBuiltin" [show r0, show r1] b2
    Is n ->
        let (r0, b1) = putName n b0
         in emit "Is" [show r0] b1
    Project n f ->
        let (r0, b1) = putName n b0
            (r1, b2) = putName f b1
         in emit "Project" [show r0, show r1] b2
    Cast n ->
        let (r0, b1) = putName n b0
         in emit "Cast" [show r0] b1
    ToWord signed bits -> emit "ToWord" [(if signed then "true" else "false"), show bits] b0
    Rel r -> emit "Rel" [show r] b0
    b -> emit "Primitive" [quote (show b)] b0

putNames :: [String] -> Build -> (Int, Build)
putNames xs b = foldl' cons (emit "NamesEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putName x state
         in emit "NamesCons" [show headId, show tailId] state'

putValues :: [Value] -> Build -> (Int, Build)
putValues xs b = foldl' cons (emit "ValuesEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putValue x state
         in emit "ValuesCons" [show headId, show tailId] state'

putStatements :: [Statement] -> Build -> (Int, Build)
putStatements xs b = foldl' cons (emit "StatementsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putStatement x state
         in emit "StatementsCons" [show headId, show tailId] state'

putExpressions :: [Expression] -> Build -> (Int, Build)
putExpressions xs b = foldl' cons (emit "ExpressionsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putExpression x state
         in emit "ExpressionsCons" [show headId, show tailId] state'

putValidations :: [ValidationStatement] -> Build -> (Int, Build)
putValidations xs b = foldl' cons (emit "ValidationsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putValidation x state
         in emit "ValidationsCons" [show headId, show tailId] state'

putProofs :: [VariableProof] -> Build -> (Int, Build)
putProofs xs b = foldl' cons (emit "ProofsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putProof x state
         in emit "ProofsCons" [show headId, show tailId] state'

putFields :: [(Variable, Type)] -> Build -> (Int, Build)
putFields xs b = foldl' cons (emit "FieldsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putField x state
         in emit "FieldsCons" [show headId, show tailId] state'

putVariants :: [(Name, [(Variable, Type)])] -> Build -> (Int, Build)
putVariants xs b = foldl' cons (emit "VariantsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putVariant x state
         in emit "VariantsCons" [show headId, show tailId] state'

putValueFields :: [(Variable, Value)] -> Build -> (Int, Build)
putValueFields xs b = foldl' cons (emit "ValueFieldsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putValueField x state
         in emit "ValueFieldsCons" [show headId, show tailId] state'

putTypes :: [Type] -> Build -> (Int, Build)
putTypes xs b = foldl' cons (emit "TypesEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putType x state
         in emit "TypesCons" [show headId, show tailId] state'

putArgs :: [Arg] -> Build -> (Int, Build)
putArgs xs b = foldl' cons (emit "ArgsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putArg x state
         in emit "ArgsCons" [show headId, show tailId] state'

putTraitFns :: [TraitFn] -> Build -> (Int, Build)
putTraitFns xs b = foldl' cons (emit "TraitFnsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putTraitFn x state
         in emit "TraitFnsCons" [show headId, show tailId] state'

putBounds :: [Bound] -> Build -> (Int, Build)
putBounds xs b = foldl' cons (emit "BoundsEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putBound x state
         in emit "BoundsCons" [show headId, show tailId] state'

readParsed :: String -> Result [Statement] String
readParsed text = decode "parsed" text `bindResult` \n -> case n of
    NStatements ss -> Ok ss
    _ -> Error "AstData: wrong root kind"

readElaborated :: String -> Result Elaborated String
readElaborated text = decode "elaborated" text `bindResult` \n -> case n of
    NElaborated e -> Ok e
    _ -> Error "AstData: wrong root kind"

decode :: String -> String -> Result Node String
decode stage text = case lines text of
    header : rest | header == "tersus-ast 1 " ++ stage -> case reverse rest of
        root : reversed -> doResult (reverse reversed) root
        _ -> Error "AstData: missing root"
    _ -> Error "AstData: unknown header"
  where
    doResult records root = foldRecords (Map.empty, IS.empty) records `bindResult` \(nodes, uses) ->
        strictLine (expect "root" >> int) root `bindResult` \r ->
        case Map.lookup r nodes of
            Just node | r == Map.size nodes - 1 && all (\i -> IS.member i uses == (i /= r)) [0 .. r] -> Ok node
            _ -> Error "AstData: dangling root or extra records"
    foldRecords state [] = Ok state
    foldRecords state (line : rest) = add state line `bindResult` \next -> foldRecords next rest
    add (nodes, uses) line = strictLine (nodeP nodes) line `bindResult` \(node, refs) ->
        if any (`IS.member` uses) refs || length refs /= IS.size (IS.fromList refs)
            then Error "AstData: reused reference"
            else Ok (Map.insert (Map.size nodes) node nodes, foldl' (flip IS.insert) uses refs)

strictLine :: P a -> String -> Result a String
strictLine p line
    | null line || length line > 1000000 = Error "AstData: empty or oversized record"
    | otherwise = strictTokenize line `bindResult` parseLine p

ref :: Map.Map Int Node -> (Node -> Maybe a) -> P (a, Int)
ref nodes project = do
    i <- int
    case Map.lookup i nodes >>= project of
        Just value -> pure (value, i)
        Nothing -> failP "AstData: dangling, cyclic, forward or wrong-kind reference"

nodeP :: Map.Map Int Node -> P (Node, [Int])
nodeP nodes = word >>= \tag -> case tag of
    "NameEnd" -> pure (NName "", [])
    "NamePart" -> do
        s <- name
        (tailName, r) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NName (s ++ tailName), [r])
    "Type" -> astTypeP >>= \t -> pure (NType t, [])
    "Size" -> sizeP >>= \s -> pure (NSize s, [])
    "Primitive" -> do
        n <- name
        case lookup n fixedBuiltins of
            Just b -> pure (NBuiltin b, [])
            _ -> failP "AstData: unknown primitive"
    "Elaborated" -> do
        (ss, s) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        (ts, t) <- ref nodes (\node -> case node of NTypes payload -> Just payload; _ -> Nothing)
        pure (NElaborated (Elaborated ss ts), [s, t])
    "VInt" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        number <- decimalP n
        pure (NValue (VInt number), [r0])
    "VList" -> do
        (xs, r0) <- ref nodes (\node -> case node of NValues payload -> Just payload; _ -> Nothing)
        pure (NValue (VList xs), [r0])
    "VBool" -> do
        b <- boolP
        pure (NValue (VBool b), [])
    "VData" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (xs, r1) <- ref nodes (\node -> case node of NValueFields payload -> Just payload; _ -> Nothing)
        pure (NValue (VData n xs), [r0, r1])
    "VFnRef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NValue (VFnRef n), [r0])
    "VFunct" -> do
        (ps, r0) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (ins, r1) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        (outs, r2) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        (body, r3) <- ref nodes (\node -> case node of NBody payload -> Just payload; _ -> Nothing)
        (exports, r4) <- ref nodes (\node -> case node of NProofs payload -> Just payload; _ -> Nothing)
        pure (NValue (VFunct ps ins outs body exports), [r0, r1, r2, r3, r4])
    "NativeFunct" -> do
        (sig, r0) <- ref nodes (\node -> case node of NSignature payload -> Just payload; _ -> Nothing)
        (term, r1) <- ref nodes (\node -> case node of NOptTermination payload -> Just payload; _ -> Nothing)
        (stmts, r2) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        pure (NBody (NativeFunct sig term stmts), [r0, r1, r2])
    "BuiltinFunct" -> do
        (b, r0) <- ref nodes (\node -> case node of NBuiltin payload -> Just payload; _ -> Nothing)
        pure (NBody (BuiltinFunct b), [r0])
    "Val" -> do
        (v, r0) <- ref nodes (\node -> case node of NValue payload -> Just payload; _ -> Nothing)
        pure (NExpression (Val v), [r0])
    "Var" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NExpression (Var n), [r0])
    "F" -> do
        (f, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        (xs, r1) <- ref nodes (\node -> case node of NExpressions payload -> Just payload; _ -> Nothing)
        pure (NExpression (F f xs), [r0, r1])
    "Shrinks" -> do
        (e, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NTermination (Shrinks e), [r0])
    "Counting" -> do
        (e, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NTermination (Counting e), [r0])
    "Parts" -> do
        (e, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NTermination (Parts e), [r0])
    "MayDiverge" -> do
        pure (NTermination (MayDiverge), [])
    "Recursing" -> do
        (t, r0) <- ref nodes (\node -> case node of NOptTermination payload -> Just payload; _ -> Nothing)
        pure (NTermination (Recursing t), [r0])
    "Rewrite" -> do
        (r, r0) <- ref nodes (\node -> case node of NRule payload -> Just payload; _ -> Nothing)
        pure (NValidation (Rewrite r), [r0])
    "ProofAssert" -> do
        (p, r0) <- ref nodes (\node -> case node of NProof payload -> Just payload; _ -> Nothing)
        pure (NValidation (ProofAssert p), [r0])
    "AssignProofVar" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (e, r1) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NValidation (AssignProofVar n e), [r0, r1])
    "Assume" -> do
        (p, r0) <- ref nodes (\node -> case node of NProof payload -> Just payload; _ -> Nothing)
        pure (NValidation (Assume p), [r0])
    "FApp" -> do
        (f, r0) <- ref nodes (\node -> case node of NProof payload -> Just payload; _ -> Nothing)
        (xs, r1) <- ref nodes (\node -> case node of NProofs payload -> Just payload; _ -> Nothing)
        pure (NProof (FApp f xs), [r0, r1])
    "ATerm" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NProof (ATerm n), [r0])
    "CTerm" -> do
        (v, r0) <- ref nodes (\node -> case node of NValue payload -> Just payload; _ -> Nothing)
        pure (NProof (CTerm v), [r0])
    "Forall" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (gs, r1) <- ref nodes (\node -> case node of NProofs payload -> Just payload; _ -> Nothing)
        (b, r2) <- ref nodes (\node -> case node of NProof payload -> Just payload; _ -> Nothing)
        pure (NProof (Forall n gs b), [r0, r1, r2])
    "BVar" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NProof (BVar n), [r0])
    "Refl" -> do
        (p, r0) <- ref nodes (\node -> case node of NProof payload -> Just payload; _ -> Nothing)
        pure (NRule (Refl p), [r0])
    "Eval" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NRule (Eval n), [r0])
    "EvalAll" -> do
        pure (NRule (EvalAll), [])
    "CheckGtZero" -> do
        (p, r0) <- ref nodes (\node -> case node of NProof payload -> Just payload; _ -> Nothing)
        pure (NRule (CheckGtZero p), [r0])
    "CheckRel" -> do
        (p, r0) <- ref nodes (\node -> case node of NProof payload -> Just payload; _ -> Nothing)
        pure (NRule (CheckRel p), [r0])
    "UserRewrite" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (xs, r1) <- ref nodes (\node -> case node of NProofs payload -> Just payload; _ -> Nothing)
        pure (NRule (UserRewrite n xs), [r0, r1])
    "Assign" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (e, r1) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NStatement (Assign n e), [r0, r1])
    "AssignDeref" -> do
        (a, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        (b, r1) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NStatement (AssignDeref a b), [r0, r1])
    "Let" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (e, r1) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NStatement (Let n e), [r0, r1])
    "Return" -> do
        (e, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NStatement (Return e), [r0])
    "ValidationStatement" -> do
        (v, r0) <- ref nodes (\node -> case node of NValidation payload -> Just payload; _ -> Nothing)
        pure (NStatement (ValidationStatement v), [r0])
    "StructDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ps, r1) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (fs, r2) <- ref nodes (\node -> case node of NFields payload -> Just payload; _ -> Nothing)
        (vs, r3) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        pure (NStatement (StructDef n ps fs vs), [r0, r1, r2, r3])
    "EnumDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (vs, r1) <- ref nodes (\node -> case node of NVariants payload -> Just payload; _ -> Nothing)
        pure (NStatement (EnumDef n vs), [r0, r1])
    "AxiomDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ps, r1) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (ins, r2) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        (outs, r3) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        pure (NStatement (AxiomDef n ps ins outs), [r0, r1, r2, r3])
    "ProofDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ps, r1) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (ins, r2) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        (outs, r3) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        (body, r4) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        pure (NStatement (ProofDef n ps ins outs body), [r0, r1, r2, r3, r4])
    "Block" -> do
        (xs, r0) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        pure (NStatement (Block xs), [r0])
    "If" -> do
        (e, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        (a, r1) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        (b, r2) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        pure (NStatement (If e a b), [r0, r1, r2])
    "While" -> do
        (e, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        (vs, r1) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        (t, r2) <- ref nodes (\node -> case node of NOptTermination payload -> Just payload; _ -> Nothing)
        (xs, r3) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        pure (NStatement (While e vs t xs), [r0, r1, r2, r3])
    "TraitDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ps, r1) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (fs, r2) <- ref nodes (\node -> case node of NTraitFns payload -> Just payload; _ -> Nothing)
        pure (NStatement (TraitDef n ps fs), [r0, r1, r2])
    "ImplDef" -> do
        (trait, r0) <- ref nodes (\node -> case node of NOptName payload -> Just payload; _ -> Nothing)
        (args, r1) <- ref nodes (\node -> case node of NArgs payload -> Just payload; _ -> Nothing)
        (n, r2) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ty, r3) <- ref nodes (\node -> case node of NType payload -> Just payload; _ -> Nothing)
        (bs, r4) <- ref nodes (\node -> case node of NBounds payload -> Just payload; _ -> Nothing)
        (xs, r5) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        pure (NStatement (ImplDef trait args n ty bs xs), [r0, r1, r2, r3, r4, r5])
    "BoundedDef" -> do
        (bs, r0) <- ref nodes (\node -> case node of NBounds payload -> Just payload; _ -> Nothing)
        (s, r1) <- ref nodes (\node -> case node of NStatement payload -> Just payload; _ -> Nothing)
        pure (NStatement (BoundedDef bs s), [r0, r1])
    "Mark" -> do
        line <- int
        col <- int
        pure (NStatement (Mark line col), [])
    "CopyDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NStatement (CopyDef n), [r0])
    "LinearDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NStatement (LinearDef n), [r0])
    "ExternDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NStatement (ExternDef n), [r0])
    "DropDef" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NStatement (DropDef n), [r0])
    "Dissolve" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NStatement (Dissolve n), [r0])
    "Signature" -> do
        (ts, r0) <- ref nodes (\node -> case node of NTypes payload -> Just payload; _ -> Nothing)
        (ret, r1) <- ref nodes (\node -> case node of NType payload -> Just payload; _ -> Nothing)
        (ss, r2) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (ps, r3) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (ws, r4) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (fs, r5) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        pure (NSignature (Signature ts ret ss ps ws fs), [r0, r1, r2, r3, r4, r5])
    "TraitFn" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ps, r1) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        (sig, r2) <- ref nodes (\node -> case node of NSignature payload -> Just payload; _ -> Nothing)
        (ins, r3) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        (outs, r4) <- ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
        pure (NTraitFn (TraitFn n ps sig ins outs), [r0, r1, r2, r3, r4])
    "Bound" -> do
        (p, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (n, r1) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ts, r2) <- ref nodes (\node -> case node of NTypes payload -> Just payload; _ -> Nothing)
        pure (NBound ((p, n, ts)), [r0, r1, r2])
    "Field" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (ty, r1) <- ref nodes (\node -> case node of NType payload -> Just payload; _ -> Nothing)
        pure (NField ((n, ty)), [r0, r1])
    "Variant" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (fs, r1) <- ref nodes (\node -> case node of NFields payload -> Just payload; _ -> Nothing)
        pure (NVariant ((n, fs)), [r0, r1])
    "ValueField" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (v, r1) <- ref nodes (\node -> case node of NValue payload -> Just payload; _ -> Nothing)
        pure (NValueField ((n, v)), [r0, r1])
    "ArgSize" -> do
        (s, r0) <- ref nodes (\node -> case node of NSize payload -> Just payload; _ -> Nothing)
        pure (NArg (ArgSize s), [r0])
    "ArgType" -> do
        (t, r0) <- ref nodes (\node -> case node of NType payload -> Just payload; _ -> Nothing)
        pure (NArg (ArgType t), [r0])
    "NoName" -> do
        pure (NOptName (Nothing), [])
    "SomeName" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NOptName (Just n), [r0])
    "NoTermination" -> do
        pure (NOptTermination (Nothing), [])
    "SomeTermination" -> do
        (t, r0) <- ref nodes (\node -> case node of NTermination payload -> Just payload; _ -> Nothing)
        pure (NOptTermination (Just t), [r0])
    "Ctor" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (args, r1) <- ref nodes (\node -> case node of NArgs payload -> Just payload; _ -> Nothing)
        (fs, r2) <- ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
        pure (NBuiltin (Ctor n args fs), [r0, r1, r2])
    "FieldBuiltin" -> do
        (owner, r0) <- ref nodes (\node -> case node of NOptName payload -> Just payload; _ -> Nothing)
        (n, r1) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NBuiltin (Field owner n), [r0, r1])
    "Is" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NBuiltin (Is n), [r0])
    "Project" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        (f, r1) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NBuiltin (Project n f), [r0, r1])
    "Cast" -> do
        (n, r0) <- ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
        pure (NBuiltin (Cast n), [r0])
    "ToWord" -> do
        signed <- boolP
        bits <- integer
        pure (NBuiltin (ToWord signed bits), [])
    "Rel" -> do
        r <- relP
        pure (NBuiltin (Rel r), [])
    "NamesEnd" -> pure (NNames [], [])
    "NamesCons" -> do
        (x, a) <- ref nodes (\node -> case node of NName v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NNames v -> Just v; _ -> Nothing)
        pure (NNames (x : xs), [a, b])
    "ValuesEnd" -> pure (NValues [], [])
    "ValuesCons" -> do
        (x, a) <- ref nodes (\node -> case node of NValue v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NValues v -> Just v; _ -> Nothing)
        pure (NValues (x : xs), [a, b])
    "StatementsEnd" -> pure (NStatements [], [])
    "StatementsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NStatement v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NStatements v -> Just v; _ -> Nothing)
        pure (NStatements (x : xs), [a, b])
    "ExpressionsEnd" -> pure (NExpressions [], [])
    "ExpressionsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NExpression v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NExpressions v -> Just v; _ -> Nothing)
        pure (NExpressions (x : xs), [a, b])
    "ValidationsEnd" -> pure (NValidations [], [])
    "ValidationsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NValidation v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NValidations v -> Just v; _ -> Nothing)
        pure (NValidations (x : xs), [a, b])
    "ProofsEnd" -> pure (NProofs [], [])
    "ProofsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NProof v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NProofs v -> Just v; _ -> Nothing)
        pure (NProofs (x : xs), [a, b])
    "FieldsEnd" -> pure (NFields [], [])
    "FieldsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NField v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NFields v -> Just v; _ -> Nothing)
        pure (NFields (x : xs), [a, b])
    "VariantsEnd" -> pure (NVariants [], [])
    "VariantsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NVariant v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NVariants v -> Just v; _ -> Nothing)
        pure (NVariants (x : xs), [a, b])
    "ValueFieldsEnd" -> pure (NValueFields [], [])
    "ValueFieldsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NValueField v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NValueFields v -> Just v; _ -> Nothing)
        pure (NValueFields (x : xs), [a, b])
    "TypesEnd" -> pure (NTypes [], [])
    "TypesCons" -> do
        (x, a) <- ref nodes (\node -> case node of NType v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NTypes v -> Just v; _ -> Nothing)
        pure (NTypes (x : xs), [a, b])
    "ArgsEnd" -> pure (NArgs [], [])
    "ArgsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NArg v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NArgs v -> Just v; _ -> Nothing)
        pure (NArgs (x : xs), [a, b])
    "TraitFnsEnd" -> pure (NTraitFns [], [])
    "TraitFnsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NTraitFn v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NTraitFns v -> Just v; _ -> Nothing)
        pure (NTraitFns (x : xs), [a, b])
    "BoundsEnd" -> pure (NBounds [], [])
    "BoundsCons" -> do
        (x, a) <- ref nodes (\node -> case node of NBound v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NBounds v -> Just v; _ -> Nothing)
        pure (NBounds (x : xs), [a, b])
    _ -> failP ("AstData: unknown tag " ++ tag)

astTypeP :: P Type
astTypeP = word >>= \w -> case w of
    "int" -> pure TInt
    "byte" -> pure TByte
    "bool" -> pure TBool
    "i8" -> pure (TWord True 8)
    "i16" -> pure (TWord True 16)
    "i32" -> pure (TWord True 32)
    "u16" -> pure (TWord False 16)
    "u32" -> pure (TWord False 32)
    "list" -> TList <$> astTypeP
    "array" -> TArrayOf <$> astTypeP <*> sizeP
    "box" -> TBox <$> astTypeP
    "addr" -> TAddr <$> astTypeP
    "block" -> TBlock <$> astTypeP
    "uninit" -> TUninit <$> astTypeP
    "ref" -> TRef <$> astTypeP
    "mutref" -> TMutRef <$> astTypeP
    "fn" -> countP >>= \n -> TFn <$> replicateM n astTypeP <*> astTypeP
    "named" -> TNamed <$> name <*> (countP >>= \n -> replicateM n astArgP)
    "variant" -> TVariant <$> name
    "var" -> TVar <$> int
    "param" -> TParam <$> name
    "forall" -> TForall <$> (countP >>= \n -> replicateM n name) <*> (countP >>= \n -> replicateM n name) <*> astTypeP
    _ -> failP "AstData: unknown type"

astArgP :: P Arg
astArgP = word >>= \w -> case w of
    "size" -> ArgSize <$> sizeP
    "type" -> ArgType <$> astTypeP
    _ -> failP "AstData: unknown type argument"

countP :: P Int
countP = P $ \ts -> runP int ts `bindResult` \(n, rest) ->
    if n >= 0 && n <= length rest then Ok (n, rest) else Error "AstData: malformed count"

boolP :: P Bool
boolP = word >>= \w -> case w of
    "true" -> pure True
    "false" -> pure False
    _ -> failP "AstData: malformed boolean"

relP :: P Rel
relP = word >>= \w -> maybe (failP "AstData: malformed relation") pure (lookup w [(show r, r) | r <- [Eq, NotEq, Lt, Gt, LtEq, GtEq]])

decimalP :: String -> P Integer
decimalP s = case decimal s of
    Just n -> pure n
    _ -> failP "AstData: malformed integer"
