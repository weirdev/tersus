module AstData
    ( writeParsed
    , readParsed
    , writeElaborated
    , readElaborated
    , InterfaceRecord (..)
    , FunctionRecord (..)
    , TemplateRecord (..)
    , writeInterfaceRecord
    , readInterfaceRecord
    , BuiltinRecord (..)
    , writeBuiltinTable
    , readBuiltinTable
    ) where

import Control.Monad (replicateM)
import qualified Data.Map.Strict as Map
import qualified Data.IntSet as IS
import Data.List (foldl')
import BuiltinRegistry (NameSpace (..), SigScheme (..), builtinRegistry, entryInstances)
import DataCodec
import Syntax
import Types
import Utils

type Build = (Int, [String])

-- A module interface as plain syntax (InterfaceData converts Interface.ModuleInterface to and from it):
-- each map is its entries in ascending key order and each set its members in ascending order.
data InterfaceRecord = InterfaceRecord
    { irPackage :: Name
    , irModule :: Maybe Name
    , irTypes :: [(Name, [Name])]
    , irCtors :: [(Name, (Name, [(Variable, Type)]))]
    , irGenerics :: [(Name, ([Variable], [(Variable, Type)]))]
    , irInvariants :: [(Name, [ValidationStatement])]
    , irTraits :: [(Name, [TraitFn])]
    , irTraitParams :: [(Name, [Variable])]
    , irFunctions :: [(Name, FunctionRecord)]
    , irImpls :: [(Name, Name)]
    , irAssoc :: [((Name, Name), [Maybe Name])]
    , irImplArgs :: [((Name, Name), (Type, [Arg]))]
    , irImplBounds :: [((Name, Name), [Bound])]
    , irCopies :: [Name]
    , irLinear :: [Name]
    , irDrops :: [Name]
    , irAxioms :: [Statement]
    , irProofs :: [Statement]
    , irExterns :: [Name]
    , irTemplates :: [(Name, TemplateRecord)]
    , irCompanions :: [(Name, [Name])]
    }
    deriving (Show, Eq)

-- Parameters, signature, requires, ensures, termination and exported proofs
data FunctionRecord = FunctionRecord [Variable] Signature [ValidationStatement] [ValidationStatement] (Maybe Termination) [VariableProof]
    deriving (Show, Eq)

-- Bounds, the functions and the return type of the context it was declared in, parameters, signature,
-- requires, ensures, termination and body
data TemplateRecord = TemplateRecord [Bound] [(Variable, Type)] (Maybe Type) [Variable] Signature [ValidationStatement] [ValidationStatement] (Maybe Termination) [Statement]
    deriving (Show, Eq)

-- A builtin as the checker uses it (BuiltinRegistry): the builtin, the names a program calls it by, its
-- signature scheme, and the value the checker writes for it
data BuiltinRecord = BuiltinRecord
    { brBuiltin :: BuiltinFunct
    , brSurface :: [(NameSpace, Name)]
    , brScheme :: SigScheme
    , brValue :: Value
    }
    deriving (Show, Eq)

data Entry
    = ENames Name [Name]
    | ECtor Name Name [(Variable, Type)]
    | EGeneric Name [Variable] [(Variable, Type)]
    | EInvariant Name [ValidationStatement]
    | ETrait Name [TraitFn]
    | EFunction Name FunctionRecord
    | EPair Name Name
    | EAssoc Name Name [Maybe Name]
    | EImplArgs Name Name Type [Arg]
    | EImplBounds Name Name [Bound]
    | ETemplate Name TemplateRecord
    | EType Name Type
    | ESurface NameSpace Name
    | EBuiltin BuiltinRecord

emit :: String -> [String] -> Build -> (Int, Build)
emit tag fields (n, records) = (n, (n + 1, unwords (tag : fields) : records))

writeParsed :: [Statement] -> Result String String
writeParsed ss = finish "parsed" (putStatements ss (0, []))

writeElaborated :: Elaborated -> Result String String
writeElaborated (Elaborated ss ts) =
    let (s, b) = putStatements ss (0, [])
        (t, b') = putTypes ts b
     in finish "elaborated" (emit "Elaborated" [show s, show t] b')

writeInterfaceRecord :: InterfaceRecord -> Result String String
writeInterfaceRecord r = finish "interface" (putInterface r (0, []))

writeBuiltinTable :: [BuiltinRecord] -> Result String String
writeBuiltinTable rs = finish "builtins" (putEntries (map EBuiltin rs) (0, []))

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
    | NEntry Entry
    | NEntries [Entry]
    | NOptNames [Maybe Name]
    | NOptType (Maybe Type)
    | NInterface InterfaceRecord
    | NScheme SigScheme

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
    IfExpr cond yes no ->
        let (r0, b1) = putExpression cond b0
            (r1, b2) = putExpression yes b1
            (r2, b3) = putExpression no b2
         in emit "IfExpr" [show r0, show r1, show r2] b3
    BlockExpr stmts result ->
        let (r0, b1) = putStatements stmts b0
            (r1, b2) = putExpression result b1
         in emit "BlockExpr" [show r0, show r1] b2
    Ascribed expr ty ->
        let (r0, b1) = putExpression expr b0
            (r1, b2) = putType ty b1
         in emit "Ascribed" [show r0, show r1] b2

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

putInterface :: InterfaceRecord -> Build -> (Int, Build)
putInterface r b0 =
    let (r0, b1) = putName (irPackage r) b0
        (r1, b2) = putOptName (irModule r) b1
        (r2, b3) = putEntries [ENames k v | (k, v) <- irTypes r] b2
        (r3, b4) = putEntries [ECtor k o fs | (k, (o, fs)) <- irCtors r] b3
        (r4, b5) = putEntries [EGeneric k ps fs | (k, (ps, fs)) <- irGenerics r] b4
        (r5, b6) = putEntries [EInvariant k vs | (k, vs) <- irInvariants r] b5
        (r6, b7) = putEntries [ETrait k fs | (k, fs) <- irTraits r] b6
        (r7, b8) = putEntries [ENames k v | (k, v) <- irTraitParams r] b7
        (r8, b9) = putEntries [EFunction k f | (k, f) <- irFunctions r] b8
        (r9, b10) = putEntries [EPair a b | (a, b) <- irImpls r] b9
        (r10, b11) = putEntries [EAssoc a b os | ((a, b), os) <- irAssoc r] b10
        (r11, b12) = putEntries [EImplArgs a b t as | ((a, b), (t, as)) <- irImplArgs r] b11
        (r12, b13) = putEntries [EImplBounds a b bs | ((a, b), bs) <- irImplBounds r] b12
        (r13, b14) = putNames (irCopies r) b13
        (r14, b15) = putNames (irLinear r) b14
        (r15, b16) = putNames (irDrops r) b15
        (r16, b17) = putStatements (irAxioms r) b16
        (r17, b18) = putStatements (irProofs r) b17
        (r18, b19) = putNames (irExterns r) b18
        (r19, b20) = putEntries [ETemplate k t | (k, t) <- irTemplates r] b19
        (r20, b21) = putEntries [ENames k v | (k, v) <- irCompanions r] b20
     in emit "Interface" (map show [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20]) b21

putEntry :: Entry -> Build -> (Int, Build)
putEntry e b0 = case e of
    ENames k v ->
        let (r0, b1) = putName k b0
            (r1, b2) = putNames v b1
         in emit "NamesEntry" [show r0, show r1] b2
    ECtor k o fs ->
        let (r0, b1) = putName k b0
            (r1, b2) = putName o b1
            (r2, b3) = putFields fs b2
         in emit "CtorEntry" [show r0, show r1, show r2] b3
    EGeneric k ps fs ->
        let (r0, b1) = putName k b0
            (r1, b2) = putNames ps b1
            (r2, b3) = putFields fs b2
         in emit "GenericEntry" [show r0, show r1, show r2] b3
    EInvariant k vs ->
        let (r0, b1) = putName k b0
            (r1, b2) = putValidations vs b1
         in emit "InvariantEntry" [show r0, show r1] b2
    ETrait k fs ->
        let (r0, b1) = putName k b0
            (r1, b2) = putTraitFns fs b1
         in emit "TraitEntry" [show r0, show r1] b2
    EFunction k (FunctionRecord ps sig ins outs term exports) ->
        let (r0, b1) = putName k b0
            (r1, b2) = putNames ps b1
            (r2, b3) = putSignature sig b2
            (r3, b4) = putValidations ins b3
            (r4, b5) = putValidations outs b4
            (r5, b6) = putOptTermination term b5
            (r6, b7) = putProofs exports b6
         in emit "FunctionEntry" (map show [r0, r1, r2, r3, r4, r5, r6]) b7
    EPair a b ->
        let (r0, b1) = putName a b0
            (r1, b2) = putName b b1
         in emit "PairEntry" [show r0, show r1] b2
    EAssoc a b os ->
        let (r0, b1) = putName a b0
            (r1, b2) = putName b b1
            (r2, b3) = putOptNames os b2
         in emit "AssocEntry" [show r0, show r1, show r2] b3
    EImplArgs a b t as ->
        let (r0, b1) = putName a b0
            (r1, b2) = putName b b1
            (r2, b3) = putType t b2
            (r3, b4) = putArgs as b3
         in emit "ImplArgsEntry" [show r0, show r1, show r2, show r3] b4
    EImplBounds a b bs ->
        let (r0, b1) = putName a b0
            (r1, b2) = putName b b1
            (r2, b3) = putBounds bs b2
         in emit "ImplBoundsEntry" [show r0, show r1, show r2] b3
    ETemplate k (TemplateRecord bs fns ret ps sig ins outs term body) ->
        let (r0, b1) = putName k b0
            (r1, b2) = putBounds bs b1
            (r2, b3) = putEntries [EType n t | (n, t) <- fns] b2
            (r3, b4) = putOptType ret b3
            (r4, b5) = putNames ps b4
            (r5, b6) = putSignature sig b5
            (r6, b7) = putValidations ins b6
            (r7, b8) = putValidations outs b7
            (r8, b9) = putOptTermination term b8
            (r9, b10) = putStatements body b9
         in emit "TemplateEntry" (map show [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9]) b10
    EType k t ->
        let (r0, b1) = putName k b0
            (r1, b2) = putType t b1
         in emit "TypeEntry" [show r0, show r1] b2
    ESurface space n ->
        let (r0, b1) = putName n b0
         in emit "SurfaceEntry" [spaceWord space, show r0] b1
    EBuiltin (BuiltinRecord b surface scheme value) ->
        let (r0, b1) = putBuiltin b b0
            (r1, b2) = putEntries [ESurface space n | (space, n) <- surface] b1
            (r2, b3) = putScheme scheme b2
            (r3, b4) = putValue value b3
         in emit "BuiltinEntry" [show r0, show r1, show r2, show r3] b4
  where
    putScheme scheme b = case scheme of
        SigFn params result ->
            let (s0, c1) = putTypes params b
                (s1, c2) = putType result c1
             in emit "SigFn" [show s0, show s1] c2
        SigDynamic -> emit "SigDynamic" [] b
        SigValueError message ->
            let (s0, c1) = putName message b
             in emit "SigValueError" [show s0] c1

spaceWords :: [(NameSpace, String)]
spaceWords = [(StdName, "std"), (PointerName, "pointer"), (GhostName, "ghost"), (ProofName, "proof"), (MethodName, "method"), (SyntaxName, "syntax")]

spaceWord :: NameSpace -> String
spaceWord space = maybe "" id (lookup space spaceWords)

putEntries :: [Entry] -> Build -> (Int, Build)
putEntries xs b = foldl' cons (emit "EntriesEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putEntry x state
         in emit "EntriesCons" [show headId, show tailId] state'

putOptNames :: [Maybe Name] -> Build -> (Int, Build)
putOptNames xs b = foldl' cons (emit "OptNamesEnd" [] b) (reverse xs)
  where
    cons (tailId, state) x =
        let (headId, state') = putOptName x state
         in emit "OptNamesCons" [show headId, show tailId] state'

putOptType :: Maybe Type -> Build -> (Int, Build)
putOptType value b0 = case value of
    Nothing -> emit "NoType" [] b0
    Just t ->
        let (r0, b1) = putType t b0
         in emit "SomeType" [show r0] b1

readInterfaceRecord :: String -> Result InterfaceRecord String
readInterfaceRecord text = decode "interface" text `bindResult` \n -> case n of
    NInterface r -> Ok r
    _ -> Error "AstData: wrong root kind"

readBuiltinTable :: String -> Result [BuiltinRecord] String
readBuiltinTable text = decode "builtins" text `bindResult` \n -> case n of
    NEntries es -> case [r | EBuiltin r <- es] of
        rs | length rs == length es -> Ok rs
        _ -> Error "AstData: a builtin table holds builtin entries"
    _ -> Error "AstData: wrong root kind"

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
    "IfExpr" -> do
        (c, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        (a, r1) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        (b, r2) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NExpression (IfExpr c a b), [r0, r1, r2])
    "BlockExpr" -> do
        (ss, r0) <- ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
        (e, r1) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        pure (NExpression (BlockExpr ss e), [r0, r1])
    "Ascribed" -> do
        (e, r0) <- ref nodes (\node -> case node of NExpression payload -> Just payload; _ -> Nothing)
        (t, r1) <- ref nodes (\node -> case node of NType payload -> Just payload; _ -> Nothing)
        pure (NExpression (Ascribed e t), [r0, r1])
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
    "Interface" -> do
        (pkg, r0) <- refName
        (modu, r1) <- ref nodes (\node -> case node of NOptName payload -> Just payload; _ -> Nothing)
        (types, r2) <- entries (\e -> case e of ENames k v -> Just (k, v); _ -> Nothing)
        (ctors, r3) <- entries (\e -> case e of ECtor k o fs -> Just (k, (o, fs)); _ -> Nothing)
        (generics, r4) <- entries (\e -> case e of EGeneric k ps fs -> Just (k, (ps, fs)); _ -> Nothing)
        (invariants, r5) <- entries (\e -> case e of EInvariant k vs -> Just (k, vs); _ -> Nothing)
        (traits, r6) <- entries (\e -> case e of ETrait k fs -> Just (k, fs); _ -> Nothing)
        (traitParams, r7) <- entries (\e -> case e of ENames k v -> Just (k, v); _ -> Nothing)
        (functions, r8) <- entries (\e -> case e of EFunction k f -> Just (k, f); _ -> Nothing)
        (impls, r9) <- entries (\e -> case e of EPair a b -> Just (a, b); _ -> Nothing)
        (assoc, r10) <- entries (\e -> case e of EAssoc a b os -> Just ((a, b), os); _ -> Nothing)
        (implArgs, r11) <- entries (\e -> case e of EImplArgs a b t as -> Just ((a, b), (t, as)); _ -> Nothing)
        (implBounds, r12) <- entries (\e -> case e of EImplBounds a b bs -> Just ((a, b), bs); _ -> Nothing)
        (copies, r13) <- refNames
        (linear, r14) <- refNames
        (drops, r15) <- refNames
        (axioms, r16) <- refStatements
        (proofs, r17) <- refStatements
        (externs, r18) <- refNames
        (templates, r19) <- entries (\e -> case e of ETemplate k t -> Just (k, t); _ -> Nothing)
        (companions, r20) <- entries (\e -> case e of ENames k v -> Just (k, v); _ -> Nothing)
        pure (NInterface (InterfaceRecord pkg modu types ctors generics invariants traits traitParams functions impls assoc implArgs implBounds copies linear drops axioms proofs externs templates companions), [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20])
    "NamesEntry" -> do
        (k, r0) <- refName
        (v, r1) <- refNames
        pure (NEntry (ENames k v), [r0, r1])
    "CtorEntry" -> do
        (k, r0) <- refName
        (o, r1) <- refName
        (fs, r2) <- refFields
        pure (NEntry (ECtor k o fs), [r0, r1, r2])
    "GenericEntry" -> do
        (k, r0) <- refName
        (ps, r1) <- refNames
        (fs, r2) <- refFields
        pure (NEntry (EGeneric k ps fs), [r0, r1, r2])
    "InvariantEntry" -> do
        (k, r0) <- refName
        (vs, r1) <- refValidations
        pure (NEntry (EInvariant k vs), [r0, r1])
    "TraitEntry" -> do
        (k, r0) <- refName
        (fs, r1) <- ref nodes (\node -> case node of NTraitFns payload -> Just payload; _ -> Nothing)
        pure (NEntry (ETrait k fs), [r0, r1])
    "FunctionEntry" -> do
        (k, r0) <- refName
        (ps, r1) <- refNames
        (sig, r2) <- refSignature
        (ins, r3) <- refValidations
        (outs, r4) <- refValidations
        (term, r5) <- refOptTermination
        (exports, r6) <- ref nodes (\node -> case node of NProofs payload -> Just payload; _ -> Nothing)
        pure (NEntry (EFunction k (FunctionRecord ps sig ins outs term exports)), [r0, r1, r2, r3, r4, r5, r6])
    "PairEntry" -> do
        (a, r0) <- refName
        (b, r1) <- refName
        pure (NEntry (EPair a b), [r0, r1])
    "AssocEntry" -> do
        (a, r0) <- refName
        (b, r1) <- refName
        (os, r2) <- ref nodes (\node -> case node of NOptNames payload -> Just payload; _ -> Nothing)
        pure (NEntry (EAssoc a b os), [r0, r1, r2])
    "ImplArgsEntry" -> do
        (a, r0) <- refName
        (b, r1) <- refName
        (t, r2) <- refType
        (as, r3) <- ref nodes (\node -> case node of NArgs payload -> Just payload; _ -> Nothing)
        pure (NEntry (EImplArgs a b t as), [r0, r1, r2, r3])
    "ImplBoundsEntry" -> do
        (a, r0) <- refName
        (b, r1) <- refName
        (bs, r2) <- refBounds
        pure (NEntry (EImplBounds a b bs), [r0, r1, r2])
    "TemplateEntry" -> do
        (k, r0) <- refName
        (bs, r1) <- refBounds
        (fns, r2) <- entries (\e -> case e of EType n t -> Just (n, t); _ -> Nothing)
        (ret, r3) <- ref nodes (\node -> case node of NOptType payload -> Just payload; _ -> Nothing)
        (ps, r4) <- refNames
        (sig, r5) <- refSignature
        (ins, r6) <- refValidations
        (outs, r7) <- refValidations
        (term, r8) <- refOptTermination
        (body, r9) <- refStatements
        pure (NEntry (ETemplate k (TemplateRecord bs fns ret ps sig ins outs term body)), [r0, r1, r2, r3, r4, r5, r6, r7, r8, r9])
    "TypeEntry" -> do
        (k, r0) <- refName
        (t, r1) <- refType
        pure (NEntry (EType k t), [r0, r1])
    "SurfaceEntry" -> do
        w <- word
        (n, r0) <- refName
        case [space | (space, w') <- spaceWords, w' == w] of
            [space] -> pure (NEntry (ESurface space n), [r0])
            _ -> failP "AstData: unknown name space"
    "BuiltinEntry" -> do
        (b, r0) <- ref nodes (\node -> case node of NBuiltin payload -> Just payload; _ -> Nothing)
        (surface, r1) <- entries (\e -> case e of ESurface space n -> Just (space, n); _ -> Nothing)
        (scheme, r2) <- ref nodes (\node -> case node of NScheme payload -> Just payload; _ -> Nothing)
        (value, r3) <- ref nodes (\node -> case node of NValue payload -> Just payload; _ -> Nothing)
        pure (NEntry (EBuiltin (BuiltinRecord b surface scheme value)), [r0, r1, r2, r3])
    "SigFn" -> do
        (params, r0) <- ref nodes (\node -> case node of NTypes payload -> Just payload; _ -> Nothing)
        (result, r1) <- refType
        pure (NScheme (SigFn params result), [r0, r1])
    "SigDynamic" -> pure (NScheme SigDynamic, [])
    "SigValueError" -> do
        (message, r0) <- refName
        pure (NScheme (SigValueError message), [r0])
    "NoType" -> pure (NOptType Nothing, [])
    "SomeType" -> do
        (t, r0) <- refType
        pure (NOptType (Just t), [r0])
    "EntriesEnd" -> pure (NEntries [], [])
    "EntriesCons" -> do
        (x, a) <- ref nodes (\node -> case node of NEntry v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NEntries v -> Just v; _ -> Nothing)
        pure (NEntries (x : xs), [a, b])
    "OptNamesEnd" -> pure (NOptNames [], [])
    "OptNamesCons" -> do
        (x, a) <- ref nodes (\node -> case node of NOptName v -> Just v; _ -> Nothing)
        (xs, b) <- ref nodes (\node -> case node of NOptNames v -> Just v; _ -> Nothing)
        pure (NOptNames (x : xs), [a, b])
    _ -> failP ("AstData: unknown tag " ++ tag)
  where
    refName = ref nodes (\node -> case node of NName payload -> Just payload; _ -> Nothing)
    refNames = ref nodes (\node -> case node of NNames payload -> Just payload; _ -> Nothing)
    refType = ref nodes (\node -> case node of NType payload -> Just payload; _ -> Nothing)
    refFields = ref nodes (\node -> case node of NFields payload -> Just payload; _ -> Nothing)
    refValidations = ref nodes (\node -> case node of NValidations payload -> Just payload; _ -> Nothing)
    refStatements = ref nodes (\node -> case node of NStatements payload -> Just payload; _ -> Nothing)
    refBounds = ref nodes (\node -> case node of NBounds payload -> Just payload; _ -> Nothing)
    refSignature = ref nodes (\node -> case node of NSignature payload -> Just payload; _ -> Nothing)
    refOptTermination = ref nodes (\node -> case node of NOptTermination payload -> Just payload; _ -> Nothing)
    entries project = ref nodes (\node -> case node of NEntries es -> mapM project es; _ -> Nothing)

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
