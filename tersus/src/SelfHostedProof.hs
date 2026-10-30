-- Bridge proof queries to the Tersus implementation while the Haskell engine
-- remains authoritative. Unsupported goals return Nothing, and unsupported
-- facts are omitted: weakening a context cannot invent a proof.
module SelfHostedProof (querySelfHosted) where

import qualified Data.Map.Strict as Map
import qualified Mir as M
import MirEval (MirValue (..), runNamedFunction)
import StdLib (builtinFunct)
import TersusTypes
import Utils (Result (..), inIntRange, mapResult)

data Enc = Enc
    { ids :: Map.Map IotaProof Integer
    , applications :: [MirValue]
    , constants :: [MirValue]
    , variants :: [MirValue]
    , fieldFunctions :: [Integer]
    , constructorFunctions :: [Integer]
    }

emptyEnc :: Enc
emptyEnc = Enc Map.empty [] [] [] [] []

record :: String -> [(String, MirValue)] -> MirValue
record = MData

-- Intern a complete term before exposing its identifier. A forall or bound
-- variable has no representation yet. Integer literals outside Tersus's
-- range cannot be carried by the bridge and are likewise unsupported.
intern :: IotaProof -> Enc -> Maybe (Integer, Enc)
intern term enc = case Map.lookup term (ids enc) of
    Just i -> Just (i, enc)
    Nothing -> case term of
        Forall{} -> Nothing
        BVar{} -> Nothing
        CTerm (VInt n) | not (inIntRange n) -> Nothing
        FApp (CTerm (VFunct _ _ _ (BuiltinFunct f) _)) _ | readsWorld f -> Nothing
        FApp f args -> do
            (fid, e1) <- intern f enc
            let e1a = if fieldFunction f then e1{fieldFunctions = fid : fieldFunctions e1} else e1
            (functionId, e1b) <- case f of
                CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name _)) _) -> intern (CTerm (builtinFunct (Ctor ("ctor:" ++ name) []))) e1a
                _ -> pure (fid, e1a)
            let e1c = if constructorFunction f then e1b{constructorFunctions = functionId : constructorFunctions e1b} else e1b
            (argIds, e2) <- internMany args e1c
            let (i, e3) = freshTerm term e2
                app = record "ApplicationTerm" [("id", MInt i), ("function", MInt functionId), ("arguments", MList (map MInt argIds))]
                e4 = e3{applications = app : applications e3}
            case f of
                CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name _)) _) -> do
                    (family, e5) <- intern (CTerm (builtinFunct (Ctor ("enum:" ++ constructorFamily name) []))) e4
                    (constructor, e6) <- intern (CTerm (builtinFunct (Ctor ("ctor:" ++ name) []))) e5
                    let fact = record "VariantFact" [("object", MInt i), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool True)]
                    pure (i, e6{variants = fact : variants e6})
                _ -> pure (i, e4)
        CTerm (VInt n) -> let (i, e) = freshTerm term enc in pure (i, addConstant i 0 n e)
        CTerm (VBool b) -> let (i, e) = freshTerm term enc in pure (i, addConstant i 1 (if b then 1 else 0) e)
        CTerm (VData name fields) -> do
            let (i, e1) = freshTerm term enc
            (fieldIds, e2) <- internMany [CTerm value | (_, value) <- fields] e1
            (family, e3) <- intern (CTerm (builtinFunct (Ctor ("enum:" ++ constructorFamily name) []))) e2
            (constructor, e4) <- intern (CTerm (builtinFunct (Ctor ("ctor:" ++ name) []))) e3
            (_, e5) <- intern (CTerm (builtinFunct (Ctor name (map fst fields)))) e4
            let fact = record "VariantFact" [("object", MInt i), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool True)]
                app = record "ApplicationTerm" [("id", MInt i), ("function", MInt constructor), ("arguments", MList (map MInt fieldIds))]
            pure (i, e5{applications = app : applications e5, variants = fact : variants e5, constructorFunctions = constructor : constructorFunctions e5})
        _ -> pure (freshTerm term enc)

fieldFunction :: IotaProof -> Bool
fieldFunction (CTerm (VFunct _ _ _ (BuiltinFunct (Field _ _)) _)) = True
fieldFunction (CTerm (VFunct _ _ _ (BuiltinFunct (Project _ _)) _)) = True
fieldFunction _ = False

constructorFunction :: IotaProof -> Bool
constructorFunction (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor _ _)) _)) = True
constructorFunction _ = False

constructorFamily :: Name -> Name
constructorFamily name = case break (== ':') name of
    (family, ':' : ':' : _) | not (null family) -> family
    _ -> name

constructorFieldFacts :: Enc -> [MirValue]
constructorFieldFacts enc =
    [ record "ConstructorField" [("constructor", MInt constructorId), ("field", MInt fieldId), ("index", MInt index)]
    | (constructorTerm, _) <- Map.toList (ids enc)
    , Just (name, fields) <- [constructorShape constructorTerm]
    , Just constructorId <- [Map.lookup (CTerm (builtinFunct (Ctor ("ctor:" ++ name) []))) (ids enc)]
    , (index, field) <- zip [0 ..] fields
    , (fieldTerm, fieldId) <- Map.toList (ids enc)
    , selects name field fieldTerm
    ]
  where
    constructorShape (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) = Just (name, fields)
    constructorShape _ = Nothing
    selects _ field (CTerm (VFunct _ _ _ (BuiltinFunct (Field _ selected)) _)) = field == selected
    selects name field (CTerm (VFunct _ _ _ (BuiltinFunct (Project variant selected)) _)) = name == variant && field == selected
    selects _ _ _ = False

freshTerm :: IotaProof -> Enc -> (Integer, Enc)
freshTerm term enc =
    let i = toInteger (Map.size (ids enc))
     in (i, enc{ids = Map.insert term i (ids enc)})

addConstant :: Integer -> Integer -> Integer -> Enc -> Enc
addConstant i kind value enc = enc{constants = record "ConstantTerm" [("id", MInt i), ("kind", MInt kind), ("value", MInt value)] : constants enc}

internMany :: [IotaProof] -> Enc -> Maybe ([Integer], Enc)
internMany [] enc = Just ([], enc)
internMany (x : xs) enc = do
    (i, e1) <- intern x enc
    (is, e2) <- internMany xs e1
    pure (i : is, e2)

relation :: IotaProof -> Maybe (Rel, IotaProof, IotaProof)
relation (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel r)) _)) [a, b]) = Just (r, a, b)
relation _ = Nothing

-- All relation constructors use the same two named operands.
goal :: Rel -> Integer -> Integer -> MirValue
goal r a b = record ("ValidatorGoal::" ++ name) [("left", MInt left), ("right", MInt right)]
  where
    (name, left, right) = case r of
        Eq -> ("Equal", a, b)
        NotEq -> ("Different", a, b)
        Lt -> ("Less", a, b)
        LtEq -> ("AtMost", a, b)
        Gt -> ("Less", b, a)
        GtEq -> ("AtMost", b, a)

data Facts = Facts { equalities :: [MirValue], different :: [MirValue], orders :: [MirValue] }

emptyFacts :: Facts
emptyFacts = Facts [] [] []

withinQuestion :: IotaProof -> Maybe (IotaProof, IotaProof)
withinQuestion (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Within) _)) [inner, outer]) = Just (inner, outer)
withinQuestion _ = Nothing

variantAssertion :: IotaProof -> Maybe (Name, IotaProof)
variantAssertion (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is name)) _)) [object]) = Just (name, object)
variantAssertion _ = Nothing

variantFact :: Name -> Integer -> Enc -> Maybe Enc
variantFact name object enc = do
    (family, e1) <- intern (CTerm (builtinFunct (Ctor ("enum:" ++ constructorFamily name) []))) enc
    (constructor, e2) <- intern (CTerm (builtinFunct (Ctor ("ctor:" ++ name) []))) e1
    let fact = record "VariantFact" [("object", MInt object), ("family", MInt family), ("constructor", MInt constructor), ("matches", MBool True)]
    pure e2{variants = fact : variants e2}

addFact :: (Enc, Facts) -> IotaProof -> (Enc, Facts)
addFact original@(enc, facts) proof = case relation proof of
    Nothing -> case variantAssertion proof of
        Nothing -> original
        Just (name, object) -> case intern object enc of
            Nothing -> original
            Just (objectId, e1) -> case variantFact name objectId e1 of
                Nothing -> original
                Just e2 -> (e2, facts)
    Just (r, a, b) -> case intern a enc >>= \(x, e) -> fmap (\(y, e') -> (x, y, e')) (intern b e) of
        Nothing -> original
        Just (x, y, e) -> (e, insert r x y facts)
  where
    insert Eq x y fs = fs{equalities = record "EqualityFact" [("left", MInt x), ("right", MInt y)] : equalities fs}
    insert NotEq x y fs = fs{different = record "DisequalityFact" [("left", MInt x), ("right", MInt y)] : different fs}
    insert r x y fs =
        let (a, b, strict) = case r of
                Lt -> (x, y, True)
                LtEq -> (x, y, False)
                Gt -> (y, x, True)
                GtEq -> (y, x, False)
            entry = record "OrderFact" [("smaller", MInt a), ("greater", MInt b), ("strict", MBool strict)]
         in fs{orders = entry : orders fs}

-- The supplied program must be the validated lib/validation.tersus. This
-- bridge returns Nothing when the goal is not yet representable. A False
-- answer means only that the Tersus engine could not prove it.
querySelfHosted :: M.Program -> [IotaProof] -> IotaProof -> Result (Maybe Bool) String
querySelfHosted program assumptions question = case withinQuestion question of
    Just (inner, outer) -> case intern inner enc >>= \(x, e) -> fmap (\(y, e') -> (x, y, e')) (intern outer e) of
        Nothing -> Ok Nothing
        Just (x, y, e) -> mapResult decode (runNamedFunction program "entailsGoal" [context e facts, record "ValidatorGoal::Within" [("inner", MInt x), ("outer", MInt y)]])
    Nothing -> case relation question of
        Nothing -> Ok Nothing
        Just (r, a, b) -> case intern a enc >>= \(x, e) -> fmap (\(y, e') -> (x, y, e')) (intern b e) of
            Nothing -> Ok Nothing
            Just (x, y, e) -> mapResult decode (runNamedFunction program "entailsGoal" [context e facts, goal r x y])
  where
    (enc, facts) = foldl addFact (emptyEnc, emptyFacts) assumptions
    context e fs = record "ValidatorContext"
        [ ("equalities", MList (equalities fs)), ("applications", MList (applications e))
        , ("constants", MList (constants e)), ("orders", MList (orders fs))
        , ("different", MList (different fs)), ("variants", MList (variants e)), ("fieldFunctions", MList (map MInt (fieldFunctions e))), ("constructorFunctions", MList (map MInt (constructorFunctions e))), ("constructorFields", MList (constructorFieldFacts e)), ("differences", MList []) ]
    decode (Just (MBool b)) = Just b
    decode _ = Nothing
