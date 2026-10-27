-- Bridge proof queries to the Tersus implementation while the Haskell engine
-- remains authoritative. Unsupported goals return Nothing, and unsupported
-- facts are omitted: weakening a context cannot invent a proof.
module SelfHostedProof (querySelfHosted) where

import qualified Data.Map.Strict as Map
import qualified Mir as M
import MirEval (MirValue (..), runNamedFunction)
import TersusTypes
import Utils (Result (..), inIntRange, mapResult)

data Enc = Enc
    { ids :: Map.Map IotaProof Integer
    , applications :: [MirValue]
    , constants :: [MirValue]
    }

emptyEnc :: Enc
emptyEnc = Enc Map.empty [] []

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
            (argIds, e2) <- internMany args e1
            let (i, e3) = freshTerm term e2
                app = record "ApplicationTerm" [("id", MInt i), ("function", MInt fid), ("arguments", MList (map MInt argIds))]
            pure (i, e3{applications = app : applications e3})
        CTerm (VInt n) -> let (i, e) = freshTerm term enc in pure (i, addConstant i 0 n e)
        CTerm (VBool b) -> let (i, e) = freshTerm term enc in pure (i, addConstant i 1 (if b then 1 else 0) e)
        _ -> pure (freshTerm term enc)

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

addFact :: (Enc, Facts) -> IotaProof -> (Enc, Facts)
addFact original@(enc, facts) proof = case relation proof of
    Nothing -> original
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
querySelfHosted program assumptions question = case relation question of
    Nothing -> Ok Nothing
    Just (r, a, b) -> case intern a enc >>= \(x, e) -> fmap (\(y, e') -> (x, y, e')) (intern b e) of
        Nothing -> Ok Nothing
        Just (x, y, e) -> mapResult decode (runNamedFunction program "entailsGoal" [context e facts, goal r x y])
  where
    (enc, facts) = foldl addFact (emptyEnc, emptyFacts) assumptions
    context e fs = record "ValidatorContext"
        [ ("equalities", MList (equalities fs)), ("applications", MList (applications e))
        , ("constants", MList (constants e)), ("orders", MList (orders fs))
        , ("different", MList (different fs)), ("differences", MList []) ]
    decode (Just (MBool b)) = Just b
    decode _ = Nothing
