module ProofState
    ( V
    , runV
    , throwV
    , liftR
    , tryV
    , fresh
    , freshN
    , iotaAt
    , PState (..)
    , FnInfo (..)
    , FnKind (..)
    , initialPState
    , allFacts
    , addFacts
    , refreshCache
    , proofContext
    , proofContextWith
    , lookupName
    , toIotaProof
    , withEnv
    , fnIota
    , withFunctions
    , constantValue
    , bodyState
    , valueOfConstant
    ) where

import Data.Containers.ListUtils (nubOrd)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

import qualified Mir as M
import qualified ProofEngine as Engine
import StdLib
import StdLibDefs (stdLibValCtx)
import TersusTypes
import Utils

-- The validator draws fresh iotas from one sequence, so that the states of different paths never share an iota
newtype V a = V {stepV :: Int -> Result (a, Int) String}

instance Functor V where
    fmap f (V g) = V (\n -> mapResult (\(a, n') -> (f a, n')) (g n))

instance Applicative V where
    pure a = V (\n -> Ok (a, n))
    V f <*> V g = V (\n -> f n `bindResult` \(h, n') -> mapResult (\(a, n'') -> (h a, n'')) (g n'))

instance Monad V where
    V g >>= f = V (\n -> g n `bindResult` \(a, n') -> stepV (f a) n')

runV :: V a -> Result a String
runV v = mapResult fst (stepV v 0)

throwV :: String -> V a
throwV e = V (\_ -> Error e)

liftR :: Result a String -> V a
liftR r = V (\n -> mapResult (\a -> (a, n)) r)

-- Runs the step and says how it ended. The iotas a failed step used are not used again, so no other path can see them.
tryV :: V a -> V (Result a String)
tryV (V g) = V (\n -> case g n of
    Ok (a, n') -> Ok (Ok a, n')
    Error e -> Ok (Error e, n))

fresh :: V Iota
fresh = V (\n -> Ok (iotaAt n, n + 1))

freshN :: Int -> V [Iota]
freshN k = V (\n -> Ok (map iotaAt [n .. n + k - 1], n + k))

-- a0, b0, ..., z0, a1, ...
iotaAt :: Int -> Iota
iotaAt n = Iota (toEnum (fromEnum 'a' + n `mod` 26) : show (n `div` 26))

-- What the validator knows about a function of the program once it has validated it: what a call has to show, and what it
-- gives. The facts about the parameters and the result are in terms of the names the function gave them.
data FnInfo = FnInfo
    { fnParamNames :: [Variable]
    , fnRequires :: [ValidationStatement]
    , fnExported :: [VariableProof]
    , fnTermination :: Maybe Termination
    , fnTerm :: IotaProof -- what the function is in a proof: the head of the applications that call it
    , fnGlobal :: Bool -- defined at the top of the program, where the functions after it can use it
    , fnKind :: FnKind
    , fnReads :: Bool -- reads the standard input: what it gives is not determined by its arguments, so two calls are not the same value
    , fnMutParams :: [Variable] -- the parameters a call may update (&mut T): the caller gets a new version of what each is to (REFERENCES.md)
    }

data FnKind = KBuiltin BuiltinFunct | KUser Name

-- The state at a point of a path through a function: what is known (the facts about the values) and which value each local
-- has. Values never change, an assignment gives the local a new one, so a fact stays true for the rest of the path.
data PState = PState
    { psLocals :: Map M.Local Iota
    , psLocalNames :: Map M.Local Variable -- the names of the program for the locals of the function being walked
    , psVars :: Map Variable Iota -- the variables of proofs (define)
    , psView :: Map Variable IotaProof -- what the names of the source mean in the statement being validated
    , psFacts :: [IotaProof] -- the facts of this path
    , psGlobalFacts :: [IotaProof] -- the facts that hold everywhere: the standard library, and the functions of the program
    , psGlobals :: Map Variable Iota -- the standard library, and the functions defined at the top of the program
    , psRules :: RuleContext
    , psFns :: Map Name FnInfo
    , psInBody :: Bool -- in the body of a function, where a function defined is local
    , psTerminates :: Bool -- in a function that is guaranteed to terminate
    , psCache :: Maybe FactCache
    , psProgram :: M.Program
    , psReaders :: Set.Set Name -- the functions of the program that read the standard input
    , psBorrows :: Map M.Local (M.Local, [M.RefStep]) -- the place each reference local is to, so that an assignment to the root re-versions what reads through it see it as
    }

-- The name of a function of the program as a value in proofs
fnIota :: Name -> Iota
fnIota name = Iota ("$" ++ name)

-- The state at the start of the program, given the names of its functions
initialPState :: M.Program -> PState
initialPState program =
    let (globals, stdFacts) = stdLibValCtx
        -- (a function of the program is known by its iota, `fnIota`, and not by a fact for each: a fact in every proof of every function
        -- makes the time to validate grow with the square of the number of functions)
        globalFacts = stdFacts
     in PState
            { psLocals = Map.empty
            , psLocalNames = Map.empty
            , psVars = Map.empty
            , psView = Map.empty
            , psFacts = []
            , psGlobalFacts = globalFacts
            , psGlobals = globals
            , psRules = stdLibRuleCtx
            , psFns = Map.empty
            , psInBody = False
            , psTerminates = False
            , psCache = Just (Engine.factCacheAdd Engine.emptyFactCache globalFacts)
            , psProgram = program
            , psReaders = M.readersOfInput program
            , psBorrows = Map.empty
            }

-- The functions that a function names are known by their value too (`f = $f` is `VFnRef f`), so that what returns one can be
-- proved to be it. These are the facts of the functions it names and not of every function of the program, since a fact in
-- every proof makes the time to validate a program grow with the square of its functions.
withFunctions :: M.Function -> PState -> PState
withFunctions fn st
    | null named = st
    | otherwise = refreshCache st{psGlobalFacts = psGlobalFacts st ++ [fact | fact <- named, fact `notElem` psGlobalFacts st]}
  where
    named = [FApp eqProof [ATerm (fnIota n), CTerm (VFnRef n)] | n <- Set.toList (M.functionsNamed fn), Map.member n (M.progFunctions (psProgram st))]

-- The state for the body of a function (or a rule) defined in this one: only what holds everywhere is known in it
bodyState :: PState -> PState
bodyState st =
    st
        { psLocals = Map.empty
        , psVars = Map.empty
        , psView = Map.empty
        , psFacts = []
        , psFns = Map.filter fnGlobal (psFns st)
        , psInBody = True
        , psCache = Just (Engine.factCacheAdd Engine.emptyFactCache (psGlobalFacts st))
        }

allFacts :: PState -> [IotaProof]
allFacts st = psFacts st ++ psGlobalFacts st

addFacts :: PState -> [IotaProof] -> PState
addFacts st new =
    st
        { psFacts = nubOrd (psFacts st ++ new)
        , psCache = Just (Engine.factCacheAdd (fromMaybe (Engine.factCacheAdd Engine.emptyFactCache (allFacts st)) (psCache st)) new)
        }

-- A cache of the facts, for a state whose facts were set by something other than addFacts
refreshCache :: PState -> PState
refreshCache st = st{psCache = Just (Engine.factCacheAdd Engine.emptyFactCache (allFacts st))}

proofContext :: PState -> Engine.ProofContext
proofContext st = Engine.proofContextFromCache (psCache st) (allFacts st)

proofContextWith :: PState -> [IotaProof] -> Engine.ProofContext
proofContextWith st extra = Engine.proofContextFromCache (psCache st) (allFacts st ++ extra)

-- What a name means in a statement: a variable of a proof, then a name of the program, then the standard library or a function
lookupName :: PState -> Variable -> Maybe IotaProof
lookupName st name =
    case Map.lookup name (psVars st) of
        Just iota -> Just (ATerm iota)
        Nothing -> case Map.lookup name (psView st) of
            Just term -> Just term
            Nothing -> ATerm <$> Map.lookup name (psGlobals st)

toIotaProof :: PState -> VariableProof -> Result IotaProof String
toIotaProof _ (CTerm val) = Ok (CTerm val)
toIotaProof _ (BVar index) = Ok (BVar index)
toIotaProof st (Forall index guards body) =
    case (flatResultMap (toIotaProof st) guards, toIotaProof st body) of
        (Ok iotaGuards, Ok iotaBody) -> Ok (Forall index iotaGuards iotaBody)
        (Error e, _) -> Error e
        (_, Error e) -> Error e
toIotaProof st (ATerm var) =
    case lookupName st var of
        Just term -> Ok term
        Nothing -> Error ("Variable not found in proof map: " ++ var)
toIotaProof st (FApp funct args) =
    toIotaProof st funct `bindResult` \functProof ->
        flatResultMap (toIotaProof st) args `bindResult` \iotaProofs -> case (functProof, iotaProofs) of
            -- (toInt(b) is b: a Byte is the Int that it is, so a proof about toInt(b) is a proof about b, which has the facts of a Byte)
            (ATerm (Iota "toInt"), [x]) -> Ok x
            -- (*r is what r is to: in a proof a reference is its current version, which the iota of its place is)
            (CTerm (VFunct _ _ _ (BuiltinFunct DerefOf) _), [x]) -> Ok x
            _ -> Ok (FApp functProof iotaProofs)

-- The state where the names of the program mean what the environment says, with the values they have now
withEnv :: M.Env -> PState -> PState
withEnv env st = st{psView = Map.mapMaybe resolve env}
  where
    resolve (M.Copy l) = ATerm <$> Map.lookup l (psLocals st)
    resolve (M.Const (M.CFn name))
        | Map.member name (psFns st) = Just (ATerm (fnIota name))
        | otherwise = Nothing
    resolve (M.Const c) = Just (CTerm (valueOfConstant c))

-- The term of a constant
constantValue :: M.Constant -> IotaProof
constantValue (M.CFn name) = ATerm (fnIota name)
constantValue c = CTerm (valueOfConstant c)

valueOfConstant :: M.Constant -> Value
valueOfConstant (M.CInt i) = VInt i
valueOfConstant (M.CBool b) = VBool b
valueOfConstant (M.CList cs) = VList (map valueOfConstant cs)
valueOfConstant (M.CArray cs) = VList (map valueOfConstant cs)
valueOfConstant (M.CData name fields) = VData name [(f, valueOfConstant c) | (f, c) <- fields]
valueOfConstant (M.CFn name) = VFnRef name
