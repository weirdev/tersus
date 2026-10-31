module Solver where

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as S

import Syntax
import Types

-- The proof engine's terms and closure
--
-- A forall is one opaque term built from its guards and body, so the same forall twice is one term
data TermKey = KIota Iota | KConst Int | KApp Int [Int] | KBound Variable | KForall Variable [Int] Int deriving (Eq, Ord)

-- What tells constants apart. Builtin functions are one constant each, however they were written.
-- Any other constant (a user function) has no key and is found by comparing whole values.
data ConstKey = CInt Integer | CList [ConstKey] | CBool Bool | CData Name [(Variable, ConstKey)] | CBuiltin String deriving (Eq, Ord)

data TermTable = TermTable
    { tableKeys :: Map.Map TermKey Int
    , tableConsts :: [(Value, Int)]
    , tableConstIds :: Map.Map ConstKey Int -- the number of each constant, found without comparing whole values
    , tableOtherConsts :: [(Value, Int)] -- constants with no key
    , tableApps :: [(Int, (Int, [Int]))] -- applications: term, function term, argument terms
    , tableForalls :: [(Int, (Variable, [Int], Int))] -- foralls: term, index, guard terms, body term
    , tableAppCount :: Int
    , tableForallCount :: Int
    }

data Shape = AppShape Int [Int] | ForallShape Variable [Int] Int

type ShapeKey = Either (Int, [Int]) (Variable, [Int], Int)

data Closure = Closure
    { closureParents :: IntMap.IntMap Int -- a term number that is not its own class points toward its class
    , closureSignatures :: Map.Map ShapeKey Int -- a term of each signature
    , closureUsers :: IntMap.IntMap [Int] -- the nodes that have a term of the class as a part, by class
    , closureNodes :: IntMap.IntMap (Int, Shape) -- the terms that have parts
    }

-- A solver holds the terms and the congruence closure of some facts, so that more facts and goals can be added to it
-- without starting again. Adding gives a new solver; the one it was added to is unchanged.
data Solver = Solver
    { solverTable :: TermTable
    , solverClosure :: Closure
    , solverTrueId :: Int
    , solverZeroId :: Int
    , solverApps :: Int -- how many applications and foralls of the table the closure has
    , solverForalls :: Int
    }


-- The facts of a proof context that are already in a solver, so that a question about the context does not start again
-- from the facts (see ProofEngine.factCacheAdd). It is a guess about the context that is checked before it is used.
data FactCache = FactCache
    { cacheOriginals :: S.Set IotaProof -- the facts as the program has them
    , cacheFacts :: [IotaProof] -- the facts the solver has, with the builtins' contracts left out
    , cacheFactSet :: S.Set IotaProof
    , cacheSolver :: Solver
    }
