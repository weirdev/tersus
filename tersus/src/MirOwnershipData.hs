module MirOwnershipData
    ( ownershipInput
    , restoreOwnership
    ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Mir
import Utils

-- GhostPosition's negative line is a wire-only marker; real source positions are never negative.
ownershipInput :: Program -> Program
ownershipInput program = program{progFunctions = functions, progMain = mainFn}
  where
    (next, functions) = Map.mapAccum numberFunction 0 (progFunctions program)
    (_, mainFn) = numberFunction next (progMain program)
    numberFunction n fn = let (n', blocks) = Map.mapAccum numberBlock n (fnBlocks fn) in (n', fn{fnBlocks = blocks})
    numberBlock n block = let (n', stmts) = numberStatements n (blockStatements block) in (n', block{blockStatements = stmts})
    numberStatements n [] = (n, [])
    numberStatements n (stmt : rest) =
        let (nextId, marked) = case stmt of
                Ghost _ _ -> (n + 1, Ghost Map.empty (GhostPosition (-1) n))
                _ -> (n, stmt)
            (n', more) = numberStatements nextId rest
         in (n', marked : more)

restoreOwnership :: Program -> Program -> Result Program String
restoreOwnership original output
    | progTypes output /= progTypes original = Error "the ownership tool changed type declarations"
    | Map.keysSet (progFunctions output) /= Map.keysSet (progFunctions original) = Error "the ownership tool changed the function set"
    | otherwise =
        flatResultMap restoreNamed (Map.toList (progFunctions output)) `bindResult` \functions ->
            restoreFunction (progMain original) (progMain numbered) (progMain output) `bindResult` \mainFn ->
                Ok output
                    { progFunctions = Map.fromList functions
                    , progMain = mainFn
                    , progGenerics = progGenerics original
                    , progInvariants = progInvariants original
                    }
  where
    numbered = ownershipInput original
    restoreNamed (name, fn) =
        restoreFunction (progFunctions original Map.! name) (progFunctions numbered Map.! name) fn `bindResult` \restored -> Ok (name, restored)

restoreFunction :: Function -> Function -> Function -> Result Function String
restoreFunction original numbered output
    | header output /= header original = bad "changed the function header"
    | not (all retained (Map.toList (fnLocals original))) = bad "changed or removed an original local declaration"
    | not (Map.keysSet (fnBlocks original) `Set.isSubsetOf` Map.keysSet (fnBlocks output)) = bad "removed an original block"
    | length ids /= Set.size (Set.fromList ids) = bad "duplicated a ghost ID"
    | Set.fromList ids /= Map.keysSet ghosts = bad "missing or unrecognized ghost IDs"
    | otherwise =
        flatResultMap restoreBlock (Map.toList (fnBlocks output)) `bindResult` \blocks ->
            Ok output{fnSpec = fnSpec original, fnBlocks = Map.fromList blocks}
  where
    bad problem = Error ("in " ++ fnName original ++ ": the ownership tool " ++ problem)
    header fn = (fnName fn, fnParams fn, fnReturns fn, fnSizeParams fn, fnTypeParams fn, fnBorrowed fn, fnMutBorrowed fn, fnFrom fn)
    retained (local, decl) = Map.lookup local (fnLocals output) == Just decl
    originals = [stmt | block <- Map.elems (fnBlocks original), stmt@Ghost{} <- blockStatements block]
    numbers = [ident | block <- Map.elems (fnBlocks numbered), Ghost _ (GhostPosition (-1) ident) <- blockStatements block]
    ghosts = Map.fromList (zip numbers originals)
    ids = [ident | block <- Map.elems (fnBlocks output), Ghost _ (GhostPosition (-1) ident) <- blockStatements block]
    restoreBlock (bid, block) = flatResultMap restoreStatement (blockStatements block) `bindResult` \stmts -> Ok (bid, block{blockStatements = stmts})
    restoreStatement (Ghost _ (GhostPosition (-1) ident)) = maybe (bad "returned an unrecognized ghost ID") Ok (Map.lookup ident ghosts)
    restoreStatement Ghost{} = bad "returned an unnumbered ghost"
    restoreStatement stmt = Ok stmt
