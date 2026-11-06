module TestStorageOracle (eraseStorageHelper) where

import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Mir
import Types (Arg (..), Type (..))
import Utils (Result (..))

-- Test-only oracle of the erased storage helpers, derived from MirGhost
-- before 6c7d87d. It avoids bootstrapping the guest eraser to check that
-- bootstrapping can construct its MIR. The fixtures have no Uninit or casts.
eraseStorageHelper :: Program -> Result Program String
eraseStorageHelper p
    | any uninit allTypes = Error "storage erasure oracle does not cover Uninit"
    | any unsupported (concatMap blockStatements [b | f <- functions, b <- Map.elems (fnBlocks f)]) = Error "storage erasure oracle does not cover Block::cast"
    | otherwise = Ok p
        { progTypes = Map.map eraseDecl (progTypes p)
        , progGenerics = Map.map (\(params, fields) -> (params, runtimeFields fields)) (progGenerics p)
        , progInvariants = Map.empty
        , progFunctions = Map.map eraseFunction (progFunctions p)
        , progMain = eraseFunction (progMain p)
        }
  where
    functions = progMain p : Map.elems (progFunctions p)
    allTypes = [localType d | f <- functions, d <- Map.elems (fnLocals f)] ++ [t | f <- functions, Just t <- [fnReturns f]] ++ [t | (_, fields) <- Map.elems (progGenerics p), (_, t) <- fields]
    uninit TUninit{} = True
    uninit (TNamed _ args) = or [uninit t | ArgType t <- args]
    uninit (TArrayOf t _) = uninit t
    uninit (TAddr t) = uninit t
    uninit (TBlock t) = uninit t
    uninit (TRef t) = uninit t
    uninit (TMutRef t) = uninit t
    uninit (TFn args result) = any uninit (result : args)
    uninit (TForall _ _ t) = uninit t
    uninit _ = False
    unsupported (Assign _ (ListOp BlockCast _)) = True
    unsupported _ = False
    ghostType = go (0 :: Int)
      where
        go depth ty | depth > 16 = False
        go depth (TNamed name _) = case Map.lookup name (progTypes p) of
            Just (StructDecl fields@(_ : _)) -> all (go (depth + 1) . snd) fields
            _ -> False
        go _ TBlock{} = True
        go _ _ = False
    runtimeFields = filter (not . ghostType . snd)
    eraseDecl (StructDecl fields) = StructDecl (runtimeFields fields)
    eraseDecl (EnumDecl variants) = EnumDecl [(name, runtimeFields fields) | (name, fields) <- variants]
    eraseFunction fn = fn
        { fnParams = filter (not . ghost) (fnParams fn)
        , fnBorrowed = filter (not . ghost) (fnBorrowed fn)
        , fnMutBorrowed = filter (not . ghost) (fnMutBorrowed fn)
        , fnFrom = filter (not . ghost) (fnFrom fn)
        , fnReturns = fmap (\t -> if ghostType t then TInt else t) (fnReturns fn)
        , fnLocals = Map.union newLocals (Map.mapWithKey keepReturn (Map.filterWithKey (\l _ -> not (ghost l) || l == Local 0) (fnLocals fn)))
        , fnBlocks = Map.map eraseBlock blocks
        , fnSpec = (fnSpec fn){specEnv = scrub (specEnv (fnSpec fn)), specLoops = Map.map (\loop -> loop{loopEnv = scrub (loopEnv loop)}) (specLoops (fnSpec fn))}
        }
      where
        ghosts = Set.fromList [l | (l, d) <- Map.toList (fnLocals fn), ghostType (localType d)]
        ghost l = l `Set.member` ghosts
        ghostOperand (Copy l) = ghost l
        ghostOperand (Move l) = ghost l
        ghostOperand _ = False
        runtime = filter (not . ghostOperand)
        scrub = Map.filter (not . ghostOperand)
        keepReturn l d | l == Local 0 && ghost l = d{localType = TInt}
        keepReturn _ d = d
        firstFree = 1 + maximum (0 : [i | Local i <- Map.keys (fnLocals fn)])
        (blocks, newLocals) = foldl' retarget (Map.empty, Map.empty) (Map.toAscList (fnBlocks fn))
        fresh new = (Local (firstFree + Map.size new), LocalDecl TInt Nothing)
        retarget (done, new) (id0, BasicBlock stmts term) =
            let (ss, n0) = foldl' statement ([], new) stmts
                (tt, n1) = case term of
                    Call f args d next | ghost d && d /= Local 0 -> let (l, decl) = fresh n0 in (Call f args l next, Map.insert l decl n0)
                    _ -> (term, n0)
             in (Map.insert id0 (BasicBlock (reverse ss) tt) done, n1)
        statement (ss, new) (Assign d rv@(ListOp op _)) | ghost d && d /= Local 0 && not (ghostOp op) =
            let (l, decl) = fresh new in (Assign l rv : ss, Map.insert l decl new)
        statement (ss, new) s = (s : ss, new)
        eraseBlock (BasicBlock ss term) = BasicBlock (concatMap eraseStatement ss) (case term of Call f args d next -> Call f (runtime args) d next; _ -> term)
        eraseStatement (Assign (Local 0) rv) | ghost (Local 0) = case rv of
            ListOp op args | not (ghostOp op) -> [Assign (Local 0) (ListOp op (runtime args))]
            _ -> [Assign (Local 0) (Use (Const (CInt 0)))]
        eraseStatement (Assign d _) | ghost d = []
        eraseStatement (Assign d (ListOp op args)) = [Assign d (ListOp op (runtime args))]
        eraseStatement (Assign d (MakeData name fields)) = [Assign d (MakeData name [(f, o) | (f, o) <- fields, not (ghostOperand o)])]
        eraseStatement (Ghost _ (GhostDissolve l)) | ghost l = []
        eraseStatement (Ghost _ (GhostDissolve l)) = [Peek l (ListOp UninitEmpty [])]
        eraseStatement (Ghost env g) = [Ghost (scrub env) g]
        eraseStatement s = [s]
