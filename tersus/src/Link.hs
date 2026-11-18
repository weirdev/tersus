{-# OPTIONS_GHC -fno-cse -fno-full-laziness #-}
module Link
    ( linkPrograms
    , linkWithLibraries
    , linkValidatedPrograms
    , pruneProgram
    , completeSpecEnvs
    ) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import DataCodec (quote)
import qualified Mir as M
import MirCopies (groundType, libraryBuiltin, makeCopiesWith)
import MirMono (instantiate, namedTypesByName, redirect)
import MirMoves (checkSpawns)
import MirPass (programData, runPassWith)
import PackageData (ModuleId (..))
import Seed (cachedSeed)
import System.IO.Unsafe (unsafePerformIO)
import Types (Arg (..), Name, Size (..), Type (..), instanceName, listType)
import Utils

linkPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkPrograms = linkWithLibraries []

-- The compiler's library units linked ahead of the program's own: their functions with bounds are validated where the
-- program uses them (MirCopies.makeCopiesWith), every other unit's where they are defined
linkWithLibraries :: [(ModuleId, M.Program)] -> [(ModuleId, M.Program)] -> Result M.Program String
linkWithLibraries libraries own = linkWith libraries True (libraries ++ own)

-- The units linked as a program that is validated and not owned or emitted itself (the native storage, all of it the
-- compiler's libraries): its types' facts are not made into copies no call names
linkValidatedPrograms :: [(ModuleId, M.Program)] -> Result M.Program String
linkValidatedPrograms units = linkWith units False units

boundedOf :: [(ModuleId, M.Program)] -> Set.Set Name
boundedOf units = Set.fromList [name | (_, program) <- units, name <- Map.keys (M.progBounded program)]

-- Linking runs in the pinned emitter seed (lib/mir/link), not stage 1: stage 1 is made from programs this module links. The
-- native merge refuses what the units disagree on, their checked providers and facts included; the copies are made here
{-# NOINLINE linkWith #-}
linkWith :: [(ModuleId, M.Program)] -> Bool -> [(ModuleId, M.Program)] -> Result M.Program String
linkWith _ _ [] = Error "link error: no modules to link"
linkWith libraries recording units = flatResultMap unitData units `bindResult` \parts ->
    linkPass ("merge " ++ show (length units) ++ "\n" ++ concat parts) `bindResult` \merged ->
        -- (an Instance record of a function without bounds is a frame of it: the types a copy of it is made at, which
        -- the elaborator found through the calls that reach it; the host's monomorphisation makes the copy)
        let copyRecord (g, args) = Map.member g (M.progBounded merged) || (g == libraryBuiltin && null args)
            frames = [record | record <- Map.elems (M.progInstances merged), not (copyRecord record)]
         in flatResultMap (frameKey (M.progFunctions merged)) frames `bindResult` \frameKeys ->
            -- (a copy the call cannot have is refused as the elaborator refuses a call)
            let linked = M.completeInstances merged{M.progInstances = Map.filter copyRecord (M.progInstances merged)}
                storage = M.progStorage linked
                -- (the frames the calls of the functions the program keeps reach, and the calls of those frames' copies in
                -- turn, keep the types a copy holds, as natively as the program has them: a frame no kept call reaches keeps none)
                framesKept p live = Set.unions [Set.union (typeNames t) (instancesIn t) | key <- Set.toList (framesReached (Set.fromList frameKeys) p live), held <- frameTypes p key, t <- [held, listType storage held]]
                -- (the facts' functions are made for the types the program keeps once the copies its calls name are made,
                -- not for every instance a library declares: the native prune says what it keeps)
                kept p = pruneProgram p `bindResult` \pruned ->
                    Ok (Set.unions [Map.keysSet (M.progTypes pruned), Map.keysSet (namedTypesByName pruned), framesKept p (Map.keysSet (M.progFunctions pruned))])
                -- (a function a fact names can keep more types, whose facts' functions are made in turn)
                withFacts owners = makeCopiesWith library (Just owners) linked `bindResult` \p ->
                    kept p `bindResult` \more -> if more `Set.isSubsetOf` owners then Ok p else withFacts (Set.union owners more)
                copied = makeCopiesWith library Nothing linked `bindResult` \plain ->
                    if recording then kept plain `bindResult` withFacts else Ok plain
             in case copied of
                Error e -> Error ("Validation failed: " ++ e)
                Ok p -> checkSpawns threadLibrary p
  where
    library = boundedOf libraries
    threadLibrary = boundedOf [unit | unit@(ModuleId "std" (Just "thread"), _) <- libraries]
    unitData (ModuleId pkg modu, program) = programData program `bindResult` \text ->
        Ok ("unit " ++ quote pkg ++ " " ++ maybe "none" (\name -> "some " ++ quote name) modu
            ++ " " ++ show (length (lines text)) ++ "\n" ++ text)

-- The copy a frame names, of a function without bounds at types and sizes that are all known; any other is refused
frameKey :: Map.Map Name M.Function -> (Name, [Arg]) -> Result (Name, [Type], [Integer]) String
frameKey functions (g, args) = case Map.lookup g functions of
    Just f
        | length tys == length (M.fnTypeParams f) && length sizes == length (M.fnSizeParams f) && length tys + length sizes == length args && all groundType tys ->
            Ok (g, tys, sizes)
    _ -> Error ("link error: an instance of " ++ g ++ " that is no copy of a function with bounds nor a frame of the function")
  where
    tys = [t | ArgType t <- args]
    sizes = [k | ArgSize (SizeConst k) <- args]

-- The frames the calls of the live functions (the native prune's) reach, through the calls of each frame's copy in turn,
-- whose bodies are the linked program's
framesReached :: Set.Set (Name, [Type], [Integer]) -> M.Program -> Set.Set Name -> Set.Set (Name, [Type], [Integer])
framesReached supplied p live = go [key | fn <- M.progMain p : livePlain, key <- snd (redirect p fn), Set.member key supplied] Set.empty
  where
    livePlain = [fn | name <- Set.toList live, Just fn <- [Map.lookup name (M.progFunctions p)], null (M.fnTypeParams fn), null (M.fnSizeParams fn)]
    go [] seen = seen
    go (key@(g, tys, sizes) : rest) seen
        | Set.member key seen = go rest seen
        | otherwise = case Map.lookup g (M.progFunctions p) of
            Just f -> go ([next | next <- snd (redirect p (instantiate f tys sizes)), Set.member next supplied] ++ rest) (Set.insert key seen)
            Nothing -> go rest (Set.insert key seen)

-- The types a frame's copy holds
frameTypes :: M.Program -> (Name, [Type], [Integer]) -> [Type]
frameTypes p (g, tys, sizes) = case Map.lookup g (M.progFunctions p) of
    Just f -> let copy = instantiate f tys sizes in [M.localType d | d <- Map.elems (M.fnLocals copy)] ++ maybe [] pure (M.fnReturns copy)
    Nothing -> []

-- The rendered names of the instances a type is made of
instancesIn :: Type -> Set.Set Name
instancesIn ty = case ty of
    TNamed name args -> Set.insert (instanceName name args) (Set.unions [instancesIn u | ArgType u <- args])
    TArrayOf inner _ -> instancesIn inner
    TRef inner -> instancesIn inner
    TMutRef inner -> instancesIn inner
    _ -> Set.empty

typeNames :: Type -> Set.Set Name
typeNames ty = case ty of
    TNamed name args -> Set.singleton name <> foldMap argNames args
    TVariant name -> Set.singleton name
    TArrayOf inner _ -> typeNames inner
    TAddr inner -> typeNames inner
    TBlock inner -> typeNames inner
    TUninit inner -> typeNames inner
    TRef inner -> typeNames inner
    TMutRef inner -> typeNames inner
    TFn args ret -> Set.unions (map typeNames (ret : args))
    TFnContract args ret _ -> Set.unions (map typeNames (ret : args))
    TForall _ _ inner -> typeNames inner
    _ -> Set.empty
  where
    argNames (ArgType inner) = typeNames inner
    argNames _ = Set.empty

{-# NOINLINE pruneProgram #-}
pruneProgram :: M.Program -> Result M.Program String
pruneProgram program = programData program `bindResult` \text -> linkPass ("prune\n" ++ text)

{-# NOINLINE completeSpecEnvs #-}
completeSpecEnvs :: M.Program -> Result M.Program String
completeSpecEnvs program = programData program `bindResult` \text -> linkPass ("environments\n" ++ text)

{-# NOINLINE linkPass #-}
linkPass :: String -> Result M.Program String
linkPass request = unsafePerformIO (runPassWith cachedSeed "the linker written in Tersus" ("pass link\n" ++ request))
