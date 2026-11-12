-- Module interfaces as data, `tersus-ast 1 interface` (AST_DATA.md): what a checked module exposes to the
-- modules that import it, written and read without loss.
module InterfaceData (writeInterface, writeInterfaceLines, readInterface, readInterfaceLines, readInterfaceBytes) where

import qualified Data.ByteString.Char8 as B
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import AstData (FunctionRecord (..), InterfaceRecord (..), TemplateRecord (..), readInterfaceRecord, readInterfaceRecordBytes, readInterfaceRecordLines, writeInterfaceRecord, writeInterfaceRecordLines)
import Interface (InterfaceFunction (..), ModuleInterface (..))
import PackageData (ModuleId (..))
import Elaboration (Ctx (..), Template (..))
import Utils

writeInterface :: ModuleInterface -> Result String String
writeInterface iface = writeInterfaceRecord (recordOf iface)

writeInterfaceLines :: ModuleInterface -> Result [String] String
writeInterfaceLines iface = writeInterfaceRecordLines (recordOf iface)

-- A map's entries and a set's members have to be in ascending order, with no key twice, so that reading
-- them back loses nothing
readInterface :: String -> Result ModuleInterface String
readInterface text = readInterfaceRecord text `bindResult` interfaceOf

readInterfaceLines :: [String] -> Result ModuleInterface String
readInterfaceLines ls = readInterfaceRecordLines ls `bindResult` interfaceOf

readInterfaceBytes :: [B.ByteString] -> Result ModuleInterface String
readInterfaceBytes ls = readInterfaceRecordBytes ls `bindResult` interfaceOf

recordOf :: ModuleInterface -> InterfaceRecord
recordOf iface =
    InterfaceRecord
        { irPackage = package
        , irModule = modu
        , irTypes = Map.toAscList (ifTypes iface)
        , irCtors = Map.toAscList (ifCtors iface)
        , irGenerics = Map.toAscList (ifGenerics iface)
        , irInvariants = Map.toAscList (ifInvariants iface)
        , irTraits = Map.toAscList (ifTraits iface)
        , irTraitParams = Map.toAscList (ifTraitParams iface)
        , irFunctions = [(name, functionRecord fn) | (name, fn) <- Map.toAscList (ifFunctions iface)]
        , irImpls = Set.toAscList (ifImpls iface)
        , irAssoc = Map.toAscList (ifAssoc iface)
        , irImplArgs = Map.toAscList (ifImplArgs iface)
        , irImplBounds = Map.toAscList (ifImplBounds iface)
        , irCopies = Set.toAscList (ifCopies iface)
        , irLinear = Set.toAscList (ifLinear iface)
        , irDrops = Set.toAscList (ifDrops iface)
        , irAxioms = ifAxioms iface
        , irProofs = ifProofs iface
        , irExterns = Set.toAscList (ifExterns iface)
        , irTemplates = [(name, templateRecord t) | (name, t) <- Map.toAscList (ifTemplates iface)]
        , irCompanions = Map.toAscList (ifCompanions iface)
        }
  where
    ModuleId package modu = ifModule iface
    functionRecord fn = FunctionRecord (fnParams fn) (fnSignature fn) (fnRequires fn) (fnEnsures fn) (fnTermination fn) (fnExported fn)
    templateRecord t =
        TemplateRecord (tmplBounds t) (Map.toAscList (ctxFns (tmplCtx t))) (ctxReturn (tmplCtx t)) (tmplParams t) (tmplSignature t) (tmplRequires t) (tmplEnsures t) (tmplTermination t) (tmplBody t)

interfaceOf :: InterfaceRecord -> Result ModuleInterface String
interfaceOf r =
    ascending (map fst (irTypes r)) `bindResult` \types ->
    ascending (map fst (irCtors r)) `bindResult` \ctors ->
    ascending (map fst (irGenerics r)) `bindResult` \generics ->
    ascending (map fst (irInvariants r)) `bindResult` \invariants ->
    ascending (map fst (irTraits r)) `bindResult` \traits ->
    ascending (map fst (irTraitParams r)) `bindResult` \traitParams ->
    ascending (map fst (irFunctions r)) `bindResult` \functions ->
    ascending (irImpls r) `bindResult` \impls ->
    ascending (map fst (irAssoc r)) `bindResult` \assoc ->
    ascending (map fst (irImplArgs r)) `bindResult` \implArgs ->
    ascending (map fst (irImplBounds r)) `bindResult` \implBounds ->
    ascending (irCopies r) `bindResult` \copies ->
    ascending (irLinear r) `bindResult` \linear ->
    ascending (irDrops r) `bindResult` \drops ->
    ascending (irExterns r) `bindResult` \externs ->
    ascending (map fst (irTemplates r)) `bindResult` \templates ->
    ascending (map fst (irCompanions r)) `bindResult` \companions ->
    mapResultAll templateAscending (irTemplates r) `bindResult` \() ->
        Ok
            ModuleInterface
                { ifModule = ModuleId (irPackage r) (irModule r)
                , ifTypes = Map.fromDistinctAscList (zip types (map snd (irTypes r)))
                , ifCtors = Map.fromDistinctAscList (zip ctors (map snd (irCtors r)))
                , ifGenerics = Map.fromDistinctAscList (zip generics (map snd (irGenerics r)))
                , ifInvariants = Map.fromDistinctAscList (zip invariants (map snd (irInvariants r)))
                , ifTraits = Map.fromDistinctAscList (zip traits (map snd (irTraits r)))
                , ifTraitParams = Map.fromDistinctAscList (zip traitParams (map snd (irTraitParams r)))
                , ifFunctions = Map.fromDistinctAscList (zip functions [interfaceFunction f | (_, f) <- irFunctions r])
                , ifImpls = Set.fromDistinctAscList impls
                , ifAssoc = Map.fromDistinctAscList (zip assoc (map snd (irAssoc r)))
                , ifImplArgs = Map.fromDistinctAscList (zip implArgs (map snd (irImplArgs r)))
                , ifImplBounds = Map.fromDistinctAscList (zip implBounds (map snd (irImplBounds r)))
                , ifCopies = Set.fromDistinctAscList copies
                , ifLinear = Set.fromDistinctAscList linear
                , ifDrops = Set.fromDistinctAscList drops
                , ifAxioms = irAxioms r
                , ifProofs = irProofs r
                , ifExterns = Set.fromDistinctAscList externs
                , ifTemplates = Map.fromDistinctAscList (zip templates [template t | (_, t) <- irTemplates r])
                , ifCompanions = Map.fromDistinctAscList (zip companions (map snd (irCompanions r)))
                }
  where
    interfaceFunction (FunctionRecord ps sig ins outs term exported) = InterfaceFunction ps sig ins outs term exported
    template (TemplateRecord bs fns ret ps sig ins outs term body) = Template bs (Ctx (Map.fromDistinctAscList fns) ret) ps sig ins outs term body
    templateAscending (_, TemplateRecord _ fns _ _ _ _ _ _ _) = mapResult (const ()) (ascending (map fst fns))
    mapResultAll f xs = foldr (\x rest -> f x `bindResult` \() -> rest) (Ok ()) xs

ascending :: Ord a => [a] -> Result [a] String
ascending keys
    | and (zipWith (<) keys (drop 1 keys)) = Ok keys
    | otherwise = Error "InterfaceData: entries out of order or repeated"
