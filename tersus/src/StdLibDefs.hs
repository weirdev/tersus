module StdLibDefs
    ( stdlibBuiltin
    , stdLibCtx
    , stdLibValCtx
    ) where

import qualified Data.Map as Map

import Parse (emptyDecls, parseStatementBlockWith)
import PreludeSource (stdlibSource)
import StdLib (builtinFunct, eqProof, stdlibBuiltinDecls)
import TersusTypes

-- The standard library written in Tersus (lib/stdlib.tersus), parsed once. Each `builtin fn` there
-- declares a builtin of StdLib.stdlibBuiltinDecls: what it does is the builtin it names, and its contracts
-- are the ones written there. This module, and not a Haskell literal, is what the checker, the lowering
-- and the validator take those contracts from.
stdlibTextDefs :: Map.Map BuiltinFunct Value
stdlibTextDefs = case parseStatementBlockWith emptyDecls stdlibSource of
    Left err -> error ("lib/stdlib.tersus does not parse: " ++ show err)
    Right (stmts, _) ->
        let defs = Map.fromList [(builtin, canonicalValue value) | Assign _ (Val value@(VFunct _ _ _ (BuiltinFunct builtin) _)) <- stmts]
         in case [name | (name, builtin) <- stdlibBuiltinDecls, not (Map.member builtin defs)] of
                [] -> defs
                missing -> error ("lib/stdlib.tersus does not declare: " ++ unwords missing)

-- A builtin, with the contract lib/stdlib.tersus writes for it. A builtin it does not declare is a
-- primitive, whose contract StdLib makes (an operation on a permission, or one made for a type).
stdlibBuiltin :: BuiltinFunct -> Value
stdlibBuiltin builtin = Map.findWithDefault (builtinFunct builtin) builtin stdlibTextDefs

-- A builtin as the term of a proof, get(list, index) or push(list, x): only which builtin it is is part
-- of a term (a builtin is compared by which one it is), so the contracts a parsed term carries are
-- taken out, to keep the term the one canonical value the proof engine interns.
canonical :: Value -> Value
canonical (VFunct ps _ _ body@(BuiltinFunct _) _) = VFunct ps [] [] body []
canonical other = other

canonicalValue :: Value -> Value
canonicalValue (VFunct ps ins outs body exported) = VFunct ps (map canonicalStatement ins) outs body (map canonicalProof exported)
canonicalValue other = other

canonicalStatement :: ValidationStatement -> ValidationStatement
canonicalStatement (ProofAssert proof) = ProofAssert (canonicalProof proof)
canonicalStatement (Rewrite rule) = Rewrite (canonicalRule rule)
canonicalStatement other = other

canonicalRule :: RwRule -> RwRule
canonicalRule (CheckRel proof) = CheckRel (canonicalProof proof)
canonicalRule (CheckGtZero proof) = CheckGtZero (canonicalProof proof)
canonicalRule (Refl proof) = Refl (canonicalProof proof)
canonicalRule (UserRewrite name proofs) = UserRewrite name (map canonicalProof proofs)
canonicalRule other = other

canonicalProof :: VariableProof -> VariableProof
canonicalProof (FApp funct args) = FApp (canonicalProof funct) (map canonicalProof args)
canonicalProof (CTerm value) = CTerm (canonical value)
canonicalProof (Forall index guards body) = Forall index (map canonicalProof guards) (canonicalProof body)
canonicalProof other = other

-- The names a program calls the standard library by
stdLibCtx :: Map.Map Variable Value
stdLibCtx =
    Map.fromList
        ( [(name, stdlibBuiltin builtin) | (name, builtin) <- stdlibBuiltinDecls, name `elem` programNames]
            ++ [ ("+", stdlibBuiltin Plus)
               , ("-", stdlibBuiltin Minus)
               , ("*", stdlibBuiltin Times)
               , ("/", stdlibBuiltin Div)
               , ("%", stdlibBuiltin Mod)
               , ("=", stdlibBuiltin (Rel Eq))
               , ("!=", stdlibBuiltin (Rel NotEq))
               , ("<", stdlibBuiltin (Rel Lt))
               , (">", stdlibBuiltin (Rel Gt))
               , ("<=", stdlibBuiltin (Rel LtEq))
               , (">=", stdlibBuiltin (Rel GtEq))
               ]
        )
  where
    programNames =
        [ "size", "first", "last", "get", "push", "pop", "set", "array"
        , "writeByte", "writeError", "readByte", "argCount", "argByte"
        , "pathByte", "fileLoad", "fileByte", "storeByte", "fileStore"
        , "toByte", "toInt"
        ]

stdLibValCtx :: (Map.Map Variable Iota, [IotaProof])
stdLibValCtx =
    let (varIotas, proofs) = helper (Map.toList stdLibCtx)
     in (Map.fromList varIotas, proofs)
  where
    -- Seed validation with one fresh symbolic name per stdlib binding plus a proof that
    -- the symbolic name is equal to the concrete builtin value.
    helper [] = ([], [])
    helper ((var, functDef) : rest) =
        let (restVarIota, restProof) = helper rest
         in ((var, Iota var) : restVarIota, FApp eqProof [ATerm (Iota var), CTerm functDef] : restProof)
