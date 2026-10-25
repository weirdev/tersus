module Pretty (renderProof, renderVarProof, renderValue, renderType) where

import Data.List (intercalate, stripPrefix)

import TersusTypes

-- Renders a proof term in Tersus syntax, e.g. "forall j in 0..size(l): get(l, j) = 0".
renderVarProof :: Proof Variable -> String
renderVarProof = renderProof sourceName
  where
    -- the ends of a for loop's range, and what a loop over a list goes through, are kept in variables the program cannot write
    loopName loop = maybe ("for " ++ loop) (\place -> "the for loop at " ++ place) (stripPrefix "$index " loop)
    sourceName name
        | Just loop <- stripPrefix "$hi " name = "(end of " ++ loopName loop ++ ")"
        | Just loop <- stripPrefix "$lo " name = "(start of " ++ loopName loop ++ ")"
        | Just place <- stripPrefix "$list " name = "(the list of the for loop at " ++ place ++ ")"
        | Just place <- stripPrefix "$index " name = "(the index of the for loop at " ++ place ++ ")"
        | otherwise = name

renderProof :: (i -> String) -> Proof i -> String
renderProof name = go 0
  where
    -- A term is parenthesized when its operator binds looser than the context's level: relations 0, +/- 1, */ 2.
    go _ (ATerm i) = name i
    go _ (BVar v) = v
    go _ (CTerm v) = renderValue v
    go prec (FApp (CTerm (VFunct _ _ _ (BuiltinFunct b) _)) [l, r])
        | Just (op, level) <- infixOp b =
            let text = go (max level 1) l ++ " " ++ op ++ " " ++ go (if level == 0 then 1 else level + 1) r
             in if prec > level then "(" ++ text ++ ")" else text
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Field _ field)) _)) [struct]) = go 3 struct ++ "." ++ field
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Project _ field)) _)) [struct]) = go 3 struct ++ "." ++ field
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Cast variant)) _)) [value]) = "(" ++ go 1 value ++ " as " ++ variant ++ ")"
    go prec (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variant)) _)) [value]) =
        let text = go 1 value ++ " is " ++ variant
         in if prec > 0 then "(" ++ text ++ ")" else text
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name _)) _)) []) = name
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name fields)) _)) args)
        | length fields == length args = name ++ " { " ++ intercalate ", " (zipWith (\f a -> f ++ ": " ++ go 0 a) fields args) ++ " }"
    go _ (FApp f args) = renderHead f ++ "(" ++ intercalate ", " (map (go 0) args) ++ ")"
    go prec (Forall v guards body) =
        let text = "forall " ++ v ++ guardText v guards ++ ": " ++ go 0 body
         in if prec > 0 then "(" ++ text ++ ")" else text

    renderHead (CTerm (VFunct _ _ _ (BuiltinFunct b) _)) = builtinName b
    renderHead (CTerm (VFunct args _ _ _ _)) = "fn(" ++ intercalate ", " args ++ ")"
    renderHead other = go 3 other

    -- Guards "j >= lo, j < hi" read back as the "in lo..hi" shorthand.
    guardText v [FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel GtEq)) _)) [BVar a, lo], FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Rel Lt)) _)) [BVar b, hi]]
        | a == v && b == v = " in " ++ go 2 lo ++ ".." ++ go 2 hi
    guardText _ [] = ""
    guardText _ guards = " where " ++ intercalate ", " (map (go 0) guards)

infixOp :: BuiltinFunct -> Maybe (String, Int)
infixOp Plus = Just ("+", 1)
infixOp Minus = Just ("-", 1)
infixOp Times = Just ("*", 2)
infixOp Div = Just ("/", 2)
infixOp Mod = Just ("%", 2)
infixOp (Rel r) = Just (relName r, 0)
infixOp _ = Nothing

relName :: Rel -> String
relName Eq = "="
relName NotEq = "!="
relName Lt = "<"
relName Gt = ">"
relName LtEq = "<="
relName GtEq = ">="

builtinName :: BuiltinFunct -> String
builtinName Size = "size"
builtinName First = "first"
builtinName Last = "last"
builtinName Get = "get"
builtinName Push = "push"
builtinName Pop = "pop"
builtinName Set = "set"
builtinName NewArray = "array"
builtinName ArrayFrom = "array"
builtinName NewBoxedArray = "Array::boxed"
builtinName NewEmptyArray = "Array::empty"
builtinName Unsize = "unsize"
builtinName NewBox = "Box::new"
builtinName UnBox = "Box::unbox"
builtinName Plus = "+"
builtinName Minus = "-"
builtinName Times = "*"
builtinName Div = "/"
builtinName Mod = "%"
builtinName (Rel r) = relName r
builtinName (Ctor name _) = name
builtinName (Field _ field) = "." ++ field
builtinName (Project _ field) = "." ++ field
builtinName (Cast variant) = "as " ++ variant
builtinName (Is variant) = "is " ++ variant
builtinName Within = "within"

renderValue :: Value -> String
renderValue (VInt i) = show i
renderValue (VBool b) = if b then "true" else "false"
renderValue (VData name []) = name
renderValue (VData name fields) = name ++ " { " ++ intercalate ", " [f ++ ": " ++ renderValue v | (f, v) <- fields] ++ " }"
renderValue (VList l) = "[" ++ intercalate ", " (map renderValue l) ++ "]"
renderValue (VFunct args _ _ _ _) = "fn(" ++ intercalate ", " args ++ ")"
renderValue (VFnRef name) = name

renderSize :: Size -> String
renderSize (SizeConst n) = show n
renderSize SizeAny = "?"
renderSize (SizeParam name) = name
renderSize (SizeVar n) = "_" ++ show n

-- Renders a type in Tersus syntax
renderType :: Type -> String
renderType TInt = "Int"
renderType TBool = "Bool"
renderType (TList t) = "List<" ++ renderType t ++ ">"
renderType (TBox t) = "Box<" ++ renderType t ++ ">"
renderType (TArrayOf t size) = "Array<" ++ renderType t ++ ", " ++ renderSize size ++ ">"
renderType (TRef t) = "&" ++ renderType t
renderType (TParam name) = name
renderType (TForall sizes types t) = "<" ++ intercalate ", " (types ++ sizes) ++ ">" ++ renderType t
renderType (TFn args ret) = "fn(" ++ intercalate ", " (map renderType args) ++ ") -> " ++ renderType ret
renderType (TNamed name) = filter (/= '`') name
renderType (TVariant name) = name
renderType (TVar _) = "?"
