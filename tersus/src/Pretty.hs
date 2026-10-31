module Pretty (renderProof, renderVarProof, renderValue, renderType) where

import Data.List (intercalate, stripPrefix)

import Types
import Syntax

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
    -- (a && b and a || b are looser than a relation, and an || inside an && is parenthesized)
    go prec (FApp (CTerm (VFunct _ _ _ (BuiltinFunct And) _)) [l, r]) =
        let operand x = case x of
                FApp (CTerm (VFunct _ _ _ (BuiltinFunct Or) _)) [_, _] -> "(" ++ go 0 x ++ ")"
                _ -> go 0 x
            text = operand l ++ " && " ++ operand r
         in if prec > 0 then "(" ++ text ++ ")" else text
    go prec (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Or) _)) [l, r]) =
        let text = go 0 l ++ " || " ++ go 0 r
         in if prec > 0 then "(" ++ text ++ ")" else text
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Not) _)) [x]) = "!" ++ go 3 x
    go prec (FApp (CTerm (VFunct _ _ _ (BuiltinFunct b) _)) [l, r])
        | Just (op, level) <- infixOp b =
            let text = go (max level 1) l ++ " " ++ op ++ " " ++ go (if level == 0 then 1 else level + 1) r
             in if prec > level then "(" ++ text ++ ")" else text
    -- (the bytes of a string written out are written as the list)
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct BytesFrom) _)) [bytes]) = go 0 bytes
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Field _ field)) _)) [struct]) = go 3 struct ++ "." ++ field
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Project _ field)) _)) [struct]) = go 3 struct ++ "." ++ field
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Cast variant)) _)) [value]) = "(" ++ go 1 value ++ " as " ++ variant ++ ")"
    go prec (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Is variant)) _)) [value]) =
        let text = go 1 value ++ " is " ++ variant
         in if prec > 0 then "(" ++ text ++ ")" else text
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name _ _)) _)) []) = name
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct (Ctor name _ fields)) _)) args)
        | length fields == length args = name ++ " { " ++ intercalate ", " (zipWith (\f a -> f ++ ": " ++ go 0 a) fields args) ++ " }"
    -- (what a permission says of a slot is read as the program writes it)
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [FApp (CTerm (VFunct _ _ _ (BuiltinFunct BlockFilled) _)) [blk], i]) = "filled(" ++ go 0 blk ++ ", " ++ go 0 i ++ ")"
    go _ (FApp (CTerm (VFunct _ _ _ (BuiltinFunct Get) _)) [FApp (CTerm (VFunct _ _ _ (BuiltinFunct BlockContents) _)) [blk], i]) = "at(" ++ go 0 blk ++ ", " ++ go 0 i ++ ")"
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
builtinName WriteByte = "writeByte"
builtinName WriteError = "writeError"
builtinName ReadByte = "readByte"
builtinName ArgCount = "argCount"
builtinName ArgByte = "argByte"
builtinName PathByte = "pathByte"
builtinName FileLoad = "fileLoad"
builtinName FileByte = "fileByte"
builtinName StoreByte = "storeByte"
builtinName FileStore = "fileStore"
builtinName ToByte = "toByte"
builtinName FromByte = "toInt"
builtinName BytesFrom = "bytes"
builtinName NewBox = "Box::new"
builtinName UnBox = "Box::unbox"
builtinName CloneOf = "clone"
builtinName Plus = "+"
builtinName Minus = "-"
builtinName Times = "*"
builtinName Div = "/"
builtinName Mod = "%"
builtinName And = "&&"
builtinName Or = "||"
builtinName Not = "!"
builtinName (Rel r) = relName r
builtinName (Ctor name _ _) = name
builtinName (Field _ field) = "." ++ field
builtinName (Project _ field) = "." ++ field
builtinName (Cast variant) = "as " ++ variant
builtinName (Is variant) = "is " ++ variant
builtinName Within = "within"
builtinName AddrNull = "Addr::null"
builtinName AddrOffset = "Addr::offset"
builtinName AddrCast = "Addr::cast"
builtinName AddrToInt = "Addr::toInt"
builtinName AddrFromInt = "Addr::fromInt"
builtinName AddrAlloc = "Addr::alloc"
builtinName AllocPair = "Addr::alloc"
builtinName AddrGet = "Addr::get"
builtinName AddrWrite = "Addr::write"
builtinName AddrTake = "Addr::take"
builtinName TakePair = "Addr::take"
builtinName AddrDropValue = "Addr::dropValue"
builtinName AddrDropRange = "Addr::dropRange"
builtinName AddrResize = "Addr::resize"
builtinName ResizePair = "Addr::resize"
builtinName AddrFree = "Addr::free"
builtinName SplitPair = "Block::split"
builtinName BlockNew = "Block::new"
builtinName BlockTaken = "Block::taken"
builtinName BlockResized = "Block::resized"
builtinName BlockSplitLo = "Block::lower"
builtinName BlockSplitHi = "Block::upper"
builtinName BlockJoin = "Block::join"
builtinName BlockAssume = "Block::assume"
builtinName BlockCast = "Block::cast"
builtinName BlockBase = "base"
builtinName BlockCap = "cap"
builtinName BlockFilled = "filledOf"
builtinName BlockContents = "contentsOf"
builtinName BlockOrigin = "origin"
builtinName BlockStart = "start"
builtinName BlockExtent = "extent"
builtinName BlockCount = "count"
builtinName UninitEmpty = "Uninit::empty"
builtinName UninitNew = "Uninit::new"
builtinName UninitGet = "Uninit::get"
builtinName UninitTake = "Uninit::take"
builtinName UninitDiscard = "Uninit::discard"
builtinName UninitFilled = "filled"
builtinName UninitAt = "at"
builtinName Replace = "replace"
builtinName (ToWord signed bits) = wordName signed bits ++ "::from"

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
renderType TByte = "Byte"
renderType TBool = "Bool"
renderType (TWord signed bits) = wordName signed bits
renderType (TList t) = "List<" ++ renderType t ++ ">"
renderType (TBox t) = "Box<" ++ renderType t ++ ">"
renderType (TAddr t) = "Addr<" ++ renderType t ++ ">"
renderType (TBlock t) = "Block<" ++ renderType t ++ ">"
renderType (TUninit t) = "Uninit<" ++ renderType t ++ ">"
renderType (TArrayOf t size) = "Array<" ++ renderType t ++ ", " ++ renderSize size ++ ">"
renderType (TRef t) = "&" ++ renderType t
renderType (TParam name) = name
renderType (TForall sizes types t) = "<" ++ intercalate ", " (types ++ sizes) ++ ">" ++ renderType t
renderType (TFn args ret) = "fn(" ++ intercalate ", " (map renderType args) ++ ") -> " ++ renderType ret
renderType (TNamed base args) = instanceName base args
renderType (TVariant name) = name
renderType (TVar _) = "?"
