module StdLib
    ( builtinFunct
    , comparable
    , eqProof
    , eqVarProof
    , evalBuiltinFunct
    , relProof
    , stdLibRuleCtx
    , stdlibBuiltinDecls
    ) where

import Data.Map (Map, fromList, toList)

import TersusTypes
import Utils

-- TODO: Separate this into primitive functions and true std lib
-- TODO: Write std lib as text to be parsed

builtinFunct :: BuiltinFunct -> Value
-- first and last are get at the first and the last index, which is how element facts about the list reach them
-- get requires a valid index, and its result is equal to the term get(list, index), which is what
-- forall facts about the list are instantiated at. The contract is checked with checkRel so that a concrete
-- list and index need no proof from the caller, while symbolic ones must already have
-- 0 <= index < size(list) in the proof context.
-- push adds an element at the end, so the result is one longer than the input list and its
-- last element (at the old size) is x. The elements it already had are unchanged. The result is
-- also equal to the term push(list, x).
-- pop takes the last element out, so the list must have one; the result is one shorter and keeps the others in their places. The
-- result is also equal to the term pop(list).
-- set replaces one element, so it needs a valid index like get, and the result has the same
-- size as the input list, and x at that index. The list itself is not changed: the result is
-- a new list. Every other element is unchanged. The result is also equal to the term
-- set(list, index, x).
-- array(n, x) is an array of n copies of x, so it needs a size that is not negative. Its size is n and every element is x;
-- the result is also equal to the term array(n, x). An array has no push: its size never changes, which is all that makes this
-- a fact a caller can keep.
-- Array::boxed(n, x) promises what array(n, x) does, for an n that need not be a constant
-- Array::empty() is the array of no elements
-- writeError(b) is writeByte(b) on the standard error
-- writeByte(b) writes the Byte b to the standard output and is b
-- toByte(x) is x as a Byte: x has to be from 0 to 255. toInt(b) is b as an Int.
-- The List<Byte> of a list of Ints that is written out: the same list
-- argCount() is the number of arguments of the program, argByte(i, j) the byte j of argument i, or -1 when there is no such argument or byte
-- The files: a path is built a byte at a time (pathByte), and then the file at it is loaded (fileLoad: its size, or -1) and read a byte at a time
-- (fileByte(i): the byte i, or -1), or a file is built a byte at a time (storeByte) and stored (fileStore: 0, or -1) in the file at the path
-- readByte() is the next byte of the standard input, or -1 at its end: it is not known beyond that, so a program has to test what it relies on
-- Unsize b is b: the Box has the same value, it carries the size
-- The array that a literal makes is the list of its elements, read as an array: the same value
-- Box::new(x) is x: a Box has the value of what it holds
-- clone(x) is x: a copy has the value of what it copies
-- The builtins lib/stdlib.tersus declares: their contracts are written there, and StdLibDefs is where
-- they are read from. The value made here, which is how a proof names such a builtin, carries none.
builtinFunct b | Just params <- lookup b stdlibDeclaredParams = VFunct params [] [] (BuiltinFunct b) []
builtinFunct CloneOf = VFunct ["value"] [] [] (BuiltinFunct CloneOf) []
-- References are made and read in the MIR, never called: these are only how they are named in a proof term
builtinFunct BorrowOf = VFunct ["place"] [] [] (BuiltinFunct BorrowOf) []
builtinFunct BorrowMutOf = VFunct ["place"] [] [] (BuiltinFunct BorrowMutOf) []
builtinFunct DerefOf = VFunct ["reference"] [] [] (BuiltinFunct DerefOf) []
builtinFunct OldOf = VFunct ["place"] [] [] (BuiltinFunct OldOf) []
builtinFunct (Ctor name fields) = VFunct fields [] [] (BuiltinFunct (Ctor name fields)) []
builtinFunct (Field owner field) = VFunct ["struct"] [] [] (BuiltinFunct (Field owner field)) []
builtinFunct (Is variant) = VFunct ["value"] [] [] (BuiltinFunct (Is variant)) []
-- A cast demands the proof that the value is the variant, and does nothing when it runs
builtinFunct (Cast variant) =
    VFunct
        ["value"]
        [ProofAssert (FApp (CTerm (builtinFunct (Is variant))) [ATerm "value"])]
        []
        (BuiltinFunct (Cast variant))
        []
builtinFunct (Project variant field) = VFunct ["value"] [] [] (BuiltinFunct (Project variant field)) []
-- Division by zero is rejected, like an out of range index: the divisor must already be known to be non-zero
-- Modulo by zero is rejected the same way
-- Addresses (POINTERS.md). The address of an offset is the term offset(p, i), so the base of the upper part of a split block is that term too.
builtinFunct AddrNull = VFunct [] [] [] (BuiltinFunct AddrNull) []
builtinFunct AddrOffset = VFunct ["p", "i"] [] [] (BuiltinFunct AddrOffset) []
-- The cast of an address is the term cast(p), and not p: offset(p, i) is i slots of the type of p further on, so offsets of an address and of
-- its cast are not the same address unless the types have the same size, which the validator does not know
builtinFunct AddrCast = VFunct ["p"] [] [] (BuiltinFunct AddrCast) []
builtinFunct AddrToInt = VFunct ["p"] [] [] (BuiltinFunct AddrToInt) []
builtinFunct AddrFromInt = VFunct ["n"] [] [] (BuiltinFunct AddrFromInt) [relProof Eq (ptrApp AddrToInt [ATerm "return"]) (ATerm "n")]
-- n new slots: the address is new (AddrAlloc reads the world), and nothing is known of it but what its permission, BlockNew, says
builtinFunct AddrAlloc = VFunct ["n"] [atLeastZero (ATerm "n")] [] (BuiltinFunct AddrAlloc) []
builtinFunct BlockNew = VFunct ["p", "n"] [] [] (BuiltinFunct BlockNew) (newBlock (ATerm "p") (ATerm "n"))
-- the value in a filled slot, which is at(b, i) (a view: the slot keeps it)
builtinFunct AddrGet =
    VFunct ["p", "i", "b"] (slotOf "b" ++ [isFilled "b" (ATerm "i")]) [] (BuiltinFunct AddrGet) [relProof Eq (ATerm "return") (blockAt (ATerm "b") (ATerm "i"))]
-- a value written into an empty slot: the permission after says it is filled with it, and is the same everywhere else
builtinFunct AddrWrite =
    VFunct
        ["p", "i", "x", "b"]
        (slotOf "b" ++ [isEmpty "b" (ATerm "i")])
        []
        (BuiltinFunct AddrWrite)
        ( keeps "return" "b"
            ++ [ relProof Eq (blockCount (ATerm "return")) (plusProof (blockCount (ATerm "b")) (CTerm (VInt 1)))
               , relProof Eq (blockFilled (ATerm "return") (ATerm "i")) (CTerm (VBool True))
               , relProof Eq (blockAt (ATerm "return") (ATerm "i")) (ATerm "x")
               ]
            ++ sameExcept "return" "b" (ATerm "i")
        )
-- the value of a filled slot, taken out: it is at(b, i), and BlockTaken is the permission with the slot empty
builtinFunct AddrTake =
    VFunct ["p", "i", "b"] (slotOf "b" ++ [isFilled "b" (ATerm "i")]) [] (BuiltinFunct AddrTake) [relProof Eq (ATerm "return") (blockAt (ATerm "b") (ATerm "i"))]
builtinFunct BlockTaken = VFunct ["b", "i"] [] [] (BuiltinFunct BlockTaken) (emptied "return" "b" (ATerm "i"))
builtinFunct AddrDropValue =
    VFunct ["p", "i", "b"] (slotOf "b" ++ [isFilled "b" (ATerm "i")]) [] (BuiltinFunct AddrDropValue) (emptied "return" "b" (ATerm "i"))
-- the values of the slots i to i + n - 1, all filled, dropped where they are
builtinFunct AddrDropRange =
    VFunct
        ["p", "i", "n", "b"]
        [ ProofAssert (relProof Eq (blockBase (ATerm "b")) (ATerm "p"))
        , atLeastZero (ATerm "i")
        , atLeastZero (ATerm "n")
        , ProofAssert (relProof LtEq (plusProof (ATerm "i") (ATerm "n")) (blockCap (ATerm "b")))
        , ProofAssert (indexIn "j" (ATerm "i") (plusProof (ATerm "i") (ATerm "n")) (relProof Eq (blockFilled (ATerm "b") (BVar "j")) (CTerm (VBool True))))
        ]
        []
        (BuiltinFunct AddrDropRange)
        ( keeps "return" "b"
            ++ [ indexIn "j" (ATerm "i") (plusProof (ATerm "i") (ATerm "n")) (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (CTerm (VBool False)))
               , indexIn "j" (CTerm (VInt 0)) (ATerm "i") (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
               , indexIn "j" (plusProof (ATerm "i") (ATerm "n")) (blockCap (ATerm "b")) (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
               , relProof Eq (ptrApp BlockContents [ATerm "return"]) (ptrApp BlockContents [ATerm "b"])
               , relProof Eq (blockCount (ATerm "return")) (minusProof (blockCount (ATerm "b")) (ATerm "n"))
               ]
        )
-- a whole allocation, moved to one of n slots (a new allocation, so a new address): the slots from n are empty, and the permission after,
-- BlockResized, has the values of the slots below n and of the old size
builtinFunct AddrResize =
    VFunct ["p", "n", "b"] ([ProofAssert (relProof Eq (blockBase (ATerm "b")) (ATerm "p")), atLeastZero (ATerm "n")] ++ isWhole "b" ++ [ProofAssert (indexIn "j" (ATerm "n") (blockCap (ATerm "b")) (relProof Eq (blockFilled (ATerm "b") (BVar "j")) (CTerm (VBool False))))]) [] (BuiltinFunct AddrResize) []
builtinFunct BlockResized =
    VFunct
        ["b", "q", "n"]
        []
        []
        (BuiltinFunct BlockResized)
        ( newBlockFacts (ATerm "q") (ATerm "n")
            ++ [ relProof Eq (blockCount (ATerm "return")) (blockCount (ATerm "b"))
               , Forall "j" [relProof GtEq (BVar "j") (CTerm (VInt 0)), relProof Lt (BVar "j") (ATerm "n"), relProof Lt (BVar "j") (blockCap (ATerm "b"))] (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
               , Forall "j" [relProof GtEq (BVar "j") (CTerm (VInt 0)), relProof Lt (BVar "j") (ATerm "n"), relProof Lt (BVar "j") (blockCap (ATerm "b"))] (relProof Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "b") (BVar "j")))
               , Forall "j" [relProof GtEq (BVar "j") (blockCap (ATerm "b")), relProof Lt (BVar "j") (ATerm "n")] (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (CTerm (VBool False)))
               ]
        )
-- an allocation given back: the whole of it, with nothing left in it
builtinFunct AddrFree =
    VFunct ["p", "b"] ([ProofAssert (relProof Eq (blockBase (ATerm "b")) (ATerm "p"))] ++ isWhole "b" ++ [noneFilled "b"]) [] (BuiltinFunct AddrFree) [relProof Eq (ATerm "return") (CTerm (VInt 0))]
-- The parts of a block: slots 0 to i - 1 and i to the end, of the same allocation
builtinFunct BlockSplitLo =
    VFunct
        ["b", "i"]
        [atLeastZero (ATerm "i"), ProofAssert (relProof LtEq (ATerm "i") (blockCap (ATerm "b")))]
        []
        (BuiltinFunct BlockSplitLo)
        [ relProof Eq (blockBase (ATerm "return")) (blockBase (ATerm "b"))
        , relProof Eq (blockCap (ATerm "return")) (ATerm "i")
        , relProof Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "b"))
        , relProof Eq (blockStart (ATerm "return")) (blockStart (ATerm "b"))
        , relProof GtEq (blockCount (ATerm "return")) (CTerm (VInt 0))
        , relProof LtEq (blockCount (ATerm "return")) (blockCount (ATerm "b"))
        , indexIn "j" (CTerm (VInt 0)) (ATerm "i") (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (BVar "j")))
        , indexIn "j" (CTerm (VInt 0)) (ATerm "i") (relProof Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "b") (BVar "j")))
        ]
builtinFunct BlockSplitHi =
    VFunct
        ["b", "i"]
        [atLeastZero (ATerm "i"), ProofAssert (relProof LtEq (ATerm "i") (blockCap (ATerm "b")))]
        []
        (BuiltinFunct BlockSplitHi)
        [ relProof Eq (blockBase (ATerm "return")) (ptrApp AddrOffset [blockBase (ATerm "b"), ATerm "i"])
        , relProof Eq (blockCap (ATerm "return")) (minusProof (blockCap (ATerm "b")) (ATerm "i"))
        , relProof Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "b"))
        , relProof Eq (blockStart (ATerm "return")) (plusProof (blockStart (ATerm "b")) (ATerm "i"))
        , relProof Eq (blockCount (ATerm "return")) (minusProof (blockCount (ATerm "b")) (blockCount (ptrApp BlockSplitLo [ATerm "b", ATerm "i"])))
        , relProof GtEq (blockCount (ATerm "return")) (CTerm (VInt 0))
        , indexIn "j" (CTerm (VInt 0)) (minusProof (blockCap (ATerm "b")) (ATerm "i")) (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "b") (plusProof (ATerm "i") (BVar "j"))))
        , indexIn "j" (CTerm (VInt 0)) (minusProof (blockCap (ATerm "b")) (ATerm "i")) (relProof Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "b") (plusProof (ATerm "i") (BVar "j"))))
        ]
-- Two blocks that are next to each other in one allocation, as one
builtinFunct BlockJoin =
    VFunct
        ["lo", "hi"]
        [ ProofAssert (relProof Eq (blockOrigin (ATerm "lo")) (blockOrigin (ATerm "hi")))
        , ProofAssert (relProof Eq (blockStart (ATerm "hi")) (plusProof (blockStart (ATerm "lo")) (blockCap (ATerm "lo"))))
        ]
        []
        (BuiltinFunct BlockJoin)
        [ relProof Eq (blockBase (ATerm "return")) (blockBase (ATerm "lo"))
        , relProof Eq (blockCap (ATerm "return")) (plusProof (blockCap (ATerm "lo")) (blockCap (ATerm "hi")))
        , relProof Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "lo"))
        , relProof Eq (blockStart (ATerm "return")) (blockStart (ATerm "lo"))
        , relProof Eq (blockCount (ATerm "return")) (plusProof (blockCount (ATerm "lo")) (blockCount (ATerm "hi")))
        , indexIn "j" (CTerm (VInt 0)) (blockCap (ATerm "lo")) (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "lo") (BVar "j")))
        , indexIn "j" (CTerm (VInt 0)) (blockCap (ATerm "lo")) (relProof Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "lo") (BVar "j")))
        , indexIn "j" (blockCap (ATerm "lo")) (plusProof (blockCap (ATerm "lo")) (blockCap (ATerm "hi"))) (relProof Eq (blockFilled (ATerm "return") (BVar "j")) (blockFilled (ATerm "hi") (minusProof (BVar "j") (blockCap (ATerm "lo")))))
        , indexIn "j" (blockCap (ATerm "lo")) (plusProof (blockCap (ATerm "lo")) (blockCap (ATerm "hi"))) (relProof Eq (blockAt (ATerm "return") (BVar "j")) (blockAt (ATerm "hi") (minusProof (BVar "j") (blockCap (ATerm "lo")))))
        ]
-- The permission to memory the program did not allocate: an assumption (`tersus assumptions` lists it)
builtinFunct BlockAssume = VFunct ["p", "n"] [atLeastZero (ATerm "n")] [] (BuiltinFunct BlockAssume) (newBlock (ATerm "p") (ATerm "n"))
-- The same memory as slots of another type of the same size, with nothing in it
builtinFunct BlockCast =
    VFunct
        ["b"]
        [noneFilled "b"]
        []
        (BuiltinFunct BlockCast)
        [ relProof Eq (blockBase (ATerm "return")) (ptrApp AddrCast [blockBase (ATerm "b")])
        , relProof Eq (blockCap (ATerm "return")) (blockCap (ATerm "b"))
        , relProof Eq (blockOrigin (ATerm "return")) (blockOrigin (ATerm "b"))
        , relProof Eq (blockStart (ATerm "return")) (blockStart (ATerm "b"))
        , relProof Eq (blockCount (ATerm "return")) (CTerm (VInt 0))
        , allEmpty "return"
        ]
-- I32::from(x) and the others: x has to be in the range of the type, and is the same number
builtinFunct (ToWord signed bits) =
    let (low, high) = wordRange signed bits
     in VFunct
            ["x"]
            [ Rewrite (CheckRel (relProof GtEq (ATerm "x") (CTerm (VInt low))))
            , ProofAssert (relProof GtEq (ATerm "x") (CTerm (VInt low)))
            , Rewrite (CheckRel (relProof Lt (ATerm "x") (CTerm (VInt high))))
            , ProofAssert (relProof Lt (ATerm "x") (CTerm (VInt high)))
            ]
            []
            (BuiltinFunct (ToWord signed bits))
            [relProof Eq (ATerm "return") (ATerm "x")]
-- Uninit<T>: whether one holds a value, and the value, are filled(u) and at(u)
builtinFunct UninitEmpty = VFunct [] [] [] (BuiltinFunct UninitEmpty) [relProof Eq (uninitFilled (ATerm "return")) (CTerm (VBool False))]
builtinFunct UninitNew =
    VFunct ["x"] [] [] (BuiltinFunct UninitNew) [relProof Eq (uninitFilled (ATerm "return")) (CTerm (VBool True)), relProof Eq (ptrApp UninitAt [ATerm "return"]) (ATerm "x")]
builtinFunct UninitGet =
    VFunct ["u"] [ProofAssert (relProof Eq (uninitFilled (ATerm "u")) (CTerm (VBool True)))] [] (BuiltinFunct UninitGet) [relProof Eq (ATerm "return") (ptrApp UninitAt [ATerm "u"])]
builtinFunct UninitTake =
    VFunct ["u"] [ProofAssert (relProof Eq (uninitFilled (ATerm "u")) (CTerm (VBool True)))] [] (BuiltinFunct UninitTake) [relProof Eq (ATerm "return") (ptrApp UninitAt [ATerm "u"])]
builtinFunct UninitDiscard =
    VFunct ["u"] [ProofAssert (relProof Eq (uninitFilled (ATerm "u")) (CTerm (VBool False)))] [] (BuiltinFunct UninitDiscard) [relProof Eq (ATerm "return") (CTerm (VInt 0))]
builtinFunct UninitFilled = VFunct ["u"] [] [] (BuiltinFunct UninitFilled) []
builtinFunct UninitAt = VFunct ["u"] [] [] (BuiltinFunct UninitAt) []
builtinFunct Replace = VFunct ["list", "index", "x"] [] [] (BuiltinFunct Replace) []
-- (the forms a program writes, which the lowering takes apart, and the functions of a permission, which have no contract)
builtinFunct b | b `elem` [AllocPair, TakePair, ResizePair, SplitPair, BlockBase, BlockCap, BlockFilled, BlockContents, BlockOrigin, BlockStart, BlockExtent, BlockCount] =
    VFunct (map (\i -> "a" ++ show i) [1 .. ptrArity b]) [] [] (BuiltinFunct b) []
builtinFunct And = VFunct ["a", "b"] [] [] (BuiltinFunct And) []
builtinFunct Or = VFunct ["a", "b"] [] [] (BuiltinFunct Or) []
builtinFunct Not = VFunct ["a"] [] [] (BuiltinFunct Not) []
builtinFunct (Rel rel) = VFunct ["a", "b"] [] [] (BuiltinFunct (Rel rel)) []
builtinFunct Within = VFunct ["a", "b"] [] [] (BuiltinFunct Within) []

-- Evaluates a builtin function on concrete arguments
evalBuiltinFunct :: BuiltinFunct -> [Value] -> Result Value String
evalBuiltinFunct Size [VList l] = Ok $ VInt (fromIntegral (length l))
evalBuiltinFunct Size _ = Error "Size only valid for a list"
evalBuiltinFunct First [VList []] = Error "First requires a non-empty list"
evalBuiltinFunct First [VList l] = Ok $ head l
evalBuiltinFunct First _ = Error "First only valid for a list"
evalBuiltinFunct Last [VList []] = Error "Last requires a non-empty list"
evalBuiltinFunct Last [VList l] = Ok $ last l
evalBuiltinFunct Last _ = Error "Last only valid for a list"
evalBuiltinFunct Get [VList l, VInt i]
    | i < 0 || i >= fromIntegral (length l) = Error "Get index out of range"
    | otherwise = Ok $ l !! fromIntegral i
evalBuiltinFunct Get _ = Error "Get only valid for a list and an int"
evalBuiltinFunct Push [VList l, x] = Ok $ VList (l ++ [x])
evalBuiltinFunct Push _ = Error "Push only valid for a list and an element"
evalBuiltinFunct Pop [VList []] = Error "Pop requires a non-empty list"
evalBuiltinFunct Pop [VList l] = Ok $ VList (init l)
evalBuiltinFunct Pop _ = Error "Pop only valid for a list"
evalBuiltinFunct Set [VList l, VInt i, x]
    | i < 0 || i >= fromIntegral (length l) = Error "Set index out of range"
    | otherwise = let (before, after) = splitAt (fromIntegral i) l in Ok $ VList (before ++ x : drop 1 after)
evalBuiltinFunct Set _ = Error "Set only valid for a list, an int and an element"
-- (an array too large to write out is not evaluated: the validator knows its size from the contract, and does not need it)
evalBuiltinFunct NewArray [VInt n, x]
    | n >= 0 && n <= maxUnfolded = Ok $ VList (replicate (fromIntegral n) x)
    | otherwise = Error "The array is not evaluated"
evalBuiltinFunct NewArray _ = Error "array takes a size and an element"
evalBuiltinFunct NewBoxedArray args = evalBuiltinFunct NewArray args
evalBuiltinFunct NewEmptyArray [] = Ok (VList [])
evalBuiltinFunct WriteByte [VInt b] = Ok (VInt b)
evalBuiltinFunct WriteByte _ = Error "writeByte takes one byte"
evalBuiltinFunct WriteError [VInt b] = Ok (VInt b)
evalBuiltinFunct WriteError _ = Error "writeError takes one byte"
evalBuiltinFunct ToByte [VInt x]
    | x >= 0 && x < 256 = Ok (VInt x)
    | otherwise = Error "toByte needs an Int from 0 to 255"
evalBuiltinFunct ToByte _ = Error "toByte takes one Int"
evalBuiltinFunct FromByte [VInt b] = Ok (VInt b)
evalBuiltinFunct (ToWord signed bits) [VInt x]
    | x >= fst (wordRange signed bits) && x < snd (wordRange signed bits) = Ok (VInt x)
    | otherwise = Error (wordName signed bits ++ "::from needs an Int in the range of " ++ wordName signed bits)
evalBuiltinFunct FromByte _ = Error "toInt takes one Byte"
evalBuiltinFunct BytesFrom [VList l]
    | all isByte l = Ok (VList l)
  where
    isByte (VInt x) = x >= 0 && x < 256
    isByte _ = False
evalBuiltinFunct BytesFrom _ = Error "A list of bytes is written with numbers from 0 to 255"
-- (not a value that can be worked out: what it gives is the input, which a proof does not have, so the proof engine may not fold a call to a constant)
evalBuiltinFunct ReadByte _ = Error "readByte reads the input, so it has no value to evaluate"
evalBuiltinFunct ArgCount _ = Error "argCount is the arguments of the program, so it has no value to evaluate"
evalBuiltinFunct ArgByte _ = Error "argByte is the arguments of the program, so it has no value to evaluate"
evalBuiltinFunct b _ | b `elem` [PathByte, FileLoad, FileByte, StoreByte, FileStore] = Error "a file operation is the files of the program, so it has no value to evaluate"
evalBuiltinFunct Unsize [value] = Ok value
evalBuiltinFunct Unsize _ = Error "unsize takes one Box"
evalBuiltinFunct ArrayFrom [VList l] = Ok $ VList l
evalBuiltinFunct ArrayFrom _ = Error "An array literal is made from a list"
evalBuiltinFunct NewBox [value] = Ok value
evalBuiltinFunct NewBox _ = Error "Box::new takes one value"
evalBuiltinFunct UnBox [value] = Ok value
evalBuiltinFunct UnBox _ = Error "Box::unbox takes one Box"
evalBuiltinFunct CloneOf [value] = Ok value
evalBuiltinFunct CloneOf _ = Error "clone takes one value"
evalBuiltinFunct (Ctor name fields) args
    | length fields == length args = Ok $ VData name (zip fields args)
    | otherwise = Error ("Struct " ++ name ++ " takes " ++ show (length fields) ++ " fields, got " ++ show (length args))
evalBuiltinFunct (Field owner field) [VData name fields]
    | maybe False (/= name) owner = Error ("Expected a " ++ maybe "" id owner ++ " but got a " ++ name)
    | otherwise =
    case lookup field fields of
        Just value -> Ok value
        Nothing -> Error ("Struct " ++ name ++ " has no field " ++ field ++ " (reading it after a cast to the wrong variant is undefined behaviour)")
evalBuiltinFunct (Is variant) [VData name _] = Ok $ VBool (name == variant)
evalBuiltinFunct (Is _) _ = Error "Is only tests the variant of an enum value"
evalBuiltinFunct (Project variant field) [VData name fields]
    | name /= variant = Error ("Expected a " ++ variant ++ " but got a " ++ name)
    | otherwise = maybe (Error ("Variant " ++ variant ++ " has no field " ++ field)) Ok (lookup field fields)
evalBuiltinFunct Within [inner, outer] = Ok $ VBool (partOf inner outer)
  where
    partOf part (VData _ fields) = any (\(_, field) -> field == part || partOf part field) fields
    partOf _ _ = False
evalBuiltinFunct Within _ = Error "Within takes two values"
evalBuiltinFunct (Cast _) [value] = Ok value
evalBuiltinFunct (Cast _) _ = Error "A cast takes one value"
evalBuiltinFunct (Project _ _) _ = Error "A field can only be read from an enum value"
evalBuiltinFunct (Field _ _) _ = Error "A field can only be read from a struct"
evalBuiltinFunct Minus [VInt v1, VInt v2] = checkedInt (v1 - v2)
evalBuiltinFunct Minus _ = Error "Minus only valid for two ints"
evalBuiltinFunct Plus [VInt v1, VInt v2] = checkedInt (v1 + v2)
evalBuiltinFunct Plus _ = Error "Plus only valid for two ints"
evalBuiltinFunct Times [VInt v1, VInt v2] = checkedInt (v1 * v2)
evalBuiltinFunct Times _ = Error "Times only valid for two ints"
evalBuiltinFunct Div [VInt _, VInt 0] = Error "Division by zero"
evalBuiltinFunct Div [VInt v1, VInt v2] = checkedInt (v1 `div` v2)
evalBuiltinFunct Div _ = Error "Div only valid for two ints"
evalBuiltinFunct Mod [VInt _, VInt 0] = Error "Modulo by zero"
evalBuiltinFunct Mod [VInt v1, VInt v2] = Ok $ VInt (v1 `mod` v2)
evalBuiltinFunct Mod _ = Error "Mod only valid for two ints"
evalBuiltinFunct And [VBool a, VBool b] = Ok (VBool (a && b))
evalBuiltinFunct And _ = Error "&& only valid for two Bools"
evalBuiltinFunct Or [VBool a, VBool b] = Ok (VBool (a || b))
evalBuiltinFunct Or _ = Error "|| only valid for two Bools"
evalBuiltinFunct Not [VBool a] = Ok (VBool (not a))
evalBuiltinFunct Not _ = Error "! only valid for a Bool"
evalBuiltinFunct (Rel Eq) [v1, v2] | comparable v1 v2 = Ok $ VBool (v1 == v2)
evalBuiltinFunct (Rel Eq) _ = Error "Eq only valid for two values of the same kind that are not functions"
evalBuiltinFunct (Rel NotEq) [v1, v2] | comparable v1 v2 = Ok $ VBool (v1 /= v2)
evalBuiltinFunct (Rel NotEq) _ = Error "NotEq only valid for two values of the same kind that are not functions"
evalBuiltinFunct (Rel Lt) [VInt v1, VInt v2] = Ok $ VBool (v1 < v2)
evalBuiltinFunct (Rel Lt) _ = Error "Lt only valid for two ints"
evalBuiltinFunct (Rel Gt) [VInt v1, VInt v2] = Ok $ VBool (v1 > v2)
evalBuiltinFunct (Rel Gt) _ = Error "Rt only valid for two ints"
evalBuiltinFunct (Rel LtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 <= v2)
evalBuiltinFunct (Rel LtEq) _ = Error "LtEq only valid for two ints"
evalBuiltinFunct (Rel GtEq) [VInt v1, VInt v2] = Ok $ VBool (v1 >= v2)
evalBuiltinFunct (Rel GtEq) _ = Error "GtEq only valid for two ints"
-- (an address is not a value a proof works out: it is new at each allocation, and memory is what a permission says)
evalBuiltinFunct b _ = Error (show b ++ " is an operation on memory, so it has no value to evaluate")

-- The parts of the contracts of addresses and permissions

ptrArity :: BuiltinFunct -> Int
ptrArity b = case b of
    AllocPair -> 1
    TakePair -> 3
    ResizePair -> 3
    SplitPair -> 2
    BlockFilled -> 1
    BlockContents -> 1
    _ -> 1

-- (the term of a builtin applied: the symbol has no contract, as getSymbol)
ptrApp :: BuiltinFunct -> [VariableProof] -> VariableProof
ptrApp b args = FApp (CTerm (VFunct [] [] [] (BuiltinFunct b) [])) args

uninitFilled :: VariableProof -> VariableProof
uninitFilled u = ptrApp UninitFilled [u]

blockBase, blockCap, blockOrigin, blockStart, blockCount :: VariableProof -> VariableProof
blockCount b = ptrApp BlockCount [b]
blockBase b = ptrApp BlockBase [b]
blockCap b = ptrApp BlockCap [b]
blockOrigin b = ptrApp BlockOrigin [b]
blockStart b = ptrApp BlockStart [b]

-- filled(b, i) and at(b, i): elements of two ghost arrays, so that what the proof engine knows of arrays is known of them
blockFilled, blockAt :: VariableProof -> VariableProof -> VariableProof
blockFilled b i = FApp (CTerm getSymbol) [ptrApp BlockFilled [b], i]
blockAt b i = FApp (CTerm getSymbol) [ptrApp BlockContents [b], i]

plusProof, minusProof :: VariableProof -> VariableProof -> VariableProof
plusProof x y = FApp (CTerm (builtinFunct Plus)) [x, y]
minusProof x y = FApp (CTerm (builtinFunct Minus)) [x, y]

atLeastZero :: VariableProof -> ValidationStatement
atLeastZero x = ProofAssert (relProof GtEq x (CTerm (VInt 0)))

-- forall j in lo..hi: body
indexIn :: Variable -> VariableProof -> VariableProof -> VariableProof -> VariableProof
indexIn j lo hi = Forall j [relProof GtEq (BVar j) lo, relProof Lt (BVar j) hi]

-- The slot i of the block b, at the address p: p is the address b is the permission to, and i is one of its slots
slotOf :: Variable -> [ValidationStatement]
slotOf b =
    [ ProofAssert (relProof Eq (blockBase (ATerm b)) (ATerm "p"))
    , atLeastZero (ATerm "i")
    , ProofAssert (relProof Lt (ATerm "i") (blockCap (ATerm b)))
    ]

isFilled, isEmpty :: Variable -> VariableProof -> ValidationStatement
isFilled b i = ProofAssert (relProof Eq (blockFilled (ATerm b) i) (CTerm (VBool True)))
isEmpty b i = ProofAssert (relProof Eq (blockFilled (ATerm b) i) (CTerm (VBool False)))

-- whole(b): the block is all of its allocation, which starts at 0 and is as long as the allocation
isWhole :: Variable -> [ValidationStatement]
isWhole b =
    [ ProofAssert (relProof Eq (blockStart (ATerm b)) (CTerm (VInt 0)))
    , ProofAssert (relProof Eq (blockCap (ATerm b)) (ptrApp BlockExtent [blockOrigin (ATerm b)]))
    ]

allEmpty :: Variable -> VariableProof
allEmpty b = indexIn "j" (CTerm (VInt 0)) (blockCap (ATerm b)) (relProof Eq (blockFilled (ATerm b) (BVar "j")) (CTerm (VBool False)))

-- No slot of the block is filled
noneFilled :: Variable -> ValidationStatement
noneFilled b = ProofAssert (relProof Eq (blockCount (ATerm b)) (CTerm (VInt 0)))

-- A new allocation of n slots at p: whole, and nothing in it
newBlock :: VariableProof -> VariableProof -> [VariableProof]
newBlock p n = newBlockFacts p n ++ [relProof Eq (blockCount (ATerm "return")) (CTerm (VInt 0)), allEmpty "return"]

newBlockFacts :: VariableProof -> VariableProof -> [VariableProof]
newBlockFacts p n =
    [ relProof Eq (blockBase (ATerm "return")) p
    , relProof Eq (blockCap (ATerm "return")) n
    , relProof GtEq (blockCap (ATerm "return")) (CTerm (VInt 0))
    , relProof Eq (blockStart (ATerm "return")) (CTerm (VInt 0))
    , relProof Eq (ptrApp BlockExtent [blockOrigin (ATerm "return")]) n
    ]

-- The block r is the block b in what it is for
keeps :: Variable -> Variable -> [VariableProof]
keeps r b =
    [ relProof Eq (blockBase (ATerm r)) (blockBase (ATerm b))
    , relProof Eq (blockCap (ATerm r)) (blockCap (ATerm b))
    , relProof Eq (blockOrigin (ATerm r)) (blockOrigin (ATerm b))
    , relProof Eq (blockStart (ATerm r)) (blockStart (ATerm b))
    ]

-- Every slot but i is as it was
sameExcept :: Variable -> Variable -> VariableProof -> [VariableProof]
sameExcept r b i =
    [ Forall "j" guards (relProof Eq (blockFilled (ATerm r) (BVar "j")) (blockFilled (ATerm b) (BVar "j")))
    , Forall "j" guards (relProof Eq (blockAt (ATerm r) (BVar "j")) (blockAt (ATerm b) (BVar "j")))
    ]
  where
    guards = [relProof GtEq (BVar "j") (CTerm (VInt 0)), relProof Lt (BVar "j") (blockCap (ATerm b)), relProof NotEq (BVar "j") i]

-- The block b with the slot i empty
emptied :: Variable -> Variable -> VariableProof -> [VariableProof]
emptied r b i =
    keeps r b
        ++ [relProof Eq (blockFilled (ATerm r) i) (CTerm (VBool False)), relProof Eq (blockCount (ATerm r)) (minusProof (blockCount (ATerm b)) (CTerm (VInt 1)))]
        ++ sameExcept r b i

eqProof :: IotaProof
eqProof = CTerm (builtinFunct (Rel Eq))

eqVarProof :: VariableProof
eqVarProof = CTerm (builtinFunct (Rel Eq))

stdLibRuleCtx :: RuleContext
stdLibRuleCtx =
    fromList
        [ ( "eqToLtPlus1"
          , AxiomRule
                ["x"]
                []
                [ AssignProofVar "xPlusOne" (F (Val (builtinFunct Plus)) [Var "x", Val (VInt 1)])
                , ProofAssert
                    ( FApp
                        (CTerm (builtinFunct (Rel Lt)))
                        [ATerm "x", ATerm "xPlusOne"]
                    )
                ]
          )
        , ( "eqToGtZero"
          , AxiomRule
                ["x"]
                [ Rewrite (CheckGtZero (ATerm "x"))
                , ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])
                ]
                [ProofAssert (FApp (CTerm (builtinFunct (Rel Gt))) [ATerm "x", CTerm (VInt 0)])]
          )
        ]

-- Function symbols for the terms push(list, x) and set(list, index, x) in contracts and frame
-- rules. They cannot be the full builtin values, which contain these very contracts.
getSymbol :: Value
getSymbol = VFunct ["list", "index"] [] [] (BuiltinFunct Get) []

popSymbol :: Value
popSymbol = VFunct ["list"] [] [] (BuiltinFunct Pop) []

pushSymbol :: Value
pushSymbol = VFunct ["list", "x"] [] [] (BuiltinFunct Push) []

setSymbol :: Value
setSymbol = VFunct ["list", "index", "x"] [] [] (BuiltinFunct Set) []

newArraySymbol :: Value
newArraySymbol = VFunct ["n", "x"] [] [] (BuiltinFunct NewArray) []

-- The largest array that the validator writes out as a value when it knows the size
maxUnfolded :: Integer
maxUnfolded = 1024

relProof :: Rel -> VariableProof -> VariableProof -> VariableProof
relProof rel lhs rhs = FApp (CTerm (builtinFunct (Rel rel))) [lhs, rhs]

-- An Int result that does not fit in 64 bits is an error, as in compiled code (addition, subtraction and
-- multiplication overflow, and so does minInt / -1)
checkedInt :: Integer -> Result Value String
checkedInt n
    | inIntRange n = Ok (VInt n)
    | otherwise = Error "Integer overflow"

-- Equality is structural, for any two values that are not functions
comparable :: Value -> Value -> Bool
comparable VFunct{} _ = False
comparable _ VFunct{} = False
comparable VFnRef{} _ = False
comparable _ VFnRef{} = False
comparable (VInt _) (VInt _) = True
comparable (VBool _) (VBool _) = True
comparable (VList _) (VList _) = True
comparable (VData _ _) (VData _ _) = True
comparable _ _ = False

-- The builtins that lib/stdlib.tersus declares, by the name it declares each under. The contracts of these
-- are written there, as text to be parsed (StdLibDefs); the ones not listed here are primitives, whose
-- contracts are made in this module because they are built from the ghost terms of a permission or are
-- made afresh for a type (Ctor, Field, Is, Cast, Project, ToWord), or have no contract to write.
stdlibBuiltinDecls :: [(String, BuiltinFunct)]
stdlibBuiltinDecls =
    [ ("size", Size)
    , ("first", First)
    , ("last", Last)
    , ("get", Get)
    , ("push", Push)
    , ("pop", Pop)
    , ("set", Set)
    , ("array", NewArray)
    , ("arrayBoxed", NewBoxedArray)
    , ("arrayEmpty", NewEmptyArray)
    , ("writeByte", WriteByte)
    , ("writeError", WriteError)
    , ("readByte", ReadByte)
    , ("argCount", ArgCount)
    , ("argByte", ArgByte)
    , ("pathByte", PathByte)
    , ("fileLoad", FileLoad)
    , ("fileByte", FileByte)
    , ("storeByte", StoreByte)
    , ("fileStore", FileStore)
    , ("toByte", ToByte)
    , ("toInt", FromByte)
    , ("bytesFrom", BytesFrom)
    , ("unsize", Unsize)
    , ("arrayFrom", ArrayFrom)
    , ("boxNew", NewBox)
    , ("boxUnbox", UnBox)
    , ("cloneOf", CloneOf)
    , ("plus", Plus)
    , ("minus", Minus)
    , ("times", Times)
    , ("div", Div)
    , ("mod", Mod)
    ]

-- The parameters of the builtins lib/stdlib.tersus declares, as a proof names them
stdlibDeclaredParams :: [(BuiltinFunct, [Variable])]
stdlibDeclaredParams =
    [ (Size, ["list"]), (First, ["list"]), (Last, ["list"]), (Get, ["list", "index"])
    , (Push, ["list", "x"]), (Pop, ["list"]), (Set, ["list", "index", "x"]), (NewArray, ["n", "x"])
    , (NewBoxedArray, ["n", "x"]), (NewEmptyArray, []), (WriteByte, ["b"]), (WriteError, ["b"])
    , (ReadByte, []), (ArgCount, []), (ArgByte, ["i", "j"]), (PathByte, ["b"]), (FileLoad, [])
    , (FileByte, ["i"]), (StoreByte, ["b"]), (FileStore, []), (ToByte, ["x"]), (FromByte, ["b"])
    , (BytesFrom, ["list"]), (Unsize, ["box"]), (ArrayFrom, ["list"]), (NewBox, ["value"])
    , (UnBox, ["box"]), (CloneOf, ["value"]), (Plus, ["a", "b"]), (Minus, ["a", "b"])
    , (Times, ["a", "b"]), (Div, ["a", "b"]), (Mod, ["a", "b"])
    ]
