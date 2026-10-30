module TestDeref (testDeref) where

import TersusTypes
import TestHarness

-- Deref<T>: a type that holds another is looked through to it where a struct or an enum is looked at (a field, `is`, `as`, a
-- `match`, the base of an update, `shrinks`), through the value its `deref` gives. A Box is looked through the same way by the
-- language itself, since what it holds is not a field of it.
testDeref :: Test
testDeref =
    let runs body expected = parseEvalProgramHelper body (Just expected)
        valid = parseValidProgramHelper
        rejected = parseValidateFailProgramHelper
        prelude =
            unlines
                [ "trait Deref<T> { fn deref(self: &Self) -> T [{ }] [{ }]; };"
                , "trait Clone { };"
                , "struct P { x: Int, y: Int };"
                , "impl Clone for P { };"
                , "struct W { v: P };"
                , "impl Deref<P> for W { fn deref(self: &Self) -> P [{ }] [{ affirm return = self.v; }] { return clone(self.v); }; };"
                ]
        enumPrelude =
            unlines
                [ "trait Deref<T> { fn deref(self: &Self) -> T [{ }] [{ }]; };"
                , "trait Clone { };"
                , "enum E { A { v: Int }, B };"
                , "impl Clone for E { };"
                , "struct WE { v: E };"
                , "impl Deref<E> for WE { fn deref(self: &Self) -> E [{ }] [{ affirm return = self.v; }] { return clone(self.v); }; };"
                ]
     in TestList
            "testDeref"
            [ testCase "a field is read through a Deref" (runs (prelude ++ "w = W { v: P { x: 4, y: 5 } }; return w.x + w.y;") (VInt 9))
            , testCase "the field it holds is read as it is" (runs (prelude ++ "w = W { v: P { x: 4, y: 5 } }; return w.v.x + w.v.y;") (VInt 9))
            , testCase "its own field wins over the one inside" (runs (prelude ++ "struct W3 { x: Int, v: P }; impl Deref<P> for W3 { fn deref(self: &Self) -> P [{ }] [{ affirm return = self.v; }] { return clone(self.v); }; }; w = W3 { x: 1, v: P { x: 4, y: 5 } }; return w.x * 100 + w.y;") (VInt 105))
            , testCase "a Deref through a Deref" (runs (prelude ++ "impl Clone for W { }; struct W2 { w: W }; impl Deref<W> for W2 { fn deref(self: &Self) -> W [{ }] [{ affirm return = self.w; }] { return clone(self.w); }; }; w = W2 { w: W { v: P { x: 4, y: 5 } } }; return w.x + w.y;") (VInt 9))
            , testCase "a field of the one in between is read" (runs (prelude ++ "impl Clone for W { }; struct W2 { w: W }; impl Deref<W> for W2 { fn deref(self: &Self) -> W [{ }] [{ affirm return = self.w; }] { return clone(self.w); }; }; w = W2 { w: W { v: P { x: 4, y: 5 } } }; return w.v.x + w.v.y;") (VInt 9))
            , testCase "a field of the one in between wins over the one inside" (runs (prelude ++ "struct WM { x: Int, v: P }; impl Clone for WM { }; impl Deref<P> for WM { fn deref(self: &Self) -> P [{ }] [{ affirm return = self.v; }] { return clone(self.v); }; }; struct W2 { w: WM }; impl Deref<WM> for W2 { fn deref(self: &Self) -> WM [{ }] [{ affirm return = self.w; }] { return clone(self.w); }; }; w = W2 { w: WM { x: 1, v: P { x: 4, y: 5 } } }; return w.x * 100 + w.y;") (VInt 105))
            , testCase "a field of the one in between is known" (valid (prelude ++ "impl Clone for W { }; struct W2 { w: W }; impl Deref<W> for W2 { fn deref(self: &Self) -> W [{ }] [{ affirm return = self.w; }] { return clone(self.w); }; }; w = W2 { w: W { v: P { x: 4, y: 5 } } }; affirm w.v.x = 4; return w.v.x;"))
            , testCase "an enum is tested through a Deref" (runs (enumPrelude ++ "w = WE { v: E::A { v: 3 } }; return w is E::A;") (VBool True))
            , testCase "an enum is cast through a Deref" (runs (enumPrelude ++ "w = WE { v: E::A { v: 3 } }; return (w as E::A).v;") (VInt 3))
            , testCase "an enum is matched through a Deref" (runs (enumPrelude ++ "fn f(w: WE) -> Int { return match w { E::A { v: v } => v, E::B => 0 }; }; return f(WE { v: E::A { v: 6 } });") (VInt 6))
            , testCase "the base of an update is looked through" (runs (prelude ++ "w = W { v: P { x: 1, y: 2 } }; c = P { x: 9, ..w }; return c.x + c.y;") (VInt 11))
            , testCase "a field of what a Deref holds is known" (valid (prelude ++ "w = W { v: P { x: 4, y: 5 } }; affirm w.x = 4; return w.x;"))
            , testCase "a contract about the variant it holds" (valid (enumPrelude ++ "fn v(w: WE) -> Int [{ affirm w is E::A; }] [{ affirm return = (w as E::A).v; }] { return (w as E::A).v; }; return v(WE { v: E::A { v: 4 } });"))
            , testCase "the contract is not met" (rejected (enumPrelude ++ "fn v(w: WE) -> Int [{ affirm w is E::A; }] [{ }] { return (w as E::A).v; }; return v(WE { v: E::B });") "Could not prove: <WE as Deref>::deref(w) is E::A")
            , testCase "a method is called on what it holds, not on it" (runs (prelude ++ "impl P { fn total(self: Self) -> Int { return self.x + self.y; }; }; w = W { v: P { x: 2, y: 3 } }; return w.deref().total();") (VInt 5))
            , testCase "not on the wrapper itself" (rejected (prelude ++ "impl P { fn total(self: Self) -> Int { return self.x + self.y; }; }; w = W { v: P { x: 2, y: 3 } }; return w.total();") "is not defined")
            , testCase "what it holds is not the wrapper" (rejected (prelude ++ "fn f(p: P) -> Int { return 0; }; return f(W { v: P { x: 1, y: 2 } });") "argument 1 of f: expected P, got W")
            , testCase "what shrinks is what it is looked through to" (valid (prelude ++ "fn f(w: W) -> Int shrinks w { return w.x; }; return f(W { v: P { x: 4, y: 5 } });"))
            ]
