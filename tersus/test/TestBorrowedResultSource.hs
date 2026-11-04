module TestBorrowedResultSource (sourceCases, checkSource) where

import Data.List (isInfixOf)
import qualified Parse
import TypeCheck (elaborate)
import Utils

checkSource :: String -> Maybe String -> Maybe String
checkSource source expected = case parsed of
    Ok () | expected == Nothing -> Nothing
    Error err | maybe False (`isInfixOf` err) expected -> Nothing
    other -> Just ("Unexpected source result: " ++ show other)
  where
    parsed = case Parse.parseStatementBlock source of
        Left err -> Error (show err)
        Right body -> mapResult (const ()) (elaborate body)

sourceCases :: [(String, String, Maybe String)]
sourceCases =
    [ ("scalar field source view", field ++ "g = G { n: 7 }; return field(g);", Nothing)
    , ("local reference alias", g ++ "fn field(g: &G) -> Int borrowed from g { r = &g.n; return *r; };", Nothing)
    , ("fresh local escape", g ++ "fn field(g: &G) -> Int borrowed from g { n = 9; return n; };", Just "every borrowed return place")
    , ("wrong parameter origin", g ++ "fn field(a: &G, b: &G) -> Int borrowed from a { return b.n; };", Just "every borrowed return place")
    , ("owning returned expression", g ++ "fn field(g: &G) -> Int borrowed from g { return 9; };", Just "must return a place")
    , ("owned parameter origin", g ++ "fn field(g: G) -> Int borrowed from g { return g.n; };", Just "not a read-borrowed parameter")
    , ("mutable parameter not read-borrowed", g ++ "fn field(g: &mut G) -> Int borrowed from g { return g.n; };", Just "not a read-borrowed parameter")
    , ("known named alias", field ++ "f = field; g = G { n: 7 }; return f(g);", Nothing)
    , ("callback parameter erasure", field ++ "fn use(f: fn(&G) -> Int, g: &G) -> Int { return f(g); }; g = G { n: 7 }; return use(field, g);", Just "cannot be erased")
    , ("constructor field erasure", field ++ "struct H { f: fn(&G) -> Int }; h = H { f: field };", Just "cannot be erased")
    , ("function return erasure", field ++ "fn fetch() -> fn(&G) -> Int { return field; };", Just "cannot be erased")
    , ("owned carrier unchanged", "struct Held { r: &Int }; fn carry(x: &Int) -> Held from x { return Held { r: &x }; };", Nothing)
    , ("reference source T view", "struct Held { r: &Int }; fn slot(h: &Held) -> &Int borrowed from h { return h.r; };", Nothing)
    , ("mode-preserving trait implementation", "trait Field { fn field(self: &Self) -> Int borrowed from self; }; struct G { n: Int }; impl Field for G { fn field(self: &Self) -> Int borrowed from self { return self.n; }; };", Nothing)
    , ("trait cannot accept owning implementation", "trait Field { fn field(self: &Self) -> Int borrowed from self; }; struct G { n: Int }; impl Field for G { fn field(self: &Self) -> Int { return self.n; }; };", Just "preserve the trait's borrowed result mode")
    , ("declared size-generic array view", "fn item<T, n>(a: &Array<T, n>) -> T borrowed from a [{ affirm n > 0; }] [{ }] { return get(a, 0); };", Nothing)
    ]
  where
    g = "struct G { n: Int }; "
    field = g ++ "fn field(g: &G) -> Int borrowed from g [{ }] [{ affirm return = g.n; }] { return g.n; }; "
