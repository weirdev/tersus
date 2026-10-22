module Linear
    ( Linear
    , Constraint (..)
    , infeasible
    , infeasibleWith
    ) where

import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.List (foldl', minimumBy)
import Data.Ord (comparing)
import qualified Data.Set as Set
import Data.Ratio (denominator, numerator)

-- Linear arithmetic over integer variables, for relations the difference constraints of ProofEngine cannot express,
-- such as s + i = n or 2 * x <= y.
--
-- A constraint is a sum of coefficients times variables, compared with a constant. The system is refused (infeasible)
-- when it has no rational solution, or when rounding the constants of the inequalities to integers (a sum of integers
-- with coefficients 2 and 4 is even, so 2x + 4y <= 3 is 2x + 4y <= 2) leaves none. Rational infeasibility implies
-- integer infeasibility, so this is sound, and it is incomplete the way integer programming is hard.

type Linear = IntMap.IntMap Rational

-- sum of (coefficient * variable) = constant, or <= constant
data Constraint
    = Equal Linear Rational
    | AtMost Linear Rational
    deriving (Show, Eq)

-- The constraints that may be kept while eliminating variables. A system that grows past this is given up on, which
-- says it is feasible (nothing is proved).
maxConstraints :: Int
maxConstraints = 300

-- Whether the constraints have no solution; False when that is not established within the size limit
infeasible :: [Constraint] -> Bool
infeasible constraints =
    case solveEqualities [(l, c) | Equal l c <- constraints] of
        Nothing -> True
        Just substitution ->
            let inequalities = [substitute substitution l c | AtMost l c <- constraints]
             in eliminate (dedupe (concatMap tighten inequalities))

-- Whether the background and the extra constraints have no solution together. Only the background constraints that
-- are connected to the extra ones through the variables they share can matter (the others are satisfiable on their own,
-- if the background is), so only those are looked at.
infeasibleWith :: [Constraint] -> [Constraint] -> Bool
infeasibleWith background extra = infeasible (extra ++ related)
  where
    variables (Equal l _) = IntMap.keys l
    variables (AtMost l _) = IntMap.keys l
    indexed = zip [0 :: Int ..] background
    byVariable = IntMap.fromListWith (++) [(x, [i]) | (i, c) <- indexed, x <- variables c]
    constraintOf = IntMap.fromList indexed
    start = concatMap variables extra
    related = [constraintOf IntMap.! i | i <- IntSet.toList (reach IntSet.empty IntSet.empty start)]
    -- the constraints reached from the variables, following the variables of each constraint reached
    reach _ seenIndexes [] = seenIndexes
    reach seenVars seenIndexes (x : rest)
        | IntSet.member x seenVars = reach seenVars seenIndexes rest
        | otherwise =
            let new = [i | i <- IntMap.findWithDefault [] x byVariable, not (IntSet.member i seenIndexes)]
                more = concat [variables (constraintOf IntMap.! i) | i <- new]
             in reach (IntSet.insert x seenVars) (foldl' (flip IntSet.insert) seenIndexes new) (more ++ rest)

-- Substituting the solved variables
type Substitution = IntMap.IntMap (Linear, Rational)

-- x = (the linear form) + constant, for each solved variable, in terms of the variables that are not solved. Nothing
-- when an equation has no solution.
solveEqualities :: [(Linear, Rational)] -> Maybe Substitution
solveEqualities = foldl' step (Just IntMap.empty)
  where
    step Nothing _ = Nothing
    step (Just solved) (l, c) =
        let (l', c') = substitute solved l c
         in case IntMap.minViewWithKey l' of
                Nothing -> if c' == 0 then Just solved else Nothing
                Just _
                    | integerless l' c' -> Nothing
                    | otherwise ->
                        -- solve for one variable: x = (c' - rest) / a
                        let (x, a) = pivot l'
                            rest = IntMap.delete x l'
                            definition = (IntMap.map (\r -> negate r / a) rest, c' / a)
                            replaced = IntMap.map (\(dl, dc) -> expand x definition dl dc) solved
                            solved' = IntMap.insert x definition replaced
                         in if any wholeless (IntMap.elems solved') then Nothing else Just solved'
    -- a variable with coefficient 1 or -1 when there is one, since then it is a whole number whenever the others are
    pivot l = case [(x, a) | (x, a) <- IntMap.toList l, abs a == 1] of
        unit : _ -> unit
        [] -> foldl' (\(bx, ba) (x, a) -> if abs a > abs ba then (x, a) else (bx, ba)) (IntMap.findMin l) (IntMap.toList l)
    expand x (xl, xc) dl dc =
        case IntMap.lookup x dl of
            Nothing -> (dl, dc)
            Just k -> (IntMap.filter (/= 0) (IntMap.unionWith (+) (IntMap.delete x dl) (IntMap.map (* k) xl)), dc + k * xc)

-- A variable that is defined by x = (a_1 y_1 + ... + c) / d, with every y a whole number, is a whole number only if
-- the gcd of the a_i and d divides c: x = y + 1/2 has none
wholeless :: (Linear, Rational) -> Bool
wholeless (l, c) =
    let d = foldl' lcm 1 (denominator c : map denominator (IntMap.elems l))
        g = foldl' gcd d (map (\a -> numerator (a * fromInteger d)) (IntMap.elems l))
     in numerator (c * fromInteger d) `mod` g /= 0

-- An equation with integer coefficients whose gcd does not divide the constant has no integer solution
integerless :: Linear -> Rational -> Bool
integerless l c =
    let (ints, k) = scaleToIntegers l c
        g = foldl' gcd 0 (IntMap.elems ints)
     in g /= 0 && k `mod` g /= 0

substitute :: Substitution -> Linear -> Rational -> (Linear, Rational)
substitute solved l c = foldl' go (l, c) (IntMap.toList l)
  where
    go (current, constant) (x, _) =
        case (IntMap.lookup x current, IntMap.lookup x solved) of
            (Just k, Just (dl, dc)) ->
                (IntMap.filter (/= 0) (IntMap.unionWith (+) (IntMap.delete x current) (IntMap.map (* k) dl)), constant - k * dc)
            _ -> (current, constant)

-- Inequalities with integer coefficients and a rounded constant: l <= c becomes (l / g) <= floor (c / g)
tighten :: (Linear, Rational) -> [(IntMap.IntMap Integer, Integer)]
tighten (l, c) =
    let (ints, k) = scaleToIntegersFloor l c
        g = foldl' gcd 0 (IntMap.elems ints)
     in if IntMap.null ints
            then [(ints, k) | k < 0]
            else [(IntMap.map (`div` g) ints, k `div` g)]

-- The coefficients multiplied up to integers, and the constant (equation: exact, when it is not an integer there is no
-- integer solution, so it is multiplied by the same factor)
scaleToIntegers :: Linear -> Rational -> (IntMap.IntMap Integer, Integer)
scaleToIntegers l c =
    let factor = foldl' lcm 1 (map denominator (IntMap.elems l) ++ [denominator c])
     in (IntMap.map (\r -> numerator (r * fromInteger factor)) l, numerator (c * fromInteger factor))

-- As above, with the constant rounded down: a_1 x_1 + ... <= c is a_1 x_1 + ... <= floor c when the a are integers
scaleToIntegersFloor :: Linear -> Rational -> (IntMap.IntMap Integer, Integer)
scaleToIntegersFloor l c =
    let factor = foldl' lcm 1 (map denominator (IntMap.elems l))
     in (IntMap.map (\r -> numerator (r * fromInteger factor)) l, floor (c * fromInteger factor))

type Row = (IntMap.IntMap Integer, Integer)

dedupe :: [Row] -> [Row]
dedupe = Set.toList . Set.fromList

-- Fourier-Motzkin elimination: whether the inequalities contradict each other
eliminate :: [Row] -> Bool
eliminate rows
    | any (\(l, c) -> IntMap.null l && c < 0) rows = True
    | length rows > maxConstraints = False
    | otherwise =
        let live = filter (not . IntMap.null . fst) rows
            -- a variable that only ever has one sign can be made as small (or large) as needed: drop its constraints
            signs = IntMap.fromListWith (\(p, n) (p', n') -> (p + p', n + n')) [(x, if a > 0 then (1 :: Int, 0 :: Int) else (0, 1)) | (l, _) <- live, (x, a) <- IntMap.toList l]
            pure' = IntSet.fromList [x | (x, (p, n)) <- IntMap.toList signs, p == 0 || n == 0]
         in if not (IntSet.null pure')
                then eliminate (filter (\(l, _) -> not (any (`IntSet.member` pure') (IntMap.keys l))) live)
                else
                    if IntMap.null signs
                        then False
                        else
                            let (x, _) = minimumBy (comparing (\(_, (p, n)) -> p * n)) (IntMap.toList signs)
                                positive = [r | r@(l, _) <- live, IntMap.findWithDefault 0 x l > 0]
                                negative = [r | r@(l, _) <- live, IntMap.findWithDefault 0 x l < 0]
                                others = [r | r@(l, _) <- live, IntMap.notMember x l]
                                combined = concat [combine x p n | p <- positive, n <- negative]
                             in eliminate (dedupe (others ++ combined))

-- p has a positive coefficient a for x, n a negative one -b: b * p + a * n has none
combine :: Int -> Row -> Row -> [Row]
combine x (pl, pc) (nl, nc) =
    let a = pl IntMap.! x
        b = negate (nl IntMap.! x)
        l = IntMap.filter (/= 0) (IntMap.unionWith (+) (IntMap.map (* b) (IntMap.delete x pl)) (IntMap.map (* a) (IntMap.delete x nl)))
        c = b * pc + a * nc
        g = foldl' gcd 0 (IntMap.elems l)
     in if IntMap.null l then [(l, c) | c < 0] else [(IntMap.map (`div` g) l, c `div` g)]
