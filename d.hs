-- CSci 119, Lab 4

import Data.List (sort, stripPrefix) -- for your solution to Lab 3
import Control.Monad (replicateM)    -- for strings function at the end


---------------- Code provided to you in Lab 3 ----------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Length-Ordered Lists over "character type" a (aka "strings")
-- Invariant: In LOL n xs, n == length xs
data LOL a = LOL Int [a] deriving (Eq,Ord)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is sorted with no duplicates
type Lang a = [LOL a]

-- Smart constructor for (finite) languages
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

---- Regular expressions, along with input and output
data RegExp = Empty                -- Empty language
            | Let Char             -- Single letter language
            | Union RegExp RegExp  -- Union
            | Cat RegExp RegExp    -- Concatenation
            | Star RegExp          -- Kleene star
            deriving (Show, Eq)

-- Compact display form for RegExp
newtype Compact = Compact RegExp

instance (Show Compact) where    -- use precedence to minimize parentheses
  showsPrec d (Compact r) = sp d r where
    sp d Empty         = showString "@"
    sp d (Let c)       = showString [c]
    sp d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                         sp 6 r1 .
                         showString "+" .
                         sp 6 r2
    sp d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                         sp 7 r1 .
                         sp 7 r2
    sp d (Star r1)     = sp 9 r1 .     -- prec(Star) = 8
                         showString "*"

-- Quick and dirty postfix RegExp parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = go w [] where
  go [] [r]              = r
  go ('+':xs) (r2:r1:rs) = go xs (Union r1 r2:rs)
  go ('.':xs) (r2:r1:rs) = go xs (Cat r1 r2:rs)
  go ('*':xs) (r:rs)     = go xs (Star r:rs)
  go ('@':xs) rs         = go xs (Empty:rs)
  go (x:xs) rs           = go xs (Let x:rs)


---------------- Your solution to Lab 3 ----------------

-- Include here any code you need from your solution to Lab 3 for testing
-- purposes. After a few days, I will release my solution for you to use.
-- Don't duplicate the code just given above.

-- The one-string and finite languages of Theorem 3.2. It should be the case
-- that, for any string w, lang_of (onestr w) == [w], and for any (finite) list
-- of (distinct, sorted) strings l, lang_of (finite l) == l.

-- Cartesian product, preserves normalization
cart :: [a] -> [b] -> [(a,b)]
cart xs ys = [(a,b) | a <- xs, b <- ys]

-- Powerset, preserves normalization. Examples:
-- power [] = [[]]
-- power [1] = [[],[1]]
-- power [1,2] = [[],[1],[1,2],[2]]
-- power [1,2,3] = [[],[1],[1,2],[1,2,3],[1,3],[2],[2,3],[3]]
-- power [2,3] = [[],[2],[2,3],[3]]
power :: [a] -> [[a]]
power []  = [[]]
power (x:xs) = let ys = power xs in
                      [] : [h : t | h <- [x], t <- ys] ++ tail ys

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot (LOL n xs) (LOL m ys) = LOL (n+m) (xs++ys)

-- Reverse of LOLs, preserves invariant--see theorem in notes
rev :: LOL a -> LOL a
rev (LOL n xs) = LOL n (reverse xs)

-- Membership for languages (infinite lists satisfying invariant included)
memb :: Ord a => LOL a -> Lang a -> Bool
memb a [] = False
memb a (x:xs) = case (compare a x) of LT -> False
                                      EQ -> True
                                      GT -> memb a xs

-- Merge of languages (aka "union")
merge :: Ord a => Lang a -> Lang a -> Lang a
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case (compare x y) of LT -> x : merge xs (y:ys)
                                            EQ -> x : merge xs ys
                                            GT -> y : merge (x:xs) ys

-- Concatenation of languages
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] _ = []
cat _ [] = []
cat (x:xs) (ys@(y:yr)) = dot x y : merge (map (dot x) (yr)) (cat xs ys)

-- Kleene star of languages
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr
kstar xs = eps : cat xs (kstar xs)

-- Left quotient of a language by an LOL (cf. Definition 2.16)--class notes
-- Hint: Use the stripPrefix function
leftq :: Ord a => LOL a -> Lang a -> Lang a
leftq a [] = []
leftq (LOL x a1) (LOL y a2:ys) = case stripPrefix a1 a2 of
                                 Nothing -> leftq (LOL x a1) ys
                                 Just a3 -> lol a3 : leftq (LOL x a1) ys

-- The language associated to a regular expression, i.e., [[r]]
lang_of :: RegExp -> Lang Char
lang_of Empty = []
lang_of (Let a) = lang [[a]]
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Star r1) = kstar (lang_of r1)

-- The one-string and finite languages of Theorem 3.2. It should be the case
-- that, for any string w, lang_of (onestr w) == [w], and for any (finite) list
-- of (distinct, sorted) strings l, lang_of (finite l) == l.
onestr :: String -> RegExp
onestr [] = Star Empty
onestr [x] = Let x
onestr (x:xs) = Cat (Let x) (onestr xs)

finite :: [String] -> RegExp
finite [] = Empty
finite [x] = onestr x
finite (x:xs) = Union (onestr x) (finite xs)

---------------- Part 1 ----------------

-- Implement the seven recursive predicates/operations on RegExp given in
-- Section 3.3 of the notes; call them empty, unitary, byp, inf, rever, lq,
-- and nep. Each should begin with a type declaration. Include several tests
-- for each function.
e = toRE "@"
l = toRE "a"
u = toRE "ab+"
c = toRE "ab."
s = toRE "a*"
empty :: RegExp -> Bool
empty Empty = True
empty (Let 'a') = False
empty (Union r1 r2) = empty r1 && empty r2
empty (Star r) = False
empty (Cat r1 r2) = empty r1 || empty r2


-- unitary covered
-- bypass covered
-- rever covered a little
--



---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes,
-- where the second algorithm is the modified one I posted on Piazza (@96).
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = undefined
--covered


match1 :: RegExp -> String -> Bool
match1 r w = undefined
--covered

match2 :: RegExp -> String -> Bool
match2 r w = undefined



-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get).

sigma = ['a', 'b']                -- Alphabet used in all examples below
-- Exercises from 3.2 below
q1 = toRE "b*ab.b.*+*"            -- every a followed by bb
-- OR -> q1   = toRE "b*ab.b.*.b*.b*ab.b.*+." -- every a followed by bb
q3 = toRE "a*b*.b*a*.+ab.ba.+.a*b*.b*a*.+." -- at least one a and one b
q4 = toRE "ab.*ba.*+a*+b*+"       -- no two adjacent letters
q5 = toRE "a*ba.bb.a.+a+*."       -- no instances of bbb
q6 = toRE "b*a*+ba.+abb.a.+ab.b.+*.b*." -- no instances of aba
-- every instance of aa coming before every instance of bb
q7 = toRE "a*b+a*.b*.aab.*+.b*."
-- even number of a's and an even number of b's.
q8 = toRE "aa.bb.+ab.a.b.+ab.b.a.+ba.b.a.+ba.a.b.+*"
-- the 4 below were given
ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's (q2 in 3.2)
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once


-- For your tests, you may also find the following helpful. For example,
-- you can generate all strings of length 10 (or 20) or less and then test
-- to see whether match1 r w == memb (lol w) (lang_of r) for each such w.

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]
