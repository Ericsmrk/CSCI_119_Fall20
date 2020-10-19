-- CSci 119, Lab 4
-- Eric Smrkovsky
-- 10/4/2020

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
empty (Let a) = False
empty (Union r1 r2) = empty r1 && empty r2
empty (Cat r1 r2) = empty r1 || empty r2
empty (Star r) = False

unitary :: RegExp -> Bool
unitary Empty = False
unitary (Let a) = False
unitary (Union r1 r2) = (unitary r1 && empty r2) || (empty r1 && unitary r2)
                        || (unitary r1 && unitary r2)
unitary (Cat r1 r2) = unitary r1 && unitary r2
unitary (Star r) = empty r || unitary r

byp :: RegExp -> Bool
byp Empty = False
byp (Let a) = False
byp (Union r1 r2) = byp r1 || byp r2
byp (Cat r1 r2) = byp r1 && byp r2
byp (Star r) = True

inf :: RegExp -> Bool
inf Empty = False
inf (Let a) = False
inf (Union r1 r2) = inf r1 || inf r2
inf (Cat r1 r2) = (inf r1 && not (empty r2)) || (inf r2 && not (empty r1))
inf (Star r) = not (empty r && unitary r)

rever :: RegExp -> RegExp
rever Empty = Empty
rever (Let a) = Let a
rever (Union r1 r2) = Union (rever r1) (rever r2)
rever (Cat r1 r2) = Cat (rever r2) (rever r1)
rever (Star r) = Star (rever r)

lq :: Char -> RegExp -> RegExp
lq s Empty = Empty
lq s (Let a) = if (s == a) then Star Empty else Empty
lq s (Union r1 r2) = Union (lq s r1) (lq s r2)
lq s (Cat r1 r2) = let c = (Cat (lq s r1) r2) in
                   if byp r1 then Union c (lq s r2) else c
lq s (Star r) = (Cat (lq s r) (Star r))

nep :: RegExp -> RegExp
nep Empty = Empty
nep (Let a) = Let a
nep (Union r1 r2) = Union (nep r1) (nep r2)
nep (Cat r1 r2) = let c = (Cat (nep r1) r2) in
                  if (byp r1) then (Union c (nep r2)) else c
nep (Star r) = Cat (nep r) (Star r)

---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes,
-- where the second algorithm is the modified one I posted on Piazza (@96).
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
-- EX: *Main> [(take 0 x, drop 0 x),(take 1 x, drop 1 x),(take 2 x, drop 2 x)
-- EX: ,(take 3 x, drop 3 x)]

splits :: [a] -> [([a], [a])]
splits xs = [(t,d) | l <- [0 .. length xs], let t = take l xs, let d = drop l xs]

match1 :: RegExp -> String -> Bool
match1 Empty _ = False
match1 (Let a) w = [a] == w
match1 (Union r1 r2) w = match1 r1 w || match1 r2 w
match1 (Cat r1 r2) w = or [match1 r1 w1 && match1 r2 w2 | (w1 , w2) <- splits w]
match1 (Star r) w = let (x:ws) = splits w in
                    w == [] ||
                    or [match1 r w1 && match1 (Star r) w2 | (w1 , w2) <- ws]

match2 :: RegExp -> String -> Bool
match2 r w = m [r] w where
  m :: [RegExp] -> String -> Bool
  m [] w = w == []
  m (Empty:rs) w = False
  m (Let a:rs) "" = False -- to prevent an error from occurring in let case...
  m (Let a:rs) (w:ws) = w == a && m rs ws -- ...ws becomes "" sometimes
  m (Union r1 r2:rs) w = m (r1:rs) w || m (r2:rs) w
  m (Cat r1 r2:rs) w = m (r1:r2:rs) w
  m (Star r:rs) w = m rs w || m (nep r:Star r:rs) w


-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get).

sigma = ['a', 'b']                -- Alphabet used in all examples below
-- Regular expressions exercises from 3.2 below
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
-- Regular expressions examples given in lab 4
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

---- testing ----
-- *Main> e
-- Empty
-- *Main> l
-- Let 'a'
-- *Main> u
-- Union (Let 'a') (Let 'b')
-- *Main> c
-- Cat (Let 'a') (Let 'b')
-- *Main> s
-- Star (Let 'a')

-- *Main> empty e
-- True
-- *Main> empty l
-- False
-- *Main> empty u
-- False
-- *Main> empty c
-- False
-- *Main> empty s
-- False

-- *Main> unitary u
-- False
-- *Main> unitary e
-- False
-- *Main> unitary l
-- False
-- *Main> unitary c
-- False
-- *Main> unitary s
-- False
-- *Main> unitary (toRE "@*")
-- True
-- *Main> unitary (toRE "@*a.")
-- False
-- *Main> unitary (toRE "@a+")
-- False
-- *Main> unitary (toRE "@@+")
-- False
-- *Main> unitary (toRE "@*@*+")
-- True

-- *Main> byp e
-- False
-- *Main> byp l
-- False
-- *Main> byp u
-- False
-- *Main> byp c
-- False
-- *Main> byp s
-- True
-- *Main> byp (toRE "ab+")
-- False
-- *Main> byp (toRE "a@+")
-- False
-- *Main> byp (toRE "as*+")
-- True
-- *Main> byp (toRE "as*.")
-- False
-- *Main> byp (toRE "a*s*.")
-- True

-- *Main> inf e
-- False
-- *Main> inf l
-- False
-- *Main> inf u
-- False
-- *Main> inf c
-- False
-- *Main> inf s
-- True
-- *Main> inf (toRE "a*")
-- True
-- *Main> inf (toRE "a*b*+")
-- True
-- *Main> inf (toRE "ab+")
-- False
-- *Main> inf (toRE "a*b+")
-- True
-- *Main> inf (toRE "a*@+")
-- True
-- *Main> inf (toRE "a@+")
-- False

-- *Main> rever e
-- Empty
-- *Main> rever l
-- Let 'a'
-- *Main> rever u
-- Union (Let 'a') (Let 'b')
-- *Main> rever c
-- Cat (Let 'b') (Let 'a')
-- *Main> rever s
-- Star (Let 'a')
-- *Main> q1
-- Star (Union (Star (Let 'b')) (Star (Cat (Cat (Let 'a') (Let 'b')) (Let 'b'))))
-- *Main> rever q1
-- Star (Union (Star (Let 'b')) (Star (Cat (Let 'b') (Cat (Let 'b') (Let 'a')))))
-- *Main> q3
-- Cat (Cat (Union (Cat (Star (Let 'a')) (Star (Let 'b'))) (Cat (Star (Let 'b'))
-- (Star (Let 'a')))) (Union (Cat (Let 'a') (Let 'b')) (Cat (Let 'b') (Let 'a'))))
-- (Union (Cat (Star (Let 'a')) (Star (Let 'b'))) (Cat (Star (Let 'b'))
-- (Star (Let 'a'))))
-- *Main> rever q3
-- Cat (Union (Cat (Star (Let 'b')) (Star (Let 'a'))) (Cat (Star (Let 'a'))
-- (Star (Let 'b')))) (Cat (Union (Cat (Let 'b') (Let 'a'))
-- (Cat (Let 'a') (Let 'b'))) (Union (Cat (Star (Let 'b')) (Star (Let 'a')))
-- (Cat (Star (Let 'a')) (Star (Let 'b')))))
-- *Main> Compact q3
-- (a*b*+b*a*)(ab+ba)(a*b*+b*a*)
-- *Main> rever q3
-- Cat (Union (Cat (Star (Let 'b')) (Star (Let 'a'))) (Cat (Star (Let 'a'))
-- (Star (Let 'b')))) (Cat (Union (Cat (Let 'b') (Let 'a'))
-- (Cat (Let 'a') (Let 'b'))) (Union (Cat (Star (Let 'b')) (Star (Let 'a')))
-- (Cat (Star (Let 'a')) (Star (Let 'b')))))
-- *Main> Compact it
-- (b*a*+a*b*)(ba+ab)(b*a*+a*b*)

-- *Main> leftq (lol "a") [(lol "a")]
-- [""]
-- *Main> leftq (lol "a") [(lol "d")]
-- []
-- *Main> lq 'a' (toRE "a")
-- Star Empty
-- *Main> lq 'a' (toRE "b")
-- Empty
-- *Main> un = toRE "ab+"
-- *Main> un
-- Union (Let 'a') (Let 'b')
-- *Main> lq 'a' un
-- Union (Star Empty) Empty
-- *Main> lq 'b' un
-- Union Empty (Star Empty)
-- *Main> lq 'c' un
-- Union Empty Empty
-- *Main> c = toRE "ab.c.d.e."
-- *Main> Compact c
-- abcde
-- *Main> lq 'a' c
-- Cat (Cat (Cat (Cat (Star Empty) (Let 'b')) (Let 'c')) (Let 'd')) (Let 'e')
-- *Main> Compact it
-- @*bcde

-- *Main> nep e
-- Empty
-- *Main> nep l
-- Let 'a'
-- *Main> nep u
-- Union (Let 'a') (Let 'b')
-- *Main> nep c
-- Cat (Let 'a') (Let 'b')
-- *Main> nep s
-- Cat (Let 'a') (Star (Let 'a'))
-- *Main> toRE "@a+b+"
-- Union (Union Empty (Let 'a')) (Let 'b')
-- *Main> nep it
-- Union (Union Empty (Let 'a')) (Let 'b')
-- *Main> toRE "@*a+b+"
-- Union (Union (Star Empty) (Let 'a')) (Let 'b')
-- *Main> nep it
-- Union (Union (Cat Empty (Star Empty)) (Let 'a')) (Let 'b')
-- *Main> Compact it
-- @@*+a+b

-- *Main> splits ""
-- [("","")]
-- *Main> splits "a"
-- [("","a"),("a","")]
-- *Main> splits "ab"
-- [("","ab"),("a","b"),("ab","")]
-- *Main> splits "abc"
-- [("","abc"),("a","bc"),("ab","c"),("abc","")]
-- *Main> splits (take 5 (lang_of q7))
-- [([],["","a","b","aa","ab"]),([""],["a","b","aa","ab"]),
-- (["","a"],["b","aa","ab"]),(["","a","b"],["aa","ab"]),(["","a","b","aa"],["ab"])
-- ,(["","a","b","aa","ab"],[])]

-- *Main> (match1 Empty "") == (memb (lol "") (lang []))
-- True
-- *Main> match1 (Let 'a') "a"
-- True
-- *Main> (match1 (Let 'a') "a") == (memb (lol "a") (lang ["a"]))
-- True
-- *Main> (match1 (Let 'a') "a") == (memb (lol "a") (lang ["ab"]))
-- False
-- *Main> match1 (Let 'a') "ba"
-- False
-- *Main> match1 (Let 'a') ""
-- False
-- *Main> match1 (toRE "a") "a"
-- True
-- *Main> match1 (toRE "ab+a+b+") "a"
-- True
-- *Main> match1 (toRE "ab+a+b+") "c"
-- False
-- *Main> match1 (toRE "ab+a+b+") "b"
-- True
-- *Main> match1 (toRE "ab+a+b+") ""
-- False
-- *Main> match1 (toRE "ab.c.") "ab"
-- False
-- *Main> match1 (toRE "a*") "a"
-- True
-- *Main> match1 (toRE "a*") "aa"
-- True
-- *Main> match1 (toRE "a*") "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
-- True
-- *Main> match1 (toRE "a*b*.") ""
-- True
-- *Main> match1 (toRE "") ""
-- *** Exception: lab4.hs:(69,3)-(74,43): Non-exhaustive patterns in function go
-- *Main> match1 (toRE "a*b*.") "ababababababababa"
-- False
-- *Main> match1 (toRE "a*b*.") "ab"
-- True
-- *Main> match1 (toRE "a*b*.") "abb"
-- True
-- *Main> match1 (toRE "aa.bb.+ab.a.b.+ab.b.a.+ba.b.a.+ba.a.b.+*") "bbababaa"
-- True
-- *Main> match1 (q1) "bbababaa"
-- False
-- *Main> match1 (q8) "bbababaa"
-- True

-- *Main> match2 q8 "ababaaa"
-- False
-- *Main> match2 q8 "ababaaaa"
-- True
-- *Main> match2 q5 "ababaaa"
-- True
-- *Main> match2 q5 "a"
-- True
-- *Main> w = "ababaaa"
-- *Main> match1 r w == memb (lol w) (lang_of r)
-- True
-- *Main> r =  q8
