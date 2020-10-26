-- Lab 6:  FSM constructions for regular operators

import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)
type FSM a = ([a], a, [a], a -> Char -> a)


---------------- Your solution to Lab 5, ported to FSM a -------------------
-- THIS CODE IS ON BOTTOM
---------------- Some additional useful functions --------------------------

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

-- Cartesian product (preserves normalization)
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- Powerset  (preserves normalization)
power :: [a] -> [[a]]
power [] = [[]]
power (x:xs) = let ys = power xs
               in [] : map (x:) ys ++ tail ys

-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 6 begins here -----------------------------------------

-- Complete the FSM constructions for the regular expression operators
-- and test your functions adequately


-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [], d) where
  d 0 _ = 0

-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM a = ([0,1,2], 0, [1], d) where
  d q x = if a == x && q == 0 then 1 else 2

-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = (><) qs1 qs2
  s  = (s1, s2)
  fs = [(q1, q2) | (q1, q2) <- qs, elem q1 fs1 || elem q2 fs2]
  d (q1, q2) a = (d1 q1 a, d2 q2 a)

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  fix q x = norm (if elem q fs1 then (s2:x) else x)
  qs = [(q1, x) | q1 <- qs1, x <- power qs2, fix q1 x == x]
  s  = (s1, fix s1 [])
  fs = [(q, x) | (q, x) <- qs, overlap x fs2]
  d (q,x) a = let q1' = d1 q a in
              (q1', fix q1' [d2 q2 a | q2 <- x])


-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  fix x = norm (if overlap x fs1 then s1:x else x)
  qs = power qs1
  s  = []
  fs = union [] [x | x <- qs, overlap x fs1]
  d x a = if x == [] then fix [d1 s1 a] else fix [d1 x1 a | x1 <- x]

---------------- Bonus Features (for testing and experimenting) ------------

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, s, fs, d) = (qs', s, fs', d) where
  qs' = uclosure [s] (\q -> map (d q) sigma)
  fs' = filter (`elem` fs) qs'

-- Change the states of an FSM from an equality type to Int
-- and use an array lookup for the transition function
intify :: Eq a => FSM a -> FSM Int
intify (qs, s, fs, d) = ([0..n-1], s', fs', d') where
  n = length qs
  m = length sigma
  s'  = ind qs s
  fs' = map (ind qs) fs
  arr = listArray ((0,0), (n-1,m-1)) [ind qs (d q a) | q <- qs, a <- sigma]
  d' q a = arr ! (q, ind sigma a)
  ind (q':qs) q = if q == q' then 0 else 1 + ind qs q

reduce :: Ord a => FSM a -> FSM Int
reduce = intify . reachable

---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp

instance (Show RegExp) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Let c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)

-- Use constructions above to get reduced machine associated with regex
-- Warning: it can take a lot of time/memory to compute these for "big" regex's
-- We will see much better ways later in the course
re2fsm :: RegExp -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Let c) = letterFSM c
re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)

---------------RE's from 3.2--------------------

q1 = toRE "b*ab.b.*+*"                        -- every a followed by bb
-- OR -> q1   = toRE "b*ab.b.*.b*.b*ab.b.*+." -- every a followed by bb
q3 = toRE "a*b*.b*a*.+ab.ba.+.a*b*.b*a*.+."   -- at least one a and one b
q4 = toRE "ab.*ba.*+a+b+"                     -- no two adjacent letters
q5 = toRE "a*ba.bb.a.+a+*."                   -- no instances of bbb
q6 = toRE "b*a*+ba.+abb.a.+ab.b.+*.b*."       -- no instances of aba
    -- every instance of aa coming before every instance of bb
q7 = toRE "a*b+a*.b*.aab.*+.b*." -- even number of a's and an even number of b's
q8 = toRE "aa.bb.+ab.a.b.+ab.b.a.+ba.b.a.+ba.a.b.+*"

-- Regular expressions examples given in lab 4
ab = toRE "aa.bb.+*"                          -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."                  -- third to last letter is a
ena = toRE "b*a.b*.a.*b*."                    -- even number of a's (q2 in 3.2)
bb1  = toRE "aba.+*b.b.aab.+*."               -- contains bb exactly once

--------------------------------------------------
----------------- TESTING ------------------------
--------------------------------------------------
test fsm re = and [accept1 fsm w == match2 re w | w <- strings 20]

-- FSM test by RE comparison
-- generic tester when you know the RE
-- it only compares the first 100 values
re_test fsm re = and [accept1 fsm s | re <- take 100 (lang_of re),
                s <- s10, (lol s) == re] -- not a good test


-- *Main> checkFSM emptyFSM
-- True
-- *Main> re_test emptyFSM (Let 'a')
-- False
-- *Main> re_test emptyFSM Empty
-- True
-- *Main> accept1 emptyFSM "b"
-- False
-- *Main> accept1 emptyFSM ""
-- False

-- *Main> checkFSM (letterFSM 'a')
-- True
-- *Main> re_test (letterFSM 'a') (Let 'a')
-- True
-- *Main> re_test (letterFSM 'a') (Let 'b')
-- False
-- *Main> re_test (letterFSM 'b') (Let 'b')
-- True
-- *Main> accept1 (letterFSM 'b') "b"
-- True
-- *Main> accept1 (letterFSM 'a') "b"
-- False
-- *Main> accept1 (letterFSM 'c') "c"
-- True

-- *Main> checkFSM (unionFSM (letterFSM 'a') (letterFSM 'a'))
-- True
-- *Main> checkFSM (unionFSM (letterFSM 'a') (letterFSM 'b'))
-- True
-- *Main> accept1 (unionFSM (letterFSM 'a') (letterFSM 'a')) ""
-- False
-- *Main> accept1 (unionFSM (letterFSM 'a') (letterFSM 'a')) "a"
-- True
-- *Main> accept1 (unionFSM (letterFSM 'a') (letterFSM 'b')) "a"
-- True
-- *Main> accept1 (unionFSM (letterFSM 'a') (letterFSM 'b')) "ab"
-- False
-- *Main> accept1 (unionFSM (letterFSM 'a') (letterFSM 'b')) "b"
-- True
-- *Main> re_test (unionFSM (letterFSM 'a') (letterFSM 'b')) (toRE "ab+")
-- True
-- *Main> re_test (unionFSM (letterFSM 'a') (letterFSM 'a')) (toRE "ab+")
-- False
-- *Main> re_test (unionFSM (letterFSM 'b') (letterFSM 'a')) (toRE "ab+")
-- True
-- *Main> re_test (unionFSM (letterFSM 'b') (unionFSM (letterFSM 'b') (letterFSM 'c'))) (toRE "ab+c+")
-- False
-- *Main> re_test (unionFSM (letterFSM 'a') (unionFSM (letterFSM 'b') (letterFSM 'c'))) (toRE "ab+c+")
-- True

-- cat
-- *Main> s2 = 3
-- *Main> fs1 = [0,1,2]
-- *Main> fix q x = if elem q fs1 then (norm (s2:x)) else x
-- *Main> fix 8 [1,2,3]
-- [1,2,3]
-- *Main> fix 2 [1,7,2,3]
-- [1,2,3,7]
-- *Main> fix 2 [1,7,2]
-- [1,2,3,7]
-- *Main> accept1 (catFSM (letterFSM 'a') (letterFSM 'b')) "ab"
-- True
-- *Main> accept1 (catFSM (letterFSM 'a') (letterFSM 'b')) "a"
-- False
-- *Main> accept1 (catFSM (letterFSM 'a') (letterFSM 'b')) "abc"
-- False
-- *Main> re_test (catFSM (letterFSM 'a') (letterFSM 'b')) (toRE "ab.")
-- True
-- *Main> re_test (unionFSM (catFSM (letterFSM 'a') (letterFSM 'b')) (letterFSM 'c')) (toRE "ab.c+")
-- True
-- EX FROM LEC
-- *Main> (qs,s,f,d) = reachable (catFSM (letterFSM 'a') (letterFSM 'b'))
-- *Main> qs
-- [(0,[]),(1,[0]),(2,[]),(2,[1]),(2,[2])] CHECK
-- *Main> [(q,a,d q a) | q <- qs, a <- sigma]
-- [((0,[]),'a',--------------------> (1,[0])),------------------------
--  ((0,[]),'b',                         V                           V
--       V                               V                           V
--       V                               V                           V
--     (2,[])),                          V                           V
--       V                          ((1,[0]),'a',(2,[2])),           V
--       V                                V              ((1,[0]),'b',(2,[1])),
--  ((2,[]),'a',(2,[])),                  V                          V
--  ((2,[]),'b',(2,[])),                  V                          V
--                                        V              ((2,[1]),'a',(2,[2])),
--                                        V              ((2,[1]),'b',(2,[2])),
--                                  ((2,[2]),'a',(2,[2])),
--                                  ((2,[2]),'b',(2,[2]))]
-- This checks out with classes example

-- *Main> re_test (starFSM (letterFSM 'a'))  (toRE "ab.c+")
-- False
-- *Main> re_test (starFSM (letterFSM 'a'))  (toRE "a")
-- True
-- *Main> re_test (starFSM (letterFSM 'a'))  (toRE "aa.")
-- True
-- *Main> re_test (starFSM (letterFSM 'a'))  (toRE "aa.a.")
-- True
-- *Main> re_test (starFSM (letterFSM 'a'))  (toRE "aa.a.b.")
-- False
-- *Main> accept1 (starFSM (letterFSM 'a')) "abc"
-- False
-- *Main> accept1 (starFSM (letterFSM 'a')) "a"
-- True
-- *Main> accept1 (starFSM (letterFSM 'a')) ""
-- False
-- *Main> checkFSM (starFSM (letterFSM 'a'))
-- True






-----------------IMPORTED CODE FROM PREVIOUS LABS---------------------------
----------------------------------------------------------------------------
---------------- Your solution to Lab 5, ported to FSM a -------------------

-- Check whether a finite state machine (qs, s, fs, d) is correct/complete:

-- (1) States qs are unique (no duplicates)
no_dups :: Eq a => [a] -> Bool
no_dups [] = True
no_dups (q:qs) = notElem q qs && no_dups qs

-- (2) Start state is a state (s is in qs) is a state of the machine
-- use elem

-- (3) Final states are states (fs is a subset of qs)
is_subset :: Eq a => [a] -> [a] -> Bool
is_subset [] qs = True
is_subset [f] [] = False
is_subset (f:fs) qs = elem f qs && is_subset fs qs

-- (4) Transition function d gives a state in qs for every state in qs and
--     letter from sigma
check_d :: Eq a => (a -> Char -> a) -> [a] -> Bool
check_d d qs = and [ elem (d q s) qs | q <- qs, s <- sigma]

--break up m into (qs, s, fs, d)
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = no_dups qs && elem s qs
                          && is_subset fs qs && check_d d qs

-- Gives the delta* function (recursive in w) (q is start state)
dstar :: FSM a -> a -> [Char] -> a
dstar _ q "" = q
dstar m@(_, _, _, d) q (w:ws) = dstar m (d q w) ws

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (dstar m s w) fs

-- Machine acceptance, Definition 2 (via L_q(M))
accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 f@(qs, s, fs, d) w = aux s w where
  -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  -- aux :: Eq a => a -> [Char] -> Bool -- <<<<< ask wilson
  aux q [] = elem q fs
  aux q (w:ws) = aux (d q w) ws

exactly :: String -> FSM Int -- vvv<<<<< ask wilson
exactly w = ([0 .. ((length w)+1)], 0, [length w], d) where
  d q l
    | q < (length w) && w !! q == l = q+1
    | otherwise = ((length w)+1)

-- Note: didn't finish these three in time.
s10 = strings 10
avoid_aab_test = and [isInfixOf "aab" s == not (accept1 avoid_aab s) | s <- s10]
end_ab_test =  and [ isSuffixOf "ab" s == accept1 end_ab s | s <- s10]
-- exactly_test x = [w | w <- s10, accept1 (exactly x) w] == [x]
--Note: exactly test only works for input strings within s10

------------ Part 2: FSM construction
-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM Int
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM Int
avoid_aab = ([0,1,2,3], 0, [0,1,2], d) where
  d 0 'a' = 1
  d 0 'b' = 0
  d 1 'b' = 0
  d 1 'a' = 2
  d 2 'a' = 2
  d 2 'b' = 3
  d 3 _ = 3

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM Int
end_ab = ([0,1,2], 0, [2], d) where
  d _ 'a' = 1
  d 0 'b' = 0
  d 1 'b' = 2
  d 2 'b' = 0

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot (LOL n xs) (LOL m ys) = LOL (n+m) (xs++ys)

-- Concatenation of languages from lab 4
cat :: Ord a => Lang a -> Lang a -> Lang a
cat [] _ = []
cat _ [] = []
cat (x:xs) (ys@(y:yr)) = dot x y : merge (map (dot x) (yr)) (cat xs ys)

-- Kleene star of languages from lab 4
kstar :: Ord a => Lang a -> Lang a
kstar [] = [eps]
kstar (LOL 0 []:xr) = kstar xr
kstar xs = eps : cat xs (kstar xs)

-- The language associated to a regular expression, i.e., [[r]] from lab 4
lang_of :: RegExp -> Lang Char
lang_of Empty = []
lang_of (Let a) = lang [[a]]
lang_of (Union r1 r2) = merge (lang_of r1) (lang_of r2)
lang_of (Cat r1 r2) = cat (lang_of r1) (lang_of r2)
lang_of (Star r1) = kstar (lang_of r1)

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

-- Splits function from lab 4
splits :: [a] -> [([a], [a])]
splits xs = [(t,d) | l <- [0 .. length xs], let t = take l xs, let d = drop l xs]

-- Match function from lab 4
match1 :: RegExp -> String -> Bool
match1 Empty _ = False
match1 (Let a) w = [a] == w
match1 (Union r1 r2) w = match1 r1 w || match1 r2 w
match1 (Cat r1 r2) w = or [match1 r1 w1 && match1 r2 w2 | (w1 , w2) <- splits w]
match1 (Star r) w = let (x:ws) = splits w in
                    w == [] ||
                    or [match1 r w1 && match1 (Star r) w2 | (w1 , w2) <- ws]

-- Merge of languages (aka "union") from lab 4
merge :: Ord a => Lang a -> Lang a -> Lang a
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys) = case (compare x y) of LT -> x : merge xs (y:ys)
                                            EQ -> x : merge xs ys
                                            GT -> y : merge (x:xs) ys

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

nep :: RegExp -> RegExp
nep Empty = Empty
nep (Let a) = Let a
nep (Union r1 r2) = Union (nep r1) (nep r2)
nep (Cat r1 r2) = let c = (Cat (nep r1) r2) in
                  if (byp r1) then (Union c (nep r2)) else c
nep (Star r) = Cat (nep r) (Star r)

byp :: RegExp -> Bool
byp Empty = False
byp (Let a) = False
byp (Union r1 r2) = byp r1 || byp r2
byp (Cat r1 r2) = byp r1 && byp r2
byp (Star r) = True
