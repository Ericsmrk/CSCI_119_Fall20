-- CSci 119, Lab 5
-- Eric Smrkovsky
-- Fall 2020
-- Reference: Lecture notes, Sections 4.1, 4.2
-- copy code from previous labs if necessary

import Data.List (sort, isInfixOf, isSuffixOf)  -- useful for testing in Part 2
-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], Int -> Char -> Int)
---------------- Part 1: Representing FSMs

-- Check whether a finite state machine (qs, s, fs, d) is correct/complete:

-- (1) States qs are unique (no duplicates)
no_dups :: [Int] -> Bool
no_dups [] = True
no_dups (q:qs) = notElem q qs && no_dups qs

-- (2) Start state is a state (s is in qs) is a state of the machine
-- use elem

-- (3) Final states are states (fs is a subset of qs)
is_subset :: [Int] -> [Int] -> Bool
is_subset [] qs = True
is_subset [f] [] = False
is_subset (f:fs) qs = elem f qs && is_subset fs qs

-- (4) Transition function d gives a state in qs for every state in qs and
--     letter from sigma
check_d :: (Int -> Char -> Int) -> [Int] -> Bool
check_d d qs = and [ elem (d q s) qs | q <- qs, s <- sigma]

--break up m into (qs, s, fs, d)
checkFSM :: FSM -> Bool
checkFSM (qs, s, fs, d) = no_dups qs && elem s qs
                          && is_subset fs qs && check_d d qs


-- Gives the delta* function (recursive in w) (q is start state)
dstar :: FSM -> Int -> [Char] -> Int
dstar _ q "" = q
dstar m@(_, _, _, d) q (w:ws) = dstar m (d q w) ws

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (dstar m s w) fs

-- Machine acceptance, Definition 2 (via L_q(M))
accept2 :: FSM -> [Char] -> Bool
accept2 (qs, s, fs, d) w = aux s w where
  -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux :: Int -> [Char] -> Bool
  aux q [] = elem q fs
  aux q (w:ws) = aux (d q w) ws

------------ Part 2: FSM construction
-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM
avoid_aab = ([0,1,2,3], 0, [0,1,2], d) where
  d 0 'a' = 1
  d 0 'b' = 0
  d 1 'b' = 0
  d 1 'a' = 2
  d 2 'a' = 2
  d 2 'b' = 3
  d 3 _ = 3

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = ([0,1,2], 0, [2], d) where
  d _ 'a' = 1
  d 0 'b' = 0
  d 1 'b' = 2
  d 2 'b' = 0

-- Every letter is duplicated RE = "aa.bb.+*" (ab)
dups :: FSM
dups = ([0,1,2,3], 0, [0], d) where
    d 0 'a' = 1 ; d 1 'a' = 0
    d 0 'b' = 2 ; d 2 'b' = 0
    d _ _ = 3

-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else (compare to 'onestr' from Lab 3)
-- Hint: the expression w !! i gives the i-th character of the string w

exactly :: String -> FSM --works with every string
exactly w = ([0 .. ((length w)+1)], 0, [length w], d) where
  d q l
    | q < (length w) && w !! q == l = q+1
    | otherwise = ((length w)+1)

-- Test the machines above. Also, try out the exercises at the end of Section 3.2
-- in my notes as FSMs.
-- Do they produce the same results as your RegExp's did? YES!

-- q1 -> every a followed by bb
eabb :: FSM
eabb = ([0,1,2,3], 0, [0], d) where
    d 0 'a' = 1 ; d 0 'b' = 0
    d 1 'b' = 2 ; d 2 'b' = 0
    d 1 'a' = 3 ; d 2 'a' = 3
    d 3 _ = 3

-- q2 -> even number of a's (test with ena)
ea :: FSM
ea = ([0,1], 0, [0], d) where
    d 0 letr = if letr == 'a' then 1 else 0
    d 1 letr = if letr == 'b' then 1 else 0
    -- or
    -- d 0 'a' = 1 ; d 0 'b' = 0
    -- d 1 'b' = 1 ; d 1 'a' = 0

-- q3 -> at least one a and at least one b
ala_alb :: FSM
ala_alb = ([0,1,2,3,4], 0, [3,4], d) where
    -- d _ _ = 1
    -- or
    d 0 'a' = 1 ; d 0 'b' = 2
    d 1 'a' = 1 ; d 1 'b' = 3
    d 2 'a' = 4 ; d 2 'b' = 2
    d 3 'a' = 4 ; d 3 'b' = 3
    d 4 'a' = 4 ; d 4 'b' = 3

-- q4 -> no 2 adjacent letters
no2adj :: FSM
no2adj = ([0,1,2,3,4,5], 0, [0,1,2,3,4], d) where
     d 0 'a' = 1 ; d 0 'b' = 2
     d 1 'b' = 3 ; d 1 'a' = 5
     d 2 'a' = 4 ; d 2 'b' = 5
     d 3 'a' = 1 ; d 4 'b' = 2
     d 3 'b' = 5 ; d 4 'a' = 5
     d 5 'a' = 5 ; d 5 'b' = 5

-- q5 -> no instance of bbb
nobbb :: FSM
nobbb = ([0,1,2,3], 0, [0,1,2], d) where
    d q 'a' = if q < 3 then 0 else 3
    d q 'b' = if q < 3 then q + 1 else 3
    -- or
    -- d 0 'a' = 0 ; d 0 'b' = 1
    -- d 1 'a' = 0 ; d 1 'b' = 2
    -- d 2 'a' = 0 ; d 2 'b' = 3
    -- d 3 _ = 3

-- q6 -> no instance of aba
noaba :: FSM
noaba = ([0,1,2,3], 0, [0,1,2], d) where
    d 0 'a' = 1 ; d 0 'b' = 0
    d 1 'a' = 1 ; d 1 'b' = 2
    d 2 'a' = 3 ; d 2 'b' = 0
    d 3 _ = 3

-- q7 every instance of aa comes before every instance of bb
nobbaa :: FSM
nobbaa = ([0,1,2,3,4,5,6], 0, [0,1,2,3,4,5], d) where
     d 0 'a' = 0 ; d 0 'b' = 1
     d 1 'a' = 2 ; d 1 'b' = 4
     d 2 'a' = 3 ; d 2 'b' = 1
     d 3 'a' = 3 ; d 3 'b' = 4
     d 4 'a' = 5 ; d 4 'b' = 4
     d 5 'a' = 6 ; d 5 'b' = 4
     d 6 _ = 6

-- q8 even number of a's and an even number of b's.
evenasbs :: FSM
evenasbs = ([0,1,2,3], 0, [0,2], d) where
    d 0 'a' = 1 ; d 0 'b' = 3
    d 1 'a' = 2 ; d 1 'b' = 0
    d 2 'a' = 3 ; d 2 'b' = 1
    d 3 'a' = 0 ; d 3 'b' = 2


-- Testing functions

-- FSM test by RE comparison
-- generic tester when you know the RE
-- it only compares the first 100 values

test fsm re = [accept1 fsm s == match1 re s | s <- s10]

new_re_test fsm re = and [accept1 fsm s == match1 re s | s <- s10]

re_test fsm re = and [accept1 fsm s | re <- take 100 (lang_of re),
                s <- s10, (lol s) == re] -- not a good test

-- when working on this I came up with the generic version
abb_test = and [accept1 eabb s | re <- take 100 (lang_of q1),
                s <- s10, (lol s) == re]

oddbs_test = and [accept1 oddbs w == odd (num_bs w) | w <- s10] where
  num_bs w = sum (map (\x -> if x == 'b' then 1 else 0) w)

-- this works because there is only 7 lol strings with length <= to 4 in ab
dups_test = and [(accept1 dups w)
                == (elem (lol w) (take 7 (lang_of ab))) | w <- s4]

-- Note: didn't finish these three in time.
avoid_aab_test = and [isInfixOf "aab" s == not (accept1 avoid_aab s) | s <- s10]
end_ab_test =  and [ isSuffixOf "ab" s == accept1 end_ab s | s <- s10]
exactly_test x = [w | w <- s10, accept1 (exactly x) w] == [x]
--Note: exactly test only works for input strings within s10



-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

s10 = strings 10  -- or larger, if you like
s4 = strings 4

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

-----------------------------------------
-------------- Testing ------------------
-----------------------------------------
-- *Main> dstar oddbs 0 "aa"
-- 0
-- *Main> dstar oddbs 0 "aaa"
-- 0
-- *Main> dstar oddbs 0 "aaaaa"
-- 0
-- *Main> dstar oddbs 0 "aaaaab"
-- 1
-- *Main> dstar oddbs 0 "aaaaababababababbbbabababbbabababbba"
-- 1
-- *Main> dstar oddbs 0 "aaaabb"
-- 0
-- *Main> checkFSM oddbs
-- True
-- *Main> accept1 oddbs "a"
-- False
-- *Main> accept1 oddbs ""
-- False
-- *Main> accept1 oddbs "b"
-- True
-- *Main> accept1 dups ""
-- True
-- *Main> accept1 dups "a"
-- False
-- *Main> accept1 dups "aa"
-- True
-- *Main> accept1 dups "aabb"
-- True
-- *Main> accept1 dups "baabb"
-- False
-- *Main> accept1 dups "bbaabb"
-- True
-- *Main> accept2 dups "aabb"
-- True
-- *Main> accept2 dups "aab"
-- False
-- *Main> accept2 dups "ab"
-- False
-- *Main> accept2 dups "abb"
-- False
-- *Main> accept2 dups "bb"
-- True
-- *Main> accept2 dups ""
-- True

-- *Main> checkFSM avoid_aab
-- True
-- *Main> accept1 avoid_aab "aab"
-- False
-- *Main> accept1 avoid_aab ""
-- True
-- *Main> accept1 avoid_aab "a"
-- True
-- *Main> accept1 avoid_aab "b"
-- True
-- *Main> accept1 avoid_aab "aa"
-- True
-- *Main> accept1 avoid_aab "ab"
-- True
-- *Main> accept1 avoid_aab "ba"
-- True
-- *Main> accept1 avoid_aab "bb"
-- True
-- *Main> accept1 avoid_aab "aba"
-- True
-- *Main> accept1 avoid_aab "abb"
-- True
-- *Main> accept1 avoid_aab "abba"
-- True
-- *Main>
-- *Main> accept1 avoid_aab "abbaab"
-- False

-- *Main> checkFSM end_ab
-- True
-- *Main> accept1 end_ab ""
-- False
-- *Main> accept1 end_ab "a"
-- False
-- *Main> accept1 end_ab "b"
-- False
-- *Main> accept1 end_ab "ab"
-- True
-- *Main> accept1 end_ab "aa"
-- False
-- *Main> accept1 end_ab "ba"
-- False
-- *Main> accept1 end_ab "bb"
-- False
-- *Main> accept1 end_ab "bba"
-- False
-- *Main> accept1 end_ab "bbab"
-- True
-- *Main> accept1 end_ab "bbabsfdafdsfdsfgadhgdfghdsafsdfnmkdgfnklsadngkjdsngab"
-- True

-- *Main> checkFSM (exactly "a")
-- True
-- *Main> checkFSM (exactly "")
-- True
-- *Main> accept1 (exactly "abb") "abb"
-- True
-- *Main> accept1 (exactly "") "abb"
-- False
-- *Main> accept1 (exactly "") ""
-- True
-- *Main> accept1 (exactly "a") ""
-- False
-- *Main> accept1 (exactly "a") "a"
-- True
-- *Main> accept1 (exactly "ab") "a"
-- False
-- *Main> accept1 (exactly "ab") "ab"
-- True
-- *Main> accept1 (exactly "ab") "aba"
-- False
-- *Main> accept1 (exactly "abb") "aba"
-- False
-- *Main> accept1 (exactly "abba") "aba"
-- False

-- *Main> exactly_test "bbbbbbbbbb"
-- True
-- *Main> exactly_test "bbbbbbbbbbb"
-- False
-- *Main> re_test eabb ena
-- False
-- *Main> re_test eabb q1
-- True
-- *Main> re_test eabb q3
-- False
-- *Main> re_test ea ena
-- True
-- *Main> re_test ea q1
-- False
-- *Main> re_test ala_alb q1
-- False
-- *Main> re_test ala_alb q5
-- False
-- *Main> re_test ala_alb q3
-- True
-- *Main> re_test no2adj q4
-- True
-- *Main> re_test no2adj q7
-- False
-- *Main> checkFSM nobbb
-- True
-- *Main> re_test nobbb q5
-- True
-- *Main> re_test nobbb q7
-- False
-- *Main> checkFSM noaba
-- True
-- *Main> re_test noaba q6
-- True
-- *Main> re_test noaba q8
-- False
-- *Main> checkFSM nobbaa
-- True
-- *Main> re_test nobbaa q8
-- False
-- *Main> re_test nobbaa q7
-- True
-- *Main> checkFSM evenasbs
-- True
-- *Main> re_test evenasbs q7
-- False
-- *Main> re_test evenasbs q8
-- True


----------------------------------------
---------------- END LAB 5 -------------
----------------------------------------



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

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

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
