-- Lab 9: Derivative-based conversion from RegExp' to FSM
-- (Brzozowski Construction)

import Data.List
import Data.Array

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

---- Regular expressions, along with output and input
data RegExp = Empty
             | Let Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp
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

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = parse w [] where
  parse [] [r] = r
  parse ('+':xs) (r2:r1:rs) = parse xs (Union r1 r2:rs)
  parse ('.':xs) (r2:r1:rs) = parse xs (Cat r1 r2:rs)
  parse ('*':xs) (r:rs) = parse xs (Star r:rs)
  parse ('@':xs) rs = parse xs (Empty:rs)
  parse (x:xs) rs = parse xs (Let x:rs)

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RegExp' = Zero | One | Let' Char |
               Union' [RegExp'] | Cat' [RegExp'] | Star' RegExp'
  deriving (Eq, Ord, Show)

-- Convert ordinary RegExps into extended RegExps
fromRE :: RegExp -> RegExp'
fromRE Empty = Zero
fromRE (Let c) = Let' c
fromRE (Union r1 r2) = Union' [fromRE r1, fromRE r2]
fromRE (Cat r1 r2) = Cat' [fromRE r1, fromRE r2]
fromRE (Star r1) = Star' (fromRE r1)

-- Convert extended RegExps into ordinary RegExps, eliminating Union' and Cat'
-- on lists of length < 2, and right-associating them on longer lists
fromRE' :: RegExp' -> RegExp
fromRE' Zero = Empty
fromRE' One = Star Empty
fromRE' (Let' c) = Let c
fromRE' (Union' []) = Empty
fromRE' (Union' [r]) = fromRE' r
fromRE' (Union' (r:rs)) = Union (fromRE' r) (fromRE' (Union' rs))
fromRE' (Cat' []) = Star Empty
fromRE' (Cat' [r]) = fromRE' r
fromRE' (Cat' (r:rs)) = Cat (fromRE' r) (fromRE' (Cat' rs))
fromRE' (Star' r) = Star (fromRE' r)

-- Basic postfix parser for RE', assuming binary + and ., including 0 and 1
toRE' :: String -> RegExp'
toRE' w = parse w [] where
  parse [] [r] = r
  parse ('0':xs) rs = parse xs (Zero:rs)
  parse ('1':xs) rs = parse xs (One:rs)
  parse ('+':xs) (r2:r1:rs) = parse xs (Union' [r1,r2]:rs)
  parse ('.':xs) (r2:r1:rs) = parse xs (Cat' [r1,r2]:rs)
  parse ('*':xs) (r:rs) = parse xs (Star' r:rs)
  parse (x:xs) rs = parse xs (Let' x:rs)


-- An extended regular expression simplifier
simp :: RegExp' -> RegExp'
simp Zero = Zero
simp One = One
simp (Let' c) = Let' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RegExp'] -> RegExp'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RegExp'] -> RegExp'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RegExp' -> RegExp'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RegExp'] -> [RegExp']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RegExp'] -> [RegExp']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RegExp'] -> [RegExp'] -> [RegExp']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs


-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)
type FSM a = ([a], a, [a], a -> Char -> a)


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

-- Unary set closure (where "set" = normalized list)
-- uclosure xs g == smallest set containing xs and closed under g
uclosure :: Ord a => [a] -> (a -> [a]) -> [a]
uclosure xs g = sort $ stable $ iterate close (xs, []) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = norm $ filter (`notElem` xs') $ concatMap g fr

---------------- Lab 9 begins here ----------------

-- Bypassable for extended REs, computed directly by recursion.
byp :: RegExp' -> Bool -- opposite or proper
byp Zero = False
byp One = True
byp (Let' c) = False
byp (Union' rs) = or [byp x| x <- rs]
byp (Cat' rs) = and [byp x| x <- rs]
byp (Star' r) = True

-- Regular-expression derivatives (aka left quotients) on extended REs,
-- computed directly by recursion.

deriv :: Char -> RegExp' -> RegExp'
deriv a Zero = Zero
deriv a One = Zero
deriv a (Let' c) = if a == c then One else Zero
deriv a (Union' rs) = Union' [deriv a r | r <- rs]
deriv a (Cat' (r:rs)) = let f = Cat' (deriv a r : rs) in -- (f is list of Cat's)
                        if byp r then Union' [f , deriv a (Cat' rs)] else f
deriv a (Star' r) = Cat' [deriv a r, Star' r]

-- Convert an RegExp' to an FSM using the derivative (Brzozowski) construction.
-- States are SIMPLIFIED extended REs.  Note: to construct all the states,
-- you will have to use another closure process.
conv :: RegExp' -> FSM RegExp'
conv r = (qs, s, fs, d) where
  qs = uclosure [simp s] (\s -> [simp (deriv l s) | l <- sigma])
  s = simp r
  fs = [q | q <- qs, byp q]
  d q l = simp (deriv l q)

-- Test, and show your tests! You may copy code from previous labs to help.

----------byp-------------
-- *Main> byp (Let' 'a')
-- False
-- *Main> byp Zero
-- False
-- *Main> byp One
-- True
-- *Main> byp (Let' 'a')
-- False
-- *Main> byp (toRE' "ab.")
-- False
-- *Main> byp (toRE' "ab+")
-- False
-- *Main> byp (toRE' "a*")
-- True

--------deriv---------
show' r = Compact (fromRE' r)
shows' states = map (Compact . fromRE') states
show_trans r = let (qs,s,fs,d) = conv r in
               shows' [d q l| q <- qs, l <- sigma]
ex1 = toRE' "abab.+*.b.ab+."
ex2 = toRE' "bab.*a.+*"

-- *Main> show' ex1
-- a(b+ab)*b(a+b)
-- *Main> deriv 'a' ex1
-- Cat' [Cat' [Cat' [One,Star' (Union' [Let' 'b',Cat' [Let' 'a',Let' 'b']])],Let' 'b'],Union' [Let' 'a',Let' 'b']]
-- *Main> show' it
-- @*(b+ab)*b(a+b)
-- *Main> deriv 'b' ex1
-- Cat' [Cat' [Cat' [Zero,Star' (Union' [Let' 'b',Cat' [Let' 'a',Let' 'b']])],Let' 'b'],Union' [Let' 'a',Let' 'b']]
-- *Main> show' it
-- @(b+ab)*b(a+b)

-- *Main> show' ex2
-- (b+(ab)*a)*
-- *Main> deriv 'a' ex2
-- Cat' [Union' [Zero,Union' [Cat' [Cat' [Cat' [One,Let' 'b'],Star' (Cat' [Let' 'a',Let' 'b'])],Let' 'a'],Cat' [One]]],Star' (Union' [Let' 'b',Cat' [Star' (Cat' [Let' 'a',Let' 'b']),Let' 'a']])]
-- *Main> show' it
-- (@+@*b(ab)*a+@*)(b+(ab)*a)*
-- *Main> deriv 'b' ex2
-- Cat' [Union' [One,Union' [Cat' [Cat' [Cat' [Zero,Let' 'b'],Star' (Cat' [Let' 'a',Let' 'b'])],Let' 'a'],Cat' [Zero]]],Star' (Union' [Let' 'b',Cat' [Star' (Cat' [Let' 'a',Let' 'b']),Let' 'a']])]
-- *Main> show' it
-- (@*+@b(ab)*a+@)(b+(ab)*a)*

----------conv---------

-- *Main> ex1
-- Cat' [Cat' [Cat' [Let' 'a',Star' (Union' [Let' 'b',Cat' [Let' 'a',Let' 'b']])],
-- Let' 'b'],Union' [Let' 'a',Let' 'b']]
-- *Main> show' ex1
-- a(b+ab)*b(a+b)
-- *Main> (qs,ss,fs,d) = conv ex1
-- *Main> length qs
-- 7
-- *Main> shows' qs
-- [@,@*+a+b+(b+ab)*ba+(b+ab)*bb,@*+b(b+ab)*ba+b(b+ab)*bb,a+b+(b+ab)*ba+(b+ab)*bb,
-- a(b+ab)*ba+a(b+ab)*bb,b(b+ab)*ba+b(b+ab)*bb,(b+ab)*ba+(b+ab)*bb]
-- *Main> shows' [ss]
-- [a(b+ab)*ba+a(b+ab)*bb]
-- *Main> shows' fs
-- [@*+a+b+(b+ab)*ba+(b+ab)*bb,@*+b(b+ab)*ba+b(b+ab)*bb] (!!!!!matches ex from lab)
-- *Main> show_trans ex1
-- [@,@,@*+b(b+ab)*ba+b(b+ab)*bb,@*+a+b+(b+ab)*ba+(b+ab)*bb,@,
-- (b+ab)*ba+(b+ab)*bb,@*+b(b+ab)*ba+b(b+ab)*bb,@*+a+b+(b+ab)*ba+(b+ab)*bb,
-- (b+ab)*ba+(b+ab)*bb,@,@,(b+ab)*ba+(b+ab)*bb,b(b+ab)*ba+b(b+ab)*bb,
-- a+b+(b+ab)*ba+(b+ab)*bb]

-- *Main> ex2
-- Star' (Union' [Let' 'b',Cat' [Star' (Cat' [Let' 'a',Let' 'b']),Let' 'a']])
-- *Main> show' ex2
-- (b+(ab)*a)*
-- *Main> (qs,ss,fs,d) = conv ex2
-- *Main> length qs
-- 3
-- *Main> shows' qs
-- [b(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,(b+(ab)*a)*]
-- *Main> shows' [ss]
-- [(b+(ab)*a)*]
-- *Main> shows' fs
-- [b(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,(b+(ab)*a)*]
-- *Main> show_trans ex2
-- [b(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,
-- b(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,(b+(ab)*a)*,b(ab)*a(b+(ab)*a)*+(b+(ab)*a)*,
-- (b+(ab)*a)*]
