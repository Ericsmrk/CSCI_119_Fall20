-- Lab 8 Solution: Additional constructions, nondeterministic machines

import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)
type FSM a = ([a], a, [a], a -> Char -> a)

------------ FSM construction ----------------------
-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM Int
oddbs = ([0,1], 0, [1], d) where
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

n_oddbs :: NFSM Int
n_oddbs = ([0,1], [0], [1], d) where
  d q 'a' = [q]        -- stay in the same state
  d q 'b' = [1 - q]    -- switch states

e_oddbs :: EFSM Int
e_oddbs = ([0,1], [0], [1], d, e) where
  d q 'a' = [q]        -- stay in the same state
  d q 'b' = [1 - q]    -- switch states
  e = [(0,0)]

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

n_avoid_aab :: NFSM Int
n_avoid_aab = ([0,1,2,3], [0], [0,1,2], d) where
  d 0 'a' = [1]
  d 0 'b' = [0]
  d 1 'b' = [0]
  d 1 'a' = [2]
  d 2 'a' = [2]
  d 2 'b' = [3]
  d 3 _ = [3]

e_avoid_aab :: EFSM Int
e_avoid_aab = ([0,1,2,3], [0], [0,1,2], d, e) where
  e = [(0,0),(0,1),(0,2),(0,3)]
  d 0 'a' = [1]
  d 0 'b' = [0]
  d 1 'b' = [0]
  d 1 'a' = [2]
  d 2 'a' = [2]
  d 2 'b' = [3]
  d 3 _ = [3]

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM Int
end_ab = ([0,1,2], 0, [2], d) where
  d _ 'a' = 1
  d 0 'b' = 0
  d 1 'b' = 2
  d 2 'b' = 0

-- Define a machine that accepts all strings that end in "ab" and test
n_end_ab :: NFSM Int
n_end_ab = ([0,1,2], [0], [2], d) where
  d _ 'a' = [1]
  d 0 'b' = [0]
  d 1 'b' = [2]
  d 2 'b' = [0]

-- Define a machine that accepts all strings that end in "ab" and test
e_end_ab :: EFSM Int
e_end_ab = ([0,1,2], [0], [2], d, e) where
  e = [(0,0),(1,0),(1,1),(2,0),(2,2)]
  d _ 'a' = [1]
  d 0 'b' = [0]
  d 1 'b' = [2]
  d 2 'b' = [0]

---------------- Given functions ----------------

-- All strings on sigma of length <= n (useful for testing)
strings :: Int -> [String]
strings n = concat $ [replicateM i sigma | i <- [0..n]]

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

-- delta* construction (trans -> trans on string)
star :: (a -> Char -> a) -> (a -> [Char] -> a)
star = foldl'

-- Unary set closure (where "set" = normalized list) ask how to use
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
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Let x:rs)


---------------- Part 1: Additional constructions ----------------
-- Define the operations given in Section 7 of the notes

-- Intersection
inters :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
inters (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = fs1 >< fs2
  d (q1, q2) a = (d1 q1 a, d2 q2 a)

-- Complement only reverse final states  (machine_bar)
compl :: Eq a => FSM a -> FSM a
compl (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = qs1
  s  = s1
  fs = [fs | fs <- qs, notElem fs fs1]
  d q a = d1 q a

-- this displays the homo_dir image of an re with substitutions for k
hd_image re = Compact $ homo_dir k_ab_ba $ toRE re where
              -- k(a) = "ab" and k(b) = "ba"
              k_ab_ba l = if l == 'a' then "ab" else "ba"

-- Direct homomorphic image: k is a substitution
homo_dir :: (Char -> String) -> RegExp -> RegExp
homo_dir k Empty = Empty
homo_dir k (Let a) = onestr (k a)
homo_dir k (Union r1 r2) = Union (homo_dir k r1) (homo_dir k r2)
homo_dir k (Cat r1 r2) = Cat (homo_dir k r1) (homo_dir k r2)
homo_dir k (Star r) = Star (homo_dir k r)

-- this displays the homo_inv image of an fsm with substitutions for k
hi_image fsm = show_fsm m1 where
                -- k(a) = "ab" and k(b) = "ba"
                k_ab_ba l = if l == 'a' then "ab" else "ba"
                m1@(qs, s, fs, d) = homo_inv k_ab_ba fsm

-- Inverse homomorphic image (use delta star)
homo_inv :: Eq a => (Char -> String) -> FSM a -> FSM a
homo_inv k (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = qs1
  s  = s1
  fs = fs1
  d q a = star d1 q $ k a

-- Right quotient by a finite language
quot_right :: Eq a => [String] -> FSM a -> FSM a
quot_right l2 (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = qs1
  s  = s1
  fs = [q | q <- qs1, w <- l2, elem (star d1 q w) fs1]
  d q a = d1 q a


---------------- Part 2: Nondeterministic machines ----------------

-- Nondeterministic FSMs, indexed by their type of state
-- All states are normalized and the output of d is normalized
-- M = (states, starts, finals, transitions)
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

-- nap_hat d qs a == normalized list of all transitions possible from qs on a
nap_hat :: Ord a => Trans a -> [a] -> Char -> [a]
nap_hat d qs a = norm $ concat [d q a | q <- qs]

-- nap_hat_star d qs w == normalized list of transitions possible from qs on w
nap_hat_star :: Ord a => Trans a -> [a] -> [Char] -> [a]
nap_hat_star d qs w = star (nap_hat d) qs w

-- nacc m w == m accept the string w
nacc :: Ord a => NFSM a -> [Char] -> Bool
nacc (_, ss, fs, ds) w = overlap (nap_hat_star ds ss w) fs


-- Nondeterministic FSMs with epsilon moves, indexed by their type of state
-- M = (states, starts, finals, transitions, epsilon-moves)
type Eps a = [(a, a)]
type EFSM a = ([a], [a], [a], Trans a, Eps a)

-- Normalized epsilon closure of a set of states (Hint: use uclosure)
eclose :: Ord a => Eps a -> [a] -> [a]
eclose eps states = uclosure states (\q -> [(qp) |(q, qp) <- eps])

-- eap_has d es qs a == eclosure of transitions possible from qs on a
eap_hat :: Ord a => (Trans a, Eps a) -> [a] -> Char -> [a]
eap_hat (d, es) qs a = eclose es (norm $ concat [d q a | q <- qs])

eap_hat_star :: Ord a => (Trans a, Eps a) -> [a] -> [Char] -> [a]
eap_hat_star (d, es) qs w = star (eap_hat (d,es)) qs w

eacc :: Ord a => EFSM a -> [Char] -> Bool
eacc (qs, ss, fs, ds, eps) w =
                        overlap (eap_hat_star (ds, eps) (eclose eps ss) w) fs

---------------- Part 3: Conversion between machines ----------------

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = qs1
  s  = [s1]
  fs = fs1
  d q a = [d1 q a]


-- Conversion from NFSM to FSM by the "subset construction"
nfsm_to_fsm :: Ord a => NFSM a -> FSM [a]
nfsm_to_fsm (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = power qs1
  s  = s1
  fs = [x | x <- qs, overlap x fs1]
  d q a = nap_hat d1 q a



-- Similar conversion from EFSM to FSM using epsilon closure
efsm_to_fsm :: Ord a => EFSM a -> FSM [a] -- end of lec
efsm_to_fsm (qs1, s1, fs1, d1, e1) = (qs, s, fs, d) where
  qs = power qs1
  s  = eclose e1 s1
  fs = [x | x <- qs, overlap x fs1]
  d q a = eap_hat (d1, e1) q a


-- Tests:

-- 1. m and fsm_to_nfsm m accept the same strings
test1 fsm = let m = fsm_to_nfsm fsm in
            and [nacc m s == accept1 fsm s | s <- strings 10]

-- *Main> test1 oddbs
-- True
-- *Main> test1 avoid_aab
-- True
-- *Main> test1 end_ab
-- True

-- 2. m and nfsm_to_fsm m accept the same strings

test2 nfsm = let m = nfsm_to_fsm nfsm in
            and [nacc nfsm s == accept1 m s | s <- strings 10]

-- *Main> test2 n_avoid_aab
-- True
-- *Main> test2 n_oddbs
-- True
-- *Main> test2 n_oddbs
-- True

-- 3. m and efsm_to_fsm m accept the same strings

test3 efsm = let m = efsm_to_fsm efsm in
            and [eacc efsm s == accept1 m s | s <- strings 10]

-- *Main> test3 e_oddbs
-- True
-- *Main> test3 e_avoid_aab
-- True
-- *Main> test3 e_end_ab
-- True
--------------Extra Code-----------
-- The one-string and finite languages of Theorem 3.2.
onestr :: String -> RegExp
onestr [] = Star Empty
onestr [x] = Let x
onestr (x:xs) = Cat (Let x) (onestr xs)

-- Gives the delta* function (recursive in w) (q is start state)
dstar :: FSM a -> a -> [Char] -> a
dstar _ q "" = q
dstar m@(_, _, _, d) q (w:ws) = dstar m (d q w) ws

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(_, s, fs, _) w = elem (dstar m s w) fs

-- Use constructions above to get reduced machine associated with regex
-- Warning: it can take a lot of time/memory to compute these for "big" regex's
-- We will see much better ways later in the course
re2fsm :: RegExp -> FSM Int
re2fsm Empty = emptyFSM
re2fsm (Let c) = letterFSM c
re2fsm (Union r1 r2) = reduce $ unionFSM (re2fsm r1) (re2fsm r2)
re2fsm (Cat r1 r2) = reduce $ catFSM (re2fsm r1) (re2fsm r2)
re2fsm (Star r1) = reduce $ starFSM (re2fsm r1)


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

--------------Testing--------------

k_ab_ba l = if l == 'a' then "ab" else "ba" -- k value for testing
-- works for FSMs
showT (qs, s, fs, d) = [(q, l, (d q l))| q <- qs, l <- sigma]
show_trans (qs, s, fs, d) = [d q l| q <- qs, l <- sigma]
show_fsm m@(qs, s, fs, d) = (qs ,s ,fs ,show_trans m, showT m)

--test that both homo_dir and homo_inv produce opposites (doesn't work)
-- homo_test re = show_fsm (homo_inv k_ab_ba (re2fsm (toRE re)))
  --              ==
    --            show_fsm (re2fsm (homo_dir k_ab_ba (toRE re)))

-------inters------
-- *Main> (x,y,z,d) = inters oddbs avoid_aab
-- *Main> accept1 (x,y,z,d) "aab"
-- False
-- *Main> accept1 (x,y,z,d) "ab"
-- True
-- *Main> accept1 (x,y,z,d) "abb"
-- False
-- *Main> accept1 (x,y,z,d) "ababbaba"
-- False
-- *Main> accept1 (x,y,z,d) "ababbabab"
-- True
-- *Main> (x1,y1,z1,d1) = oddbs
-- *Main> (x2,y2,z2,d2) = avoid_aab
-- *Main> x1
-- [0,1]
-- *Main> x2
-- [0,1,2,3]
-- *Main> x
-- [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)]
-- *Main> y
-- (0,0)
-- *Main> y1
-- 0
-- *Main> y2
-- 0
-- *Main> z
-- [(1,0),(1,1),(1,2)]
-- *Main> z1
-- [1]
-- *Main> z2
-- [0,1,2]
-- *Main> show_trans $ inters oddbs avoid_aab
-- [(0,1),(1,0),(0,2),(1,0),(0,2),(1,3),(0,3),(1,3),(1,1),
--               (0,0),(1,2),(0,0),(1,2),(0,3),(1,3),(0,3)]

--------compl-------
-- *Main> (x,y,z,d) = compl oddbs
-- *Main> accept1 (x,y,z,d) "b"
-- False
-- *Main> accept1 (x,y,z,d) "bb"
-- True
-- *Main> accept1 (x,y,z,d) "bbb"
-- False
-- *Main> accept1 (x,y,z,d) "bbbaaaaaaaaaaaaa"
-- False
-- *Main> accept1 (x,y,z,d) "bbbaaaaaaaaaaaaaa"
-- False
-- *Main> accept1 (x,y,z,d) "bbbaaaaaaaaaaaaaba"
-- True
-- *Main> (x1,y1,z1,d1) = oddbs
-- *Main> x
-- [0,1]
-- *Main> x1
-- [0,1]
-- *Main> y
-- 0
-- *Main> y1
-- 0
-- *Main> z
-- [0]
-- *Main> z1
-- [1]
-- *Main> show_trans (x,y,z,d)
-- [0,1,1,0]
-- *Main> show_trans oddbs
-- [0,1,1,0]

--------homo_dir-------
---testing function defined above
-- *Main> hd_image "@"
-- @
-- *Main> hd_image ""
-- *** Exception: lab8.hs:(136,3)-(141,39): Non-exhaustive patterns in function toRE'

-- *Main> hd_image "a"
-- ab
-- *Main> hd_image "b"
-- ba
-- *Main> hd_image "ab"
-- *** Exception: lab8.hs:(136,3)-(141,39): Non-exhaustive patterns in function toRE'

-- *Main> hd_image "ab."
-- abba
-- *Main> hd_image "ab+"
-- ab+ba
-- *Main> hd_image "ab+*"
-- (ab+ba)*
-- *Main> hd_image "aab.+*"
-- (ab+abba)*
-- *Main> hd_image "aab.+ba.a.b.a.+*"
-- (ab+abba+baababbaab)*
-- *Main> hd_image "a*"
-- (ab)*

-----------homo_inv---------
-- *Main> hi_image oddbs
-- ([0,1],0,[1],[1,1,0,0],[(0,'a',1),(0,'b',1),(1,'a',0),(1,'b',0)])
-- *Main> show_fsm oddbs
-- ([0,1],0,[1],[0,1,1,0],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',0)])
-- *Main> hi_image avoid_aab
-- ([0,1,2,3],0,[0,1,2],[0,1,3,1,3,3,3,3],[(0,'a',0),(0,'b',1),(1,'a',3),(1,'b',1),
-- (2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)])
-- *Main> show_fsm avoid_aab
-- ([0,1,2,3],0,[0,1,2],[1,0,2,0,2,3,3,3],[(0,'a',1),(0,'b',0),(1,'a',2),(1,'b',0),
-- (2,'a',2),(2,'b',3),(3,'a',3),(3,'b',3)])
-- *Main> accept1 (homo_inv k (re2fsm (toRE "b"))) "ba"
-- False
-- *Main> accept1 (homo_inv k (re2fsm (toRE "b"))) ""
-- False
-- *Main> accept1 (homo_inv k (re2fsm (toRE "ba."))) ""
-- False
-- *Main> accept1 (homo_inv k (re2fsm (toRE "ba."))) "b"
-- True
-- *Main> accept1 (homo_inv k (re2fsm (toRE "ab."))) "a"
-- True
-- *Main> accept1 (homo_inv k (re2fsm (toRE "ab.b.a."))) "ab"
-- True

---------quot_right--------------
-- only final state is 0 which means empty string is only possibility
-- *Main> show_fsm $ quot_right ["a"] (re2fsm (toRE "a"))
-- ([0,1,2],0,[0],[1,2,2,2,2,2],[(0,'a',1),(0,'b',2),(1,'a',2),(1,'b',2),(2,'a',2),(2,'b',2)])

-- *Main> show_fsm $ quot_right [""] (re2fsm (toRE "a")) --fs is 1 so only a in string
-- ([0,1,2],0,[1],[1,2,2,2,2,2],[(0,'a',1),(0,'b',2),(1,'a',2),(1,'b',2),(2,'a',2),(2,'b',2)])
-- *Main> show_fsm $ quot_right [""] (re2fsm (toRE "b")) --fs is 1 so only b in string
-- ([0,1,2],0,[1],[2,1,2,2,2,2],[(0,'a',2),(0,'b',1),(1,'a',2),(1,'b',2),(2,'a',2),(2,'b',2)])

--------fsm_to_nfsm------------
-- *Main> show_fsm $ fsm_to_nfsm oddbs
-- ([0,1],[0],[1],[[0],[1],[1],[0]],[(0,'a',[0]),(0,'b',[1]),(1,'a',[1]),(1,'b',[0])])
-- *Main> show_fsm oddbs
-- ([0,1],0,[1],[0,1,1,0],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',0)])
-- *Main> showT oddbs
-- [(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',0)]
-- *Main> showT $ fsm_to_nfsm oddbs
-- [(0,'a',[0]),(0,'b',[1]),(1,'a',[1]),(1,'b',[0])]
-- *Main> test1 oddbs
-- True
-- *Main> test1 avoid_aab
-- True
-- *Main> test1 end_ab
-- True

--------nfsm_to_fsm------------
--  above
--------esm_to_fsm------------
--  above
