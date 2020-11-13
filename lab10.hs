-- lab10 CSCi 119
-- Eric Smrkovksy
import Data.List
import Data.Array
import Control.Monad (replicateM)  -- for strings function below

-- Fixed alphabet, but everything below should work for any sigma!
sigma :: [Char]
sigma = "ab"

-- Finite state machines, now indexed by the type of their states
-- M = (states, start, finals, transitions)
type FSM a = ([a], a, [a], a -> Char -> a)

-----NFSM---
type Trans a = a -> Char -> [a]
type NFSM a = ([a], [a], [a], Trans a)

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

-----------------Some RE's-----------------------
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

-- Intersection
inters :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a,b)
inters (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = fs1 >< fs2
  d (q1, q2) a = (d1 q1 a, d2 q2 a)
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

-- Easy conversion from FSM to NFSM (given)
fsm_to_nfsm :: Eq a => FSM a -> NFSM a
fsm_to_nfsm (qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = qs1
  s  = [s1]
  fs = fs1
  d q a = [d1 q a]


---------------RE's from 3.2--------------------

q1 = toRE "b*ab.b.*+*"                        -- every a followed by bb
-- OR ->
q1'   = toRE "b*ab.b.*.b*.b*ab.b.*+." -- every a followed by bb
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

-----------START LAB 10----------------------

-- Boolean binary operation on FSMs. Examples:
-- binopFSM (||) m1 m2 computes union machine
-- binopFSM (&&) m1 m2 computes intersection machine
binopFSM :: (Eq a, Eq b) => (Bool -> Bool -> Bool) -> FSM a -> FSM b -> FSM (a,b)
binopFSM op (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1, s2)
  fs = [(f1, f2) | f1 <- qs1, f2 <- qs2, op (elem f1 fs1) (elem f2 fs2)]
  d (q1, q2) a = (d1 q1 a, d2 q2 a)

-- Reverse FSM to a NFSM. Output machine accepts reverse of language of input machine.
reverseFSM :: Eq a => FSM a -> NFSM a
reverseFSM (qs1, s1, fs1, d1) = (qs, ss, fs, d) where
  qs = qs1
  ss = fs1
  fs = [s1]
  d oldq a = [newq | newq <- qs1, (d1 newq a) == oldq]   -- d q a = fs == d fs a q

-- Reachable states of a NFSM (similar to reachable but on NFSMs)
nreachable :: Ord a => NFSM a -> [a]
nreachable (_, s, _, d) = qs' where
    qs' = uclosure s (\q -> concat (map (d q) sigma))
--  qs' = uclosure s (\q -> concatMap (d q) sigma)

-- Minimize a FSM. Put all of the above together to compute the minimum machine for m
minimize :: Ord a => FSM a -> FSM [a]
minimize m@(qs1, s1, fs1, d1) = (qs, s, fs, d) where
  m_xor_m = binopFSM (/=) m m -- (step 1)
  rev1 = reverseFSM m_xor_m   -- (step 2)
  reach2 = nreachable rev1    -- (step 3)
  comp3 = [(q1, q2) | q1 <- qs1, q2 <- qs1, notElem (q1, q2) reach2] -- (step4)
  help q = [cq2 | (cq1, cq2) <- comp3, cq1 == q] -- check head use tail
  qs =  norm $ map help qs1  -- qs is the partition of 4 (equivalence relation)
  s = head[s' | s' <- qs, elem s1 s']
  fs = [eqc | eqc <- qs, elem (head eqc) fs1] -- equiv. classes where q is final
  d l a = head[list | list <- qs, elem (d1 (head l) a) list]

  -- d q a = head[q' | q' <- qs, elem (d1 q a) q']
  -- trans from m



-- Write a function eq2part that takes an equivalence relation on u as input
-- and returns the associated partition of u. You can assume that the input is
-- really an equivalence relation on u.
-- eq2part :: Reln -> [[Int]]
-- eq2part rs = help u where
  -- help :: [Int] -> [[Int]]
  -- help [] = []
  -- help (x:xs) = let h = [y | (x1,y) <- rs, x == x1]
    --             in h : help [x | x <- xs, x `notElem` h]

-- Test. For example, make sure that the minimal machine agrees with the original machine
-- on lots of input strings. Try for multiple machines.

showT (qs, s, fs, d) = [(q, l, (d q l))| q <- qs, l <- sigma]
show_trans (qs, s, fs, d) = [d q l| q <- qs, l <- sigma]
show_fsm m@(qs, s, fs, d) = (qs ,s ,fs ,show_trans m, showT m)

--new
showreach re = show_fsm $ reachable $ re2fsm re
showre2nfsm re = show_fsm $ fsm_to_nfsm $ re2fsm re

----------binopFSM-------------

testBinopUnion m1 m2 = (show_fsm $ binopFSM (||) m1 m2) == (show_fsm $ unionFSM m1 m2)
-- *Main> testBinopUnion oddbs avoid_aab
-- True
-- *Main> testBinopUnion oddbs end_ab
-- True
-- *Main> testBinopUnion avoid_aab end_ab
-- True
-- *Main> testBinopUnion end_ab  end_ab
-- True

testBinopInters m1 m2 = (show_fsm $ binopFSM (&&) m1 m2) == (show_fsm $ inters m1 m2)
-- *Main> testBinopInters oddbs end_ab
-- True
-- *Main> testBinopInters oddbs avoid_aab
-- True
-- *Main> testBinopInters avoid_aab  avoid_aab
-- True
-- *Main> testBinopInters avoid_aab  end_ab
-- True

---------reverseFSM-------------
-- Note: these check out because the final states are reversed with the start
-- and the transition functions are reversed correctly
-- *Main> show_fsm avoid_aab
-- ([0,1,2,3],0,[0,1,2],[1,0,2,0,2,3,3,3],[(0,'a',1),(0,'b',0),(1,'a',2),(1,'b',0),
-- (2,'a',2),(2,'b',3),(3,'a',3),(3,'b',3)])
-- *Main> show_fsm $ reverseFSM avoid_aab
-- ([0,1,2,3],[0,1,2],[0],[[],[0,1],[0],[],[1,2],[],[3],[2,3]],[(0,'a',[]),
-- (0,'b',[0,1]),(1,'a',[0]),(1,'b',[]),(2,'a',[1,2]),(2,'b',[]),(3,'a',[3]),
-- (3,'b',[2,3])])
-- *Main> show_fsm odd
-- odd    oddbs
-- *Main> show_fsm oddbs
-- ([0,1],0,[1],[0,1,1,0],[(0,'a',0),(0,'b',1),(1,'a',1),(1,'b',0)])
-- *Main> show_fsm $ reverseFSM oddbs
-- ([0,1],[1],[0],[[0],[1],[1],[0]],[(0,'a',[0]),(0,'b',[1]),(1,'a',[1]),
-- (1,'b',[0])])
-- *Main> show_fsm end_ab
-- ([0,1,2],0,[2],[1,0,1,2,1,0],[(0,'a',1),(0,'b',0),(1,'a',1),(1,'b',2),
-- (2,'a',1),(2,'b',0)])
-- *Main> show_fsm $ reverseFSM end_ab
-- ([0,1,2],[2],[0],[[],[0,2],[0,1,2],[],[],[1]],[(0,'a',[]),(0,'b',[0,2]),
-- (1,'a',[0,1,2]),(1,'b',[]),(2,'a',[]),(2,'b',[1])])

--------nreachable---------
-- *Main> nreachable n_avoid_aab
-- [0,1,2,3]
-- *Main> nreachable n_oddbs
-- [0,1]
-- *Main> nreachable n_end_ab
-- [0,1,2]

-------minimize---------
*Main> qs1 = ["", "a", "b", "aa", "ab", "ba", "bb"]
*Main> d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
*Main> [(q,a,d1 q a) | q <- qs1, a <- sigma]
[("",'a',"a"),("",'b',"b"),("a",'a',"aa"),("a",'b',"ab"),("b",'a',"ba"),("b",'b',"bb"),("aa",'a',"aa"),("aa",'b',"ab"),("ab",'a',"ba"),("ab",'b',"bb"),("ba",'a',"aa"),("ba",'b',"ab"),("bb",'a',"ba"),("bb",'b',"bb")]
*Main> m = (qs1, "", ["ab"], d1) :: FSM String
*Main> (qs,s,fs,d) = minimize m
*Main> [(q,a,d q a) | q <- qs, a <- sigma]
[(["","b","bb"],'a',["a","aa","ba"]),(["","b","bb"],'b',["","b","bb"]),(["a","aa","ba"],'a',["a","aa","ba"]),(["a","aa","ba"],'b',["ab"]),(["ab"],'a',["a","aa","ba"]),(["ab"],'b',["","b","bb"])]
---above matches example given---


-------building minimize---
-- *Main> qs1 = ["", "a", "b", "aa", "ab", "ba", "bb"]
-- *Main> d1 q c = if length q < 2 then q ++ [c] else tail (q ++ [c])
-- *Main> [(q,a,d1 q a) | q <- qs1, a <- sigma]
-- [("",'a',"a"),("",'b',"b"),("a",'a',"aa"),("a",'b',"ab"),("b",'a',"ba"),
-- ("b",'b',"bb"),("aa",'a',"aa"),("aa",'b',"ab"),("ab",'a',"ba"),("ab",'b',"bb"),
-- ("ba",'a',"aa"),("ba",'b',"ab"),("bb",'a',"ba"),("bb",'b',"bb")]
-- *Main> m = (qs1, "", ["ab"], d1) :: FSM String
-- *Main> show_fsm m
-- (["","a","b","aa","ab","ba","bb"],"",["ab"],
-- ["a","b","aa","ab","ba","bb","aa","ab","ba","bb","aa","ab","ba","bb"],
-- [("",'a',"a"),("",'b',"b"),("a",'a',"aa"),("a",'b',"ab"),("b",'a',"ba"),
-- ("b",'b',"bb"),("aa",'a',"aa"),("aa",'b',"ab"),("ab",'a',"ba"),("ab",'b',"bb"),
-- ("ba",'a',"aa"),("ba",'b',"ab"),("bb",'a',"ba"),("bb",'b',"bb")])
-- *Main> m = (qs1, "", ["ab"], d1) :: FSM String
-- *Main> (qs,s,fs,d) = m
-- *Main> qs
-- ["","a","b","aa","ab","ba","bb"]
-- *Main>  x = nreachable $ reverseFSM (binopFSM (/=) m m)
-- *Main> x
-- [("","a"),("","aa"),("","ab"),("","ba"),("a",""),("a","ab"),("a","b"),
-- ("a","bb"),("aa",""),("aa","ab"),("aa","b"),("aa","bb"),("ab",""),("ab","a"),
-- ("ab","aa"),("ab","b"),("ab","ba"),("ab","bb"),("b","a"),("b","aa"),("b","ab"),
-- ("b","ba"),("ba",""),("ba","ab"),("ba","b"),("ba","bb"),("bb","a"),("bb","aa"),
-- ("bb","ab"),("bb","ba")]
-- *Main> comp3 = [(q1, q2) | q1 <- qs, q2 <- qs, notElem (q1, q2) x]
-- *Main> comp3 -- these match wilsons example with an extra diagonal column
-- [("",""),("","b"),("","bb"),("a","a"),("a","aa"),("a","ba"),("b",""),("b","b"),
-- ("b","bb"),("aa","a"),("aa","aa"),("aa","ba"),("ab","ab"),("ba","a"),
-- ("ba","aa"),("ba","ba"),("bb",""),("bb","b"),("bb","bb")]

-- *Main> fs'
-- [["ab"]]
-- *Main> s' = [st | st <- qs', elem s st]
-- *Main> s'
-- [["","b","bb"]]

-- *Main> [ eqc | eqc <- ps, elem (head eqc) fs]
-- [["ab"]]
-- *Main> ps = norm $ map help qs1
-- *Main> ps
-- [["","b","bb"],["a","aa","ba"],["ab"]]
-- *Main> ps = [["","b","bb"],["a","aa","ba"],["ab","a","aa","ba"]]
-- *Main> [ eqc | eqc <- ps, elem (head eqc) fs]
-- [["ab","a","aa","ba"]]
