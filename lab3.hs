-- CSci 119, Lab 3
-- Eric Smrkovsky
-- Fall 2020
-- See https://hackage.haskell.org/package/base-4.14.0.0/docs/Data-List.html
import Data.List (sort, stripPrefix)


---------------- General list functions

-- Normalize a list: sort and remove duplicates
norm :: Ord a => [a] -> [a]
norm xs = rad $ sort xs where
  rad :: Eq a => [a] -> [a]  -- Remove adjacent duplicates
  rad [] = []
  rad [x] = [x]
  rad (x:ys@(y:zs)) | x == y = rad ys
                    | otherwise = x : rad ys

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

---------------- Length-ordered lists

-- Length-Ordered Lists over "character type" a (aka "strings over a")
-- Invariant: In LOL n xs, n == length xs
-- Note that automatically-derived Ord instance correctly orders LOLs
data LOL a = LOL Int [a] deriving (Eq,Ord)--,Show)

instance Show a => Show (LOL a) where
  show (LOL n xs) = show xs   --comment out if add show

-- Empty list (epsilon)
eps :: LOL a
eps = LOL 0 []

-- Smart constructor for LOL a, establishes invariant
lol :: [a] -> LOL a
lol xs = LOL (length xs) xs

-- Concatenation of LOLs, preserves invariant
dot :: LOL a -> LOL a -> LOL a
dot (LOL n xs) (LOL m ys) = LOL (n+m) (xs++ys)

-- Reverse of LOLs, preserves invariant--see theorem in notes
rev :: LOL a -> LOL a
rev (LOL n xs) = LOL n (reverse xs)

---------------- Languages

-- Normalized lists of LOLs (aka "languages")
-- Invariant: xs :: Lang a implies xs is ordered with no duplicates
type Lang a = [LOL a]


-- Constructor for languages, establishes invariant
lang :: Ord a => [[a]] -> Lang a
lang xs = norm $ map lol xs

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

-- Concatenation of languages--preserve order, no duplicates!
cat :: Ord a => Lang a -> Lang a -> Lang a
cat xs [] = []
cat [] ys = []
cat (x:xs) ys =  merge (map (dot x) ys) (cat xs ys)

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

---- Regular expressions and the languages they denote
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


-- Test all of the above operations extensively!
-- norm
-- *Main> norm []
-- []
-- *Main> norm [[1],[2],[1,2],[1],[2],[1,2,3],[2,1]]
-- [[1],[1,2],[1,2,3],[2],[2,1]]
-- *Main> norm [[1],[2],[1,2],[1],[2],[1],[2],[1,2],[1],[2]]
-- [[1],[1,2],[2]]

-- cart
-- *Main> cart [] []
-- []
-- *Main> cart [(1,1)] [(1,1)]
-- [((1,1),(1,1))]
-- *Main> cart [1,2,3] [1,2,3]
-- [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)]
-- *Main> cart [1,2,3] [1,2,3,4]
-- [(1,1),(1,2),(1,3),(1,4),(2,1),(2,2),(2,3),(2,4),(3,1),(3,2),(3,3),(3,4)]

-- power
-- *Main> power []
-- [[]]
-- *Main> power [2,3]
-- [[],[2],[2,3],[3]]
-- *Main> power [1,2,3]
-- [[],[1],[1,2],[1,2,3],[1,3],[2],[2,3],[3]]
-- power [3,1,2,3]
-- [[],[3],[3,1],[3,1,2],[3,1,2,3],[3,1,3],[3,2],[3,2,3],[3,3],[1],[1,2]
-- ,[1,2,3],[1,3],[2],[2,3],[3]]

-- eps
-- *Main> [eps,eps,eps]
-- [LOL 0 [],LOL 0 [],LOL 0 []]
-- *Main> eps
-- LOL 0 []

-- lol
-- *Main> lol []
-- []
-- *Main> lol [1,2,3]
-- [1,2,3]
-- *Main> lol "1,2,3"
-- "1,2,3"
-- *Main> lol "123"
-- "123"
-- *Main> lol "abcd"
-- "abcd"

-- dot
-- *Main> dot (lol "") (lol "")
-- ""
-- *Main> dot eps eps
-- []
-- *Main> a = lol "abcd"
-- *Main> b = lol "abcd"
-- *Main> dot a b
-- "abcdabcd"
-- *Main> dot a (dot a b)
-- "abcdabcdabcd"

-- rev
-- *Main> a
-- "abcd"
-- *Main> b
-- "abcd"
-- *Main> rev a
-- "dcba"
-- *Main> rev (lol "")
-- ""
-- *Main> rev eps
-- []
-- *Main> rev (dot a b)
-- "dcbadcba"
-- *Main> rev (dot eps (dot a (lol "123")))
-- "321dcba"

-- lang
-- *Main> lang ["abc", "def", "geh", "g", "a", "ag", "A"]
-- ["A","a","g","ag","abc","def","geh"]
-- *Main> lang ["abc", "def", "geh"]
-- ["abc","def","geh"]
-- *Main> a
-- "abcd"
-- *Main> b
-- "abcd"
-- *Main> lang [[a],[b],[a,b]]
-- [["abcd"],["abcd","abcd"]]
-- *Main> lang ["abcd","abc","ab","a",""]
-- ["","a","ab","abc","abcd"]

-- memb
-- *Main> l2 = lang ["b", "cb", "def", "l"]
-- *Main> l = lang ["a", "ab", "abc", "k"]
-- *Main> memb (lol "") l
-- False
-- *Main> memb (lol "a") l
-- True
-- *Main> memb (lol "abbc") l
-- False
-- *Main> memb (lol "ack") l
-- False
-- *Main> memb (lol "k") l
-- True

-- merge
-- *Main> l
-- ["a","k","ab","abc"]
-- *Main> l2
-- ["","k"]
-- *Main> l3
-- ["a"]
-- *Main> merge l l2
-- ["","a","k","ab","abc"]
-- *Main> memb eps (merge l l3)
-- False
-- *Main> memb eps (merge l l2)
-- True

-- cat
-- *Main> list1 = lang ["a", "ab", "abb", "ba", "c"]
-- *Main> list2 = lang ["ab", "abc", "baa", "c", "ca"]
-- *Main> cat list1 list2
-- ["ac","cc","aab","abc","aca","bac","cab","cca","aabc",
-- "abaa","abab","abbc","abca","baab","baca","cabc","cbaa",
-- "ababc","abbaa","abbab","abbca","baabc","babaa","abbabc","abbbaa"]

-- leftq
-- *Main> l
-- ["a","k","ab","abc"]
-- *Main> l3
-- ["a"]
-- *Main> leftq (lol"a") l
-- ["","b","bc"]
-- *Main> leftq (lol"b") l
-- []

-- lang_of
-- *Main> lang_of Empty
-- []
-- *Main> lang_of (Star Empty)
-- [""]
-- *Main> lang_of (Union (Let 'a') (Let 'b'))
-- ["a","b"]
-- *Main> lang_of (Cat (Let 'a') (Let 'b'))
-- ["ab"]
-- [""]
-- *Main> take 10 (lang_of (Star (Cat (Let 'a') (Let 'b'))))
-- ["","ab","abab","ababab","abababab",
-- "ababababab","abababababab","ababababababab","abababababababab","ababababababababab"]
-- *Main> take 10 (lang_of (Star (Let 'a')))
-- ["","a","aa","aaa","aaaa","aaaaa","aaaaaa","aaaaaaa","aaaaaaaa","aaaaaaaaa"]

-- onestr
-- *Main> onestr "a"
-- Let 'a'
-- *Main> onestr "abc"
-- Cat (Let 'a') (Cat (Let 'b') (Let 'c'))
-- *Main> onestr "a"
-- Let 'a'
-- *Main>  onestr ""
-- Star Empty
-- *Main> onestr "ab"
-- Cat (Let 'a') (Let 'b')
-- *Main>  onestr "abcd"
-- Cat (Let 'a') (Cat (Let 'b') (Cat (Let 'c') (Let 'd')))
-- *Main> onestr "abcde"
-- Cat (Let 'a') (Cat (Let 'b') (Cat (Let 'c') (Cat (Let 'd') (Let 'e'))))

-- finite
-- *Main> finite ["",""]
-- Union (Star Empty) (Star Empty)
-- *Main>  finite ["","a"]
-- Union (Star Empty) (Let 'a')
-- *Main>  finite ["a","ab"]
-- Union (Let 'a') (Cat (Let 'a') (Let 'b'))
-- *Main>  finite ["a","ab","abc"]
-- Union (Let 'a') (Union (Cat (Let 'a') (Let 'b')) (Cat (Let 'a') (Cat (Let 'b') (Let 'c'))))
-- *Main> finite ["a"]
-- Let 'a'
-- *Main> finite [""]
-- Star Empty
