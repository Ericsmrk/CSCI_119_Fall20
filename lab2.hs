---- CSci 119, Fall 2020, Lab 2 ----


----- PART 1:  Testing properties of relations -----

-- As in Lab 1, we will be working with the finite universe U = [1..8],
-- but your code should work with any universe.
u = [1..8]

-- A relation, R, on U is a list of the ordered pairs of elements of U:
type Reln = [(Int,Int)]

-- For example, here are the < and <= relations
less_reln :: Reln
less_reln = [(i,j) | i <- u, j <- u, i < j]

leq_reln :: Reln
leq_reln  = [(i,j) | i <- u, j <- u, i <= j]

-- and here is the relation of equivalence mod 3:
eqmod3_reln :: Reln
eqmod3_reln = [(i,j) | i <- u, j <- u, (j - i) `mod` 3 == 0]


l1 = [(i,i) | i <- u]
l2 = [(1,2),(2,3),(1,3),(4,4)] :: [(Int,Int)]
l3 = [(2,3),(3,2)] :: [(Int,Int)]
-- Write a function refl that tests whether a relation is reflexive:
-- R is reflexive if: forall a, (a,a) in R
-- Example: [(i,i) | i <- u] is the smallest reflexive relation over u.
-- Anything that does not contain all of these 8 elements is not reflexive.
refl :: Reln -> Bool
refl rs = and[(x,x) `elem` rs | x <- u]

-- Write a function symm that tests whether a relation is symmetric:
-- R is symmetric if: forall a b, (a,b) in R -> (b,a) in R
-- Example: [(1,1), (1,2), (2,1)] is symmetric but [(1,1), (1,2)] is not.
symm :: Reln -> Bool
symm rs = and [((x, y) `elem` rs) <= ((y, x) `elem` rs) | (x,y) <- rs]

-- Write a function trans that tests whether a relation is transitive:
-- R is transistive if: forall a b c, ((a,b) in R /\ (b,c) in R) -> (a,c) in R
-- Example: [(1,2),(2,3),(1,3),(4,4)] is transitive but [(2,3),(3,2)] is not
trans :: Reln -> Bool
trans rs = and [(x, z) `elem` rs | (x, y1) <- rs, (y2, z) <- rs, y1 == y2]

-- Use the functions above to check the less, leq, and eqmod3 relations for
-- reflexivity, symmetry, and transitivity.

--NOTE: checked all three and all were correct when matched to the table in the lecture.


----- PART 2:  Finding minimal relations with combinations of properties -----

-- For the following problems, you can assume that u = [1..8].
--
-- For each of the 8 possible combinations of yes/no on reflexivity,
-- symmetry, and transitivity, find a MINIMAL relation on u that has exactly
-- that combination of properties. Add a test to check whether you got the
-- properties right. (I'll do the first one as an example.)

-- refl, symm, trans
rst :: Reln
rst = [(1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8)]
rst_test = refl rst && symm rst && trans rst

-- refl, symm, not trans
rst' :: Reln
rst' = rst ++ [(1,2), (2,1), (1,8), (8,1)]
rst'_test = refl rst' && symm rst' && not (trans rst')

-- refl, not symm, trans
rs't :: Reln
rs't = rst ++ [(1,2)]
rs't_test = refl rs't && not (symm rs't) && trans rs't

-- refl, not symm, not trans
rs't' :: Reln
rs't' = rst ++ [(1,2),(2,4)]
rs't'_test = refl rs't' && not (symm rs't' && trans rs't')

-- not refl, symm, trans
r'st :: Reln
r'st = [(1,1)]
r'st_test = not (refl r'st) && symm r'st && trans r'st

-- not refl, symm, not trans
r'st' :: Reln
r'st' = [(1,2),(2,1)]
r'st'_test = not (refl r'st') && symm r'st' && not (trans r'st')

-- not refl, not symm, trans
r's't :: Reln
r's't =  [(1,2),(2,8),(1,8)]
r's't_test = not (refl r's't && symm r's't) && trans r's't

-- not refl, not symm, not trans
r's't' :: Reln
r's't' = [(1,2),(2,3)]
r's't'_test = not (refl r's't' && symm r's't' && trans r's't')


---- PART 3: Partitions of u -----

-- Again, the functions in this part should work with any finite universe, u

-- A partitition, P, of u is a list of blocks, which are lists of elements
-- of u, that satisfies these conditions:
-- nontrivial: forall X in P, exists x in U, x in X;
--             equivalently, {} not in P
-- total:      forall x in U, exists X in P, x in X
-- disjoint:   forall X,Y in P (exists a, a in X /\ a in Y) -> X = Y,
--             equivalently, forall X,Y in P, X /= Y -> X intersect Y = {}

nontrivial :: [[Int]] -> Bool
nontrivial ls = or [and [x/= [] | x <- ls] | x <- u]

total :: [[Int]] -> Bool
total ls = and [or [x `elem` l | l <- ls] | x <- u]

disjoint :: [[Int]] -> Bool
disjoint = undefined

-- For example, here is the partitition of u = [1..8] corresponding to eqmod3_reln:
eqmod3_part :: [[Int]]
eqmod3_part = [[1,4,7], [2,5,8], [3,6]]

-- Write a function, part, that tests whether a list of lists is a partition of u
part :: [[Int]] -> Bool
part bs = undefined

-- Write a function eq2part that takes an equivalence relation on u as input
-- and returns the associated partition of u. You can assume that the input is
-- really an equivalence relation on u.
eq2part :: Reln -> [[Int]]
eq2part rs = undefined


-- Write a function part2eq that takes a partition of u as input and returns
-- the associated equivalence relation on u. You can assume that the argument
-- is really a partition of u.
part2eq :: [[Int]] -> Reln
part2eq bs = [(x,y) | r <- bs, x <- r, y <- r]
