---- Eric Smrkovsky ----
---- CSci 119, Lab 1 ----
---- CSUFresno, Fall 2020 ----

-- Note: you will replace all instances of "undefined" below with your answers.


---- Boolean operators

-- The following code tests whether "and" is commutative:
bools = [True, False]
and_commutes = and [(p && q) == (q && p) | p <- bools, q <- bools]

-- Write similar defintions that test whether "or" is commutative,
-- "and" and "or" are associative, "and" distributes over "or",
-- "or" distributes over "and"
or_commutes = and [(p || q) == (q || p) | p <- bools, q <- bools]
and_assoc = and [((p && q) && a) == (p && (q && a)) | p <- bools, q <- bools, a <- bools]
or_assoc = and [((p || q) || a) == (p || (q || a)) | p <- bools, q <- bools, a <- bools]
and_dist = and [(p && (q || a)) == ((p && q) || (p && a)) | p <- bools, q <- bools, a <- bools]
or_dist = and [(p || (q && a)) == ((p || q) && (p || a)) | p <- bools, q <- bools, a <- bools]

-- The exclusive-or operation on Bool in Haskell is equivalent to /=.
-- Test the properties of this operation (commutativity, associativity,
-- distributivity over and+or, and distributivity of and+or over it)
-- using the same method as above
xor_commutes = and [(p /= q) == (q /= p) | p <- bools, q <- bools]
xor_assoc    = and [((p /= q) /= a) == (p /= (q /= a)) | p <- bools, q <- bools, a <- bools]
xor_dist_and = and [(p /= (q && a)) == ((p /= q) && (p /= a)) | p <- bools, q <- bools, a <- bools]
xor_dist_or  = and [(p /= (q || a)) == ((p /= q) || (p /= a)) | p <- bools, q <- bools, a <- bools]
and_dist_xor  = and [(p && (q /= a)) == ((p && q) /= (p && a)) | p <- bools, q <- bools, a <- bools]
or_dist_xor = and [(p || (q /= a)) == ((p || q) /= (p || a)) | p <- bools, q <- bools, a <- bools]

-- The implication operator on Bool in Haskell is equivalent to <=.
-- Check whether implication is associative or commutative:
assoc_imp = and [((p <= q) <= a) == (p <= (q <= a)) | p <- bools, q <- bools, a <- bools]
comm_imp = and [(p <= q) == (q <= p) | p <- bools, q <- bools]


----- Evaluating statements involving quantifiers

-- Assume that the universe of discourse is the set {1,2,3,4,5,6,7,8},
-- that is, that the word "number" temporarily means 1, 2, ..., 8.
-- Your solutions to the problems below should work no matter what
-- finite list of integers u is. For example, u = [5, 2, 17, 58, 21].

u = [1..3]
--u = [5, 2, 17, 58, 21]
--u = [5, 10, 15]

-- Translate each of the following statements first, in a comment, into a
-- logical statement involving forall, exists, and, or, imp, and not,
-- and then into Haskell code that checks ("brute force") whether
-- the statement is true. I'll work one example.

-- 1. "Every number that's greater than 2 is greater than 1"
-- A: forall n, (n > 2) imp (n > 1)
prob1_1 = and [(n > 2) <= (n > 1) | n <- u]   -- direct translation
prob1_2 = and [n > 1 | n <- u, n > 2]         -- using bounded quantifier

-- 2. Every number is either greater than 1 or less than 2
-- A: forall n, (n > 1) or (n < 2)
prob2 = and [((n > 1) || (n < 2)) | n <- u]

-- 3. Every two numbers are comparable with <= (i.e., either one is <=
--    the other or vice-versa)
-- A: forall x, forall n, (x >= n) or (n >= x)
prob3 = and [((x <= n) || (n <= x)) | x <- u, n <- u]

-- 4. There is an odd number greater than 4
-- A: exists x, x is odd and x > 4
prob4 = or [x > 4 | x <- u, odd x]

-- 5: There are two odd numbers that add up to 10
-- A: exists x, exists y, x is odd and y is odd and x plus y equals 10
prob5 = or [(x + y == 10) | x <- u, odd x, y <- u, odd y]

-- 6. For every odd number, there is a greater even number (use the Haskell
--    predicates odd, even :: Integral a => a -> Bool)
-- A: forall x, if x is odd than exists y, y is even and y > x
prob6 = and [or [x < y | y <- u, even y] | x <- u, odd x]

-- 7. For every even number, there is a greater odd number
-- A: forall x, if x is even then exists y, y is odd and y > x
prob7 = and [or [x < y | y <- u, odd y] | x <- u, even x]

-- 8. There are two odd numbers that add up to 6
-- A: exists x, exists y, x is odd and y is odd and x plus y equals 6
prob8 = or [(x + y == 6) | x <- u, odd x, y <- u, odd y]

-- 9. There is a number that is at least as large as every number
--    (i.e., according to >=)
-- A: exists x, forall y, x >= y
prob9 = or [and [x >= y | y <- u] | x <- u]

-- 10. For every number, there is a different number such that there are no
--    numbers between these two.
-- A: forall y, exists x, x /= y, forall z, if x < y then (not!?) x < z and z < y else y < z and z < x
prob10 = and [or [and [not((x < z && z < y) || (y < z && z < x)) | z <- u] | x <- u, x /= y] | y <- u]
