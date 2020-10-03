-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2
-- copy code from previous labs if necessary

import Data.List (isInfixOf, isSuffixOf)  -- useful for testing in Part 2

-- Again, for this (and most) labs, the alphabet will be {a,b} to keep testing
-- easier, but your code should work just as well for any finite list.
sigma = ['a', 'b']

-- explains qsfd in lec
-- Finite State Machine M = (Q, s, F, d) with integer states
type FSM = ([Int], Int, [Int], Int -> Char -> Int)


---------------- Part 1: Representing FSMs

-- Check whether a finite state machine (qs, s, fs, d) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (s is in qs) is a state of the machine
-- (3) Final states are states (fs is a subset of qs)
-- (4) Transition function d gives a state in qs for every state in qs and
--     letter from sigma

--break up m into (qs, s, fs, d)
checkFSM :: FSM -> Bool
checkFSM (qs, s, fs, d) = undefined

-- Gives the delta* function (recursive in w) (q is start state)
dstar :: FSM -> Int -> [Char] -> Int
dstar m q w = undefined

-- Machine acceptance, Definition 1 (via delta*)
accept1 :: FSM -> [Char] -> Bool
accept1 m w = undefined

-- Machine acceptance, Definition 2 (via L_q(M))
accept2 :: FSM -> [Char] -> Bool
accept2 (qs, s, fs, d) w = aux s w where
  -- aux q w = whether the machine, starting in q, accepts w (recursive in w)
  aux :: Int -> [Char] -> Bool
  aux q w = undefined


------------ Part 2: FSM construction(does some tests at the end of lec@30min)
-- first 3 type is fsm, so need to give for variable a FSM
-- Define a machine that accepts exactly the strings with an odd number of b's
-- (Solution given for illustration)
oddbs :: FSM
oddbs = ([0,1], 0, [1], d) where -- lec has good explanation he drew a picture
  d q 'a' = q        -- stay in the same state
  d q 'b' = 1 - q    -- switch states

-- Define a machine that accepts exactly the strings that do not contain "aab"
-- as a substring and test it adequately
avoid_aab :: FSM
avoid_aab = undefined

-- Define a machine that accepts all strings that end in "ab" and test
end_ab :: FSM
end_ab = undefined

-- Define a function that takes a string and returns a machine that accepts
-- exactly that string and nothing else (compare to 'onestr' from Lab 3)
-- Hint: the expression w !! i gives the i-th character of the string w
-- (!! gives ith element of A LIST)(use to manipulate states,go to trap state?)
exactly :: String -> FSM --works with every string
exactly w = undefined -- (_,_,_,_) where


-- Test the machines above. Also, try out the exerices at the end of Section 3.2
-- in my notes as FSMs. Do they produce the same results as your RegExp's did?

-- Recursive reimplementation of strings function from Lab 4
strings :: Int -> [String]
strings n = concat [strs i | i <- [0..n]] where
  strs 0 = [""]
  strs n = [a:xs | a <- sigma, xs <- strs (n-1)]

s10 = strings 10  -- or larger, if you like

oddbs_test = and [accept1 oddbs w == odd (num_bs w) | w <- s10] where
  num_bs w = sum (map (\x -> if x == 'b' then 1 else 0) w)
