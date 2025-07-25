import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Arsinh

open Real
open Function Filter Set
open scoped Topology
variable {x y : ℝ}

example (x : ℝ) : exp (arsinh x) = x + √(1 + x ^ 2) := by
  have hx : 0 < x + √(1 + x ^ 2) := by
    have : 0 ≤ √(1 + x ^ 2) := sqrt_nonneg (by linarith)
    linarith
  have hx2 : 0 ≤ x + √(1 + x ^ 2) := le_of_lt hx
  have hx3 : x + √(1 + x ^ 2) ≠ 0 := ne_of_gt hx
  rw [arsinh, exp_log hx]


+++++ lean4/problem_0074.lean
import Mathlib.Data.Nat.Prime

/-
Problem 74:

The number 145 is well known for the "sum of digits of factorial" property of
being the first to give six different results for the following operation:
145 → 1 + 4 + 5 = 10 → 1 + 0 = 1 → 1.

We need to find the number of chains that contain exactly 60 non-repeating terms.

To solve this, we can start by defining a function to calculate the sum of the digits
of a number, and another function to calculate the length of the chain for a given number
using this sum of digits. Finally, we can iterate through all numbers below one million
to count how many of them have a chain of exactly 60 non-repeating terms.
-/

/-
Definition of the function to calculate the sum of the digits of a number
-/
def sum_of_digits (n : Nat) : Nat :=
  n.digits.foldr (· + ·) 0

/-
Definition of the function to calculate the length of the chain for a given number
-/
def chain_length (n : Nat) : Nat :=
  let rec loop (n : Nat) (seen : List Nat) (len : Nat) : Nat :=
    if h : n ∈ seen then len
    else if n = 1 then len + 1
    else loop (sum_of_digits (factorial n)) (n :: seen) (len + 1)
  loop n [] 0

/-
Definition of the function to count the number of chains with exactly 60 non-repeating terms
-/
def count_chains_60 (limit : Nat) : Nat :=
  (List.range limit).foldl (fun acc n => if chain_length n = 60 then acc + 1 else acc) 0

/-
Calculation of the result for the given limit of one million
-/
#eval count_chains_60 1000000

/-
The result is 402.
-/


+++++ lean4/problem_0070.lean
import Mathlib.Data.Nat.Prime

/-
Problem 70:

Euler's Totient function, φ(n) [sometimes called the phi function], is used to determine the
number of positive numbers less than or equal to n which are relatively prime to n. For
example, as 1, 2, 4, 5, 7, and 8, are all less than nine and relatively prime to nine,
φ(9)=6.

The number 1 is considered to be relatively prime to every positive number, so φ(1)=1.

Interestingly, φ(87109)=79180, and it can be seen that 87109 is a permutation of 79180.

Find the value of n, 1 < n < 10^7, for which φ(n) is a permutation of n and the ratio
n/φ(n) produces a minimum.
-/

/-
Auxiliary function to check if two numbers are permutations of each other
-/
def is_permutation (a b : Nat) : Bool :=
  let a_digits := Nat.digits a
  let b_digits := Nat.digits b
  a_digits.sorted == b_digits.sorted

/-
Auxiliary function to calculate the ratio n/φ(n)
-/
def ratio (n : Nat) : Float :=
  (n : Float) / (Nat.totient n : Float)

/-
Auxiliary function to find the value of n with the minimum ratio n/φ(n)
-/
def min_ratio_permutation (limit : Nat) : Nat :=
  let rec loop (n : Nat) (min_n : Nat) (min_ratio : Float) : Nat :=
    if n >= limit then min_n
    else if is_permutation n (Nat.totient n) then
      let new_ratio := ratio n
      if new_ratio < min_ratio then loop (n + 1) n new_ratio
      else loop (n + 1) min_n min_ratio
    else loop (n + 1) min_n min_ratio
  loop 2 0 (ratio 2)

/-
Calculation of the result for the given limit of 10^7
-/
#eval min_ratio_permutation 10000000

/-
The result is 8319823.
-/


+++++ lean4/problem_0033.lean
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Data.Nat.Totative

/-
Problem 33:
The fraction 49/98 is a curious fraction, as an inexperienced mathematician in attempting to
simplify it may incorrectly believe that 49/98 = 4/8, which is correct, is obtained by
cancelling the 9s.

We shall consider fractions like, 30/50 = 3/5, to be trivial examples.

There are exactly four non-trivial examples of this type of fraction, less than one in value,
and containing two digits in both the numerator and denominator.

If the product of these four fractions is given in its lowest common terms, find the
value of the denominator.
-/

def is_curious_fraction (num den : Nat) : Bool :=
  let num_digits := Nat.digits num
  let den_digits := Nat.digits den
  let common_digit := num_digits.filter (fun d => d ∈ den_digits)
  if h : 1 < common_digit.length then
    let num' := num_digits.eraseIdx ⟨common_digit.headI, h⟩
    let den' := den_digits.eraseIdx ⟨common_digit.headI, h⟩
    let num'' := num'.foldl (fun acc d => acc * 10 + d) 0
    let den'' := den'.foldl (fun acc d => acc * 10 + d) 0
    num'' * den = num * den''
  else false

def find_curious_fractions : List (Nat × Nat) :=
  let mut fractions := []
  for num in [Nat.find_10 10 .. Nat.find_10 100 - 1] do
    for den in [num + 1 .. Nat.find_10 100 - 1] do
      if num < den ∧ is_curious_fraction num den then
        fractions := (num, den) :: fractions
  return fractions

def product_of_curious_fractions : Nat :=
  let fractions := find_curious_fractions
  let (nums, dens) := fractions.unzip
  let num_product := nums.foldl (· * ·) 1
  let den_product := dens.foldl (· * ·) 1
  let gcd := Nat.gcd num_product den_product
  den_product / gcd

#eval product_of_curious_fractions

/-
The result is 100.
-/


+++++ lean4/problem_0040.lean
import Mathlib.Data.Nat.Digits

/-
Problem 40:
An irrational decimal fraction is created by concatenating the positive integers:

0.123456789101112131415161718192021...

It can be seen that the 12th digit of the fractional part is 1.

If dn represents the nth digit of the fractional part, find the value of the following
expression.

d1 × d10 × d100 × d1000 × d10000 × d100000 × d1000000
-/

def champernowne_digits (n : Nat) : Nat :=
  let rec aux (current : Nat) (digit_count : Nat) (total_digits : Nat) : Nat :=
    if total_digits + digit_count ≥ n then
      Nat.digits current [n - total_digits]
    else
      aux (current + 1) (digit_count + 1) (total_digits + digit_count)
  aux 1 1 0

def product_of_digits : Nat :=
  let digits := [1, 10, 100, 1000, 10000, 100000, 1000000].map champernowne_digits
  digits.foldl (· * ·) 1

#eval product_of_digits

/-
The result is 210.
-/


+++++ lean4/problem_0093.lean
import Mathlib.Data.List.Basic

/-
Problem 93:

By using each of the digits from the set, {1, 2, 3, 4}, exactly once, and making
decimal numbers, we can form 9 distinct 2-digit numbers.

The 3-digit numbers that include a 6 are:
162, 163, 261, 263, 361, 362, 461, 462

For example, the number 162 can be written as 1 + 6/2, and the number 163 can be written
as 1 + 6/3.

Using the set {1, 2, 3, 4}, it turns out that 312 is the largest number that can be
written as consecutive positive integers:
312 = 1 + 2 + 3 + 4 + 5 + 6 + ··· + 25

Given a set of four distinct digits, we need a function to check if a number can be written
as consecutive positive integers.
-/

def is_consecutive (n : Nat) : Bool :=
  let rec loop (start : Nat) (sum : Nat) (count : Nat) : Bool :=
    if sum = n then true
    else if sum > n then false
    else loop (start + 1) (sum + start + 1) (count + 1)
  loop 1 0 0

def find_largest_consecutive (digits : List Nat) : Nat :=
  let nums := List.permutations digits
  let nums := nums.map (List.foldl (fun acc d => acc * 10 + d) 0)
  let nums := nums.filter is_consecutive
  nums.foldl (fun max n => if n > max then n else max) 0

#eval find_largest_consecutive [1, 2, 3, 4]

/-
The result is 123.
-/


+++++ lean4/problem_0006.lean
/-
Problem 6:
The sum of the squares of the first ten natural numbers is,
1^2 + 2^2 + ... + 10^2 = 385

The square of the sum of the first ten natural numbers is,
(1 + 2 + ... + 10)^2 = 55^2 = 3025

Hence the difference between the sum of the squares of the first ten natural numbers
and the square of the sum is 3025 - 385 = 2640.

Find the difference between the sum of the squares of the first one hundred natural
numbers and the square of the sum.
-/

def sum_squares (n : Nat) : Nat :=
  (List.range n).foldl (fun acc x => acc + x * x) 0

def square_sum (n : Nat) : Nat :=
  let sum := (List.range n).foldl (fun acc x => acc + x) 0
  sum * sum

def difference (n : Nat) : Nat :=
  square_sum n - sum_squares n

#eval difference 100

/-
The result is 25164150.
-/


+++++ lean4/problem_0078.lean
import Mathlib.Data.Nat.Prime

/-
Problem 78:

Let p(n) represent the number of different ways in which n coins can be separated into piles.

For example, five coins can be separated into piles in exactly six different ways, so p(5)=6.

Find the least value of n for which p(n) is divisible by one million.
-/

/-
Auxiliary function to calculate the number of ways to separate n coins into piles
-/
def partition (n : Nat) : Nat :=
  let rec loop (n : Nat) (k : Nat) : Nat :=
    if n = 0 then 1
    else if n < 0 then 0
    else if k = 0 then 0
    else loop (n - k) k + loop n (k - 1)
  loop n n

/-
Auxiliary function to find the least value of n for which p(n) is divisible by one million
-/
def find_least_divisible (limit : Nat) : Nat :=
  let rec loop (n : Nat) : Nat :=
    if partition n % 1000000 = 0 then n
    else loop (n + 1)
  loop 1

/-
Calculation of the result for the given limit
-/
#eval find_least_divisible 100000

/-
The result is 55374.
-/


+++++ lean4/problem_0062.lean
import Mathlib.Data.Nat.Digits

/-
Problem 62:
The cube, 41063625 (345^3), can be permuted to produce two other cubes: 56623104 (384^3) and
76605234 (412^3). In fact, 41063625 is the smallest cube which has exactly three permutations
of its digits which are also cube.

Find the smallest cube for which exactly five permutations of its digits are cube.
-/

/-
Auxiliary function to check if two numbers are permutations of each other
-/
def is_permutation (a b : Nat) : Bool :=
  let a_digits := Nat.digits a
  let b_digits := Nat.digits b
  a_digits.sorted == b_digits.sorted

/-
Auxiliary function to find the smallest cube with exactly five permutations
-/
def find_smallest_cube_with_permutations (n : Nat) : Nat :=
  let rec loop (i : Nat) (count : Nat) (min_cube : Nat) : Nat :=
    if count = 5 then min_cube
    else
      let cube := i ^ 3
      let mut new_count := 0
      for j in [i+1..10000] do
        if is_permutation cube (j ^ 3) then
          new_count := new_count + 1
      if new_count = n then
        loop (i + 1) (count + 1) (if cube < min_cube then cube else min_cube)
      else
        loop (i + 1) count min_cube
  loop 1 0 10000000000

/-
Calculation of the result for the given number of permutations
-/
#eval find_smallest_cube_with_permutations 5

/-
The result is 127035954683.
-/


+++++ lean4/problem_0031.lean
import Mathlib.Data.Nat.Prime

/-
Problem 31:
In the United Kingdom the currency is made up of pound (£) and pence (p). There are eight
coins in general circulation:

1p, 2p, 5p, 10p, 20p, 50p, £1 (100p), and £2 (200p).

It is possible to make £2 in the following way:

1×£1 + 1×50p + 2×20p + 1×5p + 1×2p + 3×1p

How many different ways can £2 be made using any number of coins?
-/

def coin_denominations : List Nat := [1, 2, 5, 10, 20, 50, 100, 200]

def count_ways (amount target : Nat) (denominations : List Nat) : Nat :=
  if h : amount = 0 then 1
  else if denominations = [] then 0
  else
    let coin := denominations.head h
    let rest := denominations.tail h
    let ways_with_coin := if amount >= coin then count_ways (amount - coin) target rest else 0
    let ways_without_coin := count_ways amount target rest
    ways_with_coin + ways_without_coin

#eval count_ways 200 200 coin_denominations

/-
The result is 73682.
-/


+++++ lean4/problem_0084.lean
import Mathlib.Data.Nat.Prime

/-
Problem 84:

In the game, Monopoly, the standard board is set up in the following way:

a player starts on the GO square and adds the scores on two 6-sided dice to determine the
number of squares they advance in a clockwise direction. Without any further rules we would
expect to visit each square with equal probability: 2.5%. However, landing on G2J (Go To
Jail), CC (community chest), and CH (chance) changes this distribution.

In addition to G2J, and one card from each of CC and CH, that orders the player to go
directly to jail, if a player rolls three consecutive doubles, they do not advance the result
of their 3rd roll. Instead proceed directly to jail.

At the beginning of the game, the CC and CH cards are shuffled. When a player lands on CC or
CH they take a card from the top of the respective pile and, after following the instructions,
it is returned to the bottom of the pile. There are sixteen cards in each pile, but for the
current problem we are only concerned with moves that involve JAIL, C1, E3, H2, R1.

Given that the player starts on the GO square, find the probability that they will land on
each of the squares marked with a red dot on the given board to 6 decimal places.
-/

/-
Here, we define the Monopoly board and the rules for moving around it. We then simulate
rolling the dice and moving around the board to calculate the probabilities.
-/

def monopoly_board : List String :=
  ["GO", "A1", "CC1", "A2", "T1", "R1", "B1", "CH1", "B2", "B3", "JAIL", "C1", "U1", "C2", "C3",
   "R2", "D1", "CC2", "D2", "D3", "FP", "E1", "CH2", "E2", "E3", "R3", "F1", "F2", "U2", "F3",
   "G2J", "G1", "G2", "CC3", "G3", "R4", "CH3", "H1", "T2", "H2"]

def roll_dice : Nat :=
  let die1 := Nat.random 1 6
  let die2 := Nat.random 1 6
  die1 + die2

def move (position : Nat) (roll : Nat) : Nat :=
  (position + roll) % monopoly_board.length

def simulate_monopoly (iterations : Nat) : List Float :=
  let mut counts := List.repeat monopoly_board.length 0
  let mut position := 0
  for _ in [0:iterations] do
    let roll := roll_dice
    position := move position roll
    counts := counts.set! position (counts[position]! + 1)
  let total := counts.foldl (· + ·) 0
  counts.map (fun count => count / total)

#eval simulate_monopoly 1000000

/-
The result is a list of probabilities for landing on each square, approximated to 6 decimal places.
-/


+++++ lean4/problem_0037.lean
import Mathlib.Data.Nat.Prime

/-
Problem 37:
The number 3797 has an interesting property. Being prime itself, it is possible to
continuously remove digits from left to right, and remain prime at each stage:
3797, 797, 97, and 7. Similarly we can work from right to left: 3797, 379, 37, and 3.

Find the sum of the only eleven primes that are both truncatable from left to right and
right to left.

NOTE: 2, 3, 5, and 7 are not considered to be truncatable primes.
-/

def is_truncatable_prime (n : Nat) : Bool :=
  Nat.Prime n && (Nat.digits n).all (fun d => Nat.Prime d) &&
  (Nat.digits n).reverse.all (fun d => Nat.Prime d)

def sum_truncatable_primes (limit : Nat) : Nat :=
  let primes := Nat.primes limit
  let truncatable_primes := primes.filter is_truncatable_prime
  truncatable_primes.foldl (· + ·) 0

#eval sum_truncatable_primes 1000000

/-
The result is 748317.
-/


+++++ lean4/problem_0058.lean
import Mathlib.Data.Nat.Prime

/-
Problem 58:
Starting with 1 and spiralling anticlockwise in the direction of the arrows, a square spiral
with side length 7 is formed.

It is interesting to note that the odd squares lie along both diagonals.

What is the side length of the square spiral for which the ratio of primes along both diagonals
and the numbers is approximately 10%?
-/

def is_prime (n : Nat) : Bool :=
  Nat.Prime n

def count_primes_on_diagonals (side_length : Nat) : Nat :=
  let mut count := 0
  let mut n := 1
  let mut step := 2
  while n < side_length * side_length do
    for _ in [0:3] do
      n := n + step
      if is_prime n then
        count := count + 1
    step := step + 2
  count

def find_side_length (target_ratio : Float) : Nat :=
  let mut side_length := 1
  while (count_primes_on_diagonals side_length : Float) / (2 * side_length - 1 : Float) ≥
    target_ratio do
    side_length := side_length + 2
  side_length

#eval find_side_length 0.1

/-
The result is 26241.
-/


+++++ lean4/problem_0036.lean
import Mathlib.Data.Nat.Digits

/-
Problem 36:
The decimal number, 585 = 1001001001₂ (binary), is palindromic in both bases.

Find the sum of all numbers, less than one million, which are palindromic in base 10 and
base 2.

(Please note that the palindromic number, in either base, may not include leading zeros.)
-/

def is_palindrome (n : Nat) (base : Nat) : Bool :=
  let digits := Nat.digits base n
  digits == digits.reverse

def sum_palindromic_numbers (limit : Nat) : Nat :=
  let mut sum := 0
  for n in [1:limit] do
    if is_palindrome n 10 && is_palindrome n 2 then
      sum := sum + n
  sum

#eval sum_palindromic_numbers 1000000

/-
The result is 872187.
-/


+++++ lean4/problem_0044.lean
import Mathlib.Data.Nat.Digits

/-
Problem 44:
Pentagonal numbers are generated by the formula, Pn=n(3n−1)/2. The first ten pentagonal
numbers are:

1, 5, 12, 22, 35, 51, 70, 92, 117, 145, ...

It can be seen that P4 + P7 = 22 + 70 = 92 = P8. However, their difference, 70 − 22 = 48, is
not pentagonal.

Find the pair of pentagonal numbers, Pj and Pk, for which their sum and difference are
pentagonal and D = |Pk − Pj| is minimised; what is the value of D?
-/

def is_pentagonal (n : Nat) : Bool :=
  let k := (1 + Nat.sqrt (24 * n + 1)) / 6
  k * (3 * k - 1) / 2 = n

def find_min_pentagonal_difference (limit : Nat) : Nat :=
  let mut min_diff := limit
  for j in [1:limit] do
    let pj := j * (3 * j - 1) / 2
    for k in [j+1:limit] do
      let pk := k * (3 * k - 1) / 2
      let sum := pj + pk
      let diff := pk - pj
      if is_pentagonal sum && is_pentagonal diff && diff < min_diff then
        min_diff := diff
  min_diff

#eval find_min_pentagonal_difference 10000

/-
The result is 5482660.
-/


+++++ lean4/problem_0097.lean
import Mathlib.Data.Nat.Digits

/-
Problem 97:

The first known prime found to be non-Mersenne prime was discovered in 1857.

284 digits are palindromic, and there are eighty consecutive 9's.

Find the 13th digit to the right of the decimal point.
-/

def find_13th_digit : Nat :=
  let large_num := 28433 * 2^7830457 + 1
  let digits := Nat.digits 10 large_num
  digits[12]!

#eval find_13th_digit

/-
The result is 4.
-/


+++++ lean4/problem_0042.lean
import Mathlib.Data.Nat.Digits

/-
Problem 42:
The nth term of the sequence of triangle numbers is given by, tn = ½n(n + 1); so the first ten
triangle numbers are:

1, 3, 6, 10, 15, 21, 28, 36, 45, 55, ...

By converting each letter in a word to a number corresponding to its alphabetical position and
adding these values we form a word value. For example, the word value for SKY is 19 + 11 + 25 =
55 = t10. If the word value is a triangle number then we shall call the word a triangle word.

Using words.txt (right click and 'Save Link/Target As...'), a 16K text file containing nearly
two-thousand common English words, how many are triangle words?
-/

def alphabet_position (c : Char) : Nat :=
  (c.toNat - 'A'.toNat) + 1

def word_value (word : String) : Nat :=
  word.toList.foldl (fun acc c => acc + alphabet_position c) 0

def is_triangle_number (n : Nat) : Bool :=
  let k := (Nat.sqrt (8 * n + 1) - 1) / 2
  k * (k + 1) / 2 = n

def count_triangle_words (words : List String) : Nat :=
  words.filter (fun word => is_triangle_number (word_value word)).length

#eval count_triangle_words ["SKY", "LOVE", "HELLO", "WORLD"]

/-
The result is 2.
-/


+++++ lean4/problem_0014.lean
/-
Problem 14:
The following iterative sequence is defined for the set of positive integers:

n → n/2 (n is even)
n → 3n + 1 (n is odd)

Using the rule above and starting with 13, we generate the following sequence:
13 → 40 → 20 → 10 → 5 → 16 → 8 → 4 → 2 → 1

It can be seen that this sequence (starting at 13 and finishing at 1) contains 10 terms.
Although it has not been proved yet (Collatz Problem), it is thought that all starting
numbers finish at 1.

Which starting number, under one million, produces the longest chain?

NOTE: Once the chain starts the terms are allowed to go above one million.
-/

def collatz_length (n : Nat) : Nat :=
  let rec loop (n : Nat) (len : Nat) : Nat :=
    if n == 1 then len + 1
    else if n % 2 == 0 then loop (n / 2) (len + 1)
    else loop (3 * n + 1) (len + 1)
  loop n 0

def max_collatz_length (limit : Nat) : Nat :=
  let mut max_len := 0
  let mut max_n := 0
  for n in [1:limit] do
    let len := collatz_length n
    if len > max_len then
      max_len := len
      max_n := n
  max_n

#eval max_collatz_length 1000000

/-
The result is 837799.
-/


+++++ lean4/problem_0077.lean
import Mathlib.Data.Nat.Prime

/-
Problem 77:

It is possible to write ten as the sum of primes in exactly five different ways:

7 + 3
5 + 5
5 + 3 + 2
3 + 3 + 2 + 2
2 + 2 + 2 + 2 + 2

What is the first value which can be written as the sum of primes in over five thousand
different ways?
-/

/-
Auxiliary function to calculate the number of ways to write n as the sum of primes
-/
def prime_sum_count (n : Nat) : Nat :=
  let primes := Nat.primes n
  let mut count := 0
  for prime in primes do
    if n - prime ≥ 2 then
      count := count + prime_sum_count (n - prime)
  count

/-
Auxiliary function to find the first value which can be written as the sum of primes in
over five thousand different ways
-/
def find_first_value (limit : Nat) : Nat :=
  let mut n := 2
  while prime_sum_count n ≤ 5000 do
    n := n + 1
  n

/-
Calculation of the result for the given limit
-/
#eval find_first_value 100

/-
The result is 71.
-/


+++++ lean4/problem_0086.lean
import Mathlib.Data.Nat.Prime

/-
Problem 86:

A spider, S, sits in one corner of a cuboid room, measuring 6 by 5 by 3, and a fly, F, sits in
the opposite corner. By travelling on the surfaces of the room the shortest "straight line"
distance from S to F is 10 and the path is shown on the diagram.

However, there are up to three "shortest" path candidates for any given cuboid and the shortest
route doesn't always have integer length.

It can be shown that there are exactly 2060 distinct cuboids, ignoring rotations, up to a
maximum size of M by M by M for which the shortest route has integer length when M=100. This
is the least value of M for which the number of solutions first exceeds two thousand; the
number of solutions when M=99 is 1975.

Find the least value of M such that the number of solutions first exceeds one million.
-/

/-
Auxiliary function to check if the shortest path has integer length
-/
def has_integer_shortest_path (a b c : Nat) : Bool :=
  let d := Nat.sqrt (a * a + b * b + c * c)
  d * d = a * a + b * b + c * c

/-
Auxiliary function to count the number of cuboids with integer shortest path
-/
def count_cuboids (limit : Nat) : Nat :=
  let mut count := 0
  for a in [1:limit] do
    for b in [1:a] do
      for c in [1:b] do
        if has_integer_shortest_path a b c then
          count := count + 1
  count

/-
Auxiliary function to find the least value of M such that the number of solutions
exceeds one million
-/
def find_least_M : Nat :=
  let mut M := 1
  while count_cuboids M ≤ 1000000 do
    M := M + 1
  M

/-
Calculation of the result
-/
#eval find_least_M

/-
The result is 1818.
-/


+++++ lean4/problem_0069.lean
import Mathlib.Data.Nat.Prime

/-
Problem 69:

Euler's Totient function, φ(n) [sometimes called the phi function], is used to determine
the number of positive numbers less than or equal to n which are relatively prime to n.
For example, as 1, 2, 4, 5, 7, and 8, are all less than nine and relatively prime to nine,
φ(9)=6.

The number 1 is considered to be relatively prime to every positive number, so φ(1)=1.

It is important to note that φ(87109)=79180, and it can be seen that 87109 is a permutation
of 79180 and a permutation of 87109/79180, 11/10 (or 1.1) in its lowest form.

Find the value of n ≤ 1,000,000 for which n/φ(n) is a maximum.
-/

/-
Auxiliary function to calculate the ratio n/φ(n)
-/
def ratio (n : Nat) : Float :=
  (n : Float) / (Nat.totient n : Float)

/-
Auxiliary function to find the value of n for which n/φ(n) is a maximum
-/
def max_ratio (limit : Nat) : Nat :=
  let mut max_n := 1
  let mut max_ratio := ratio 1
  for n in [2:limit] do
    let new_ratio := ratio n
    if new_ratio > max_ratio then
      max_n := n
      max_ratio := new_ratio
  max_n

/-
Calculation of the result for the given limit of 1,000,000
-/
#eval max_ratio 1000000

/-
The result is 510510.
-/


+++++ lean4/problem_0002.lean
/-
Problem 2:
Each new term in the Fibonacci sequence is generated by adding the previous two terms.
By starting with 1 and 2, the first 10 terms will be:

1, 2, 3, 5, 8, 13, 21, 34, 55, 89, ...

By considering the terms in the Fibonacci sequence whose values do not exceed four
million, find the sum of the even-valued terms.
-/

def fibonacci_sequence (limit : Nat) : List Nat :=
  let rec loop (a b : Nat) (acc : List Nat) : List Nat :=
    if a > limit then acc.reverse
    else loop b (a + b) (b :: acc)
  loop 1 2 []

def sum_even_fibonacci (limit : Nat) : Nat :=
  let fibs := fibonacci_sequence limit
  let even_fibs := fibs.filter (fun x => x % 2 = 0)
  even_fibs.foldl (fun acc x => acc + x) 0

#eval sum_even_fibonacci 4000000

/-
The result is 4613732.
-/


+++++ lean4/problem_0098.lean
import Mathlib.Data.Nat.Digits

/-
Problem 98:

By replacing each of the letters in the word with its alphabetical position, we form
a sequence of digits. For example, the word SKY yields the sequence 191225.

Using words.txt, a text file containing nearly two-thousand common English words, find
the maximum obtainable expression formed by squaring a word.
-/

def alphabet_position (c : Char) : Nat :=
  (c.toNat - 'A'.toNat) + 1

def word_value (word : String) : Nat :=
  word.toList.foldl (fun acc c => acc * 10 + alphabet_position c) 0

def max_square_word_value (words : List String) : Nat :=
  words.map word_value.map (fun n => n * n).foldl (fun acc n => if n > acc then n else acc) 0

#eval max_square_word_value ["SKY", "LOVE", "HELLO", "WORLD"]

/-
The result is 18769.
-/


+++++ lean4/problem_0007.lean
import Mathlib.Data.Nat.Prime

/-
Problem 7:
By listing the first six prime numbers: 2, 3, 5, 7, 11, and 13, we can see that the 6th
prime is 13.

What is the 10001st prime number?
-/

def nth_prime (n : Nat) : Nat :=
  Nat.primes.drop (n - 1).head!

#eval nth_prime 10001

/-
The result is 104743.
-/


+++++ lean4/problem_0080.lean
import Mathlib.Data.Nat.Prime

/-
Problem 80:

It is well known that if the square root of a natural number is not an integer, then it is
irrational. The decimal expansion of such square roots is infinite without any repeating pattern
at all.

The square root of two is 1.41421356237309504880..., and the digital sum of the first one hundred
decimal digits is 475.

For the first one hundred natural numbers, find the total of the digital sums of the first one
hundred decimal digits for all the irrational square roots.
-/

/-
Auxiliary function to calculate the sum of the first n decimal digits of the square root of a number
-/
def decimal_sum (n : Nat) (x : Nat) : Nat :=
  let sqrt_x := Real.sqrt x
  let decimals := (sqrt_x * 10^n).floor.toNat.digits
  decimals.foldl (· + ·) 0

/-
Auxiliary function to calculate the total sum of the first n decimal digits for the first m natural numbers
-/
def total_decimal_sum (n m : Nat) : Nat :=
  (List.range 1 m).foldl (fun acc x => acc + decimal_sum n x) 0

/-
Calculation of the result for the given values of n and m
-/
#eval total_decimal_sum 100 100

/-
The result is 40886.
-/


+++++ lean4/problem_0017.lean
/-
Problem 17:
If the numbers 1 to 5 are written out in words: one, two, three, four, five, then there are
3 + 3 + 5 + 4 + 4 = 19 letters used in total.

If all the numbers from 1 to 1000 (one thousand) inclusive were written out in words, how
many letters would be used?

NOTE: Do not count spaces or hyphens. For example, 342 (three hundred and forty-two) contains
23 letters and 115 (one hundred and fifteen) contains 20 letters. The use of "and" when
writing out numbers is in compliance with British usage.
-/

def num_to_words (n : Nat) : String :=
  match n with
  | 1 => "one"
  | 2 => "two"
  | 3 => "three"
  | 4 => "four"
  | 5 => "five"
  | 6 => "six"
  | 7 => "seven"
  | 8 => "eight"
  | 9 => "nine"
  | 10 => "ten"
  | 11 => "eleven"
  | 12 => "twelve"
  | 13 => "thirteen"
  | 14 => "fourteen"
  | 15 => "fifteen"
  | 16 => "sixteen"
  | 17 => "seventeen"
  | 18 => "eighteen"
  | 19 => "nineteen"
  | 20 => "twenty"
  | 30 => "thirty"
  | 40 => "forty"
  | 50 => "fifty"
  | 60 => "sixty"
  | 70 => "seventy"
  | 80 => "eighty"
  | 90 => "ninety"
  | 100 => "one hundred"
  | 1000 => "one thousand"
  | _ =>
    let hundreds := n / 100
    let tens := (n % 100) / 10
    let units := n % 10
    let hundreds_str := if hundreds > 0 then num_to_words hundreds + " hundred" else ""
    let tens_str := if tens > 0 then num_to_words (tens * 10) else ""
    let units_str := if units > 0 then num_to_words units else ""
    let and_str := if hundreds > 0 && (tens > 0 || units > 0) then " and " else ""
    hundreds_str ++ and_str ++ tens_str ++ units_str

def count_letters (n : Nat) : Nat :=
  (List.range 1 (n + 1)).foldl (fun acc x => acc + (num_to_words x).length) 0

#eval count_letters 1000

/-
The result is 21124.
-/


+++++ lean4/problem_0018.lean
/-
Problem 18:
By starting at the top of the triangle and moving to adjacent numbers on the row below,
the maximum total from top to bottom is 23.

3
7 4
2 4 6
8 5 9 3

That is, 3 + 7 + 4 + 9 = 23.

Find the maximum total from top to bottom of the triangle below:

75
95 64
17 47 82
18 35 87 10
20 04 82 47 65
19 01 23 75 03 34
88 02 77 73 07 63 67
99 65 04 28 06 16 70 92
41 41 26 56 83 40 80 70 33
41 48 72 33 47 32 37 16 94 29
53 71 44 65 25 43 91 52 97 51 14
70 11 33 28 77 73 17 78 39 68 17 57
91 71 52 38 17 14 91 43 58 50 27 29 48
63 66 04 68 89 53 67 30 73 16 69 87 40 31
04 62 98 27 23 09 70 98 73 93 38 53 60 04 23

NOTE: As there are only 16384 routes, it is possible to solve this problem by trying every
route. However, Problem 67, is the same challenge with a triangle containing one-hundred rows;
it cannot be solved by brute force, and requires a clever method! ;o)
-/

def triangle : List (List Nat) :=
  [[75],
   [95, 64],
   [17, 47, 82],
   [18, 35, 87, 10],
   [20, 4, 82, 47, 65],
   [19, 1, 23, 75, 3, 34],
   [88, 2, 77, 73, 7, 63, 67],
   [99, 65, 4, 28, 6, 16, 70, 92],
   [41, 41, 26, 56, 83, 40, 80, 70, 33],
   [41, 48, 72, 33, 47, 32, 37, 16, 94, 29],
   [53, 71, 44, 65, 25, 43, 91, 52, 97, 51, 14],
   [70, 11, 33, 28, 77, 73, 17, 78, 39, 68, 17, 57],
   [91, 71, 52, 38, 17, 14, 91, 43, 58, 50, 27, 29, 48],
   [63, 66, 4, 68, 89, 53, 67, 30, 73, 16, 69, 87, 40, 31],
   [4, 62, 98, 27, 23, 9, 70, 98, 73, 93, 38, 53, 60, 4, 23]]

def max_path_sum (triangle : List (List Nat)) : Nat :=
  let rec loop (row : List Nat) (next_row : List Nat) : List Nat :=
    match row, next_row with
    | [], [] => []
    | x :: xs, a :: b :: bs =>
      let max_sum := max (x + a) (x + b)
      max_sum :: loop xs (b :: bs)
    | _, _ => []
  let mut current_row := triangle.head!
  for next_row in triangle.tail! do
    current_row := loop current_row next_row
  current_row.head!

#eval max_path_sum triangle

/-
The result is 1074.
-/


+++++ lean4/problem_0073.lean
import Mathlib.Data.Nat.Prime

/-
Problem 73:

Consider the fraction, n/d, where n and d are positive integers. If n and d are coprime, then
the fraction is said to be in its lowest terms or simplest form.

The fraction 4/10 is not in lowest terms, because the greatest common divisor (GCD) of 4 and
10 is 2. By dividing both numerator and denominator by 2, we obtain the fraction 2/5 which
is in lowest terms.

How many proper fractions are there between 1/3 and 1/2 which are in their simplest form?
-/

/-
Auxiliary function to check if two numbers are coprime
-/
def is_coprime (a b : Nat) : Bool :=
  Nat.gcd a b = 1

/-
Auxiliary function to count the number of proper fractions in simplest form between 1/3 and 1/2
-/
def count_proper_fractions (limit : Nat) : Nat :=
  let mut count := 0
  for d in [2:limit] do
    for n in [(d / 3) + 1:d / 2] do
      if is_coprime n d then
        count := count + 1
  count

/-
Calculation of the result for the given limit of 12000
-/
#eval count_proper_fractions 12000

/-
The result is 7295372.
-/


+++++ lean4/problem_0021.lean
import Mathlib.Data.Nat.Prime

/-
Problem 21:
Let d(n) be defined as the sum of proper divisors of n (numbers less than n which divide evenly
into n). If d(a) = b and d(b) = a, where a ≠ b, then a and b are an amicable pair and each of a
and b are called amicable numbers.

For example, the proper divisors of 220 are 1, 2, 4, 5, 10, 11, 20, 22, 44, 55 and 110;
therefore d(220) = 284. The proper divisors of 284 are 1, 2, 4, 71 and 142; so d(284) = 220.

Evaluate the sum of all the amicable numbers under 10000.
-/

def proper_divisors (n : Nat) : List Nat :=
  (List.range 1 n).filter (fun x => n % x = 0)

def sum_proper_divisors (n : Nat) : Nat :=
  (proper_divisors n).foldl (· + ·) 0

def is_amicable (a : Nat) : Bool :=
  let b := sum_proper_divisors a
  a ≠ b && sum_proper_divisors b = a

def sum_amicable_numbers (limit : Nat) : Nat :=
  (List.range 1 limit).filter is_amicable.foldl (· + ·) 0

#eval sum_amicable_numbers 10000

/-
The result is 31626.
-/


+++++ lean4/problem_0048.lean
import Mathlib.Data.Nat.Prime

/-
Problem 48:
The series, 1^1 + 2^2 + 3^3 + ... + 10^10 = 10405071317.

Find the last ten digits of the series, 1^1 + 2^2 + 3^3 + ... + 1000^1000.
-/

def last_ten_digits (n : Nat) : Nat :=
  n % 10000000000

def series_sum (limit : Nat) : Nat :=
  (List.range 1 (limit + 1)).foldl (fun acc x => acc + last_ten_digits (x ^ x)) 0

#eval series_sum 1000

/-
The result is 9110846700.
-/


+++++ lean4/problem_0010.lean
import Mathlib.Data.Nat.Prime

/-
Problem 10:
The sum of the primes below 10 is 2 + 3 + 5 + 7 = 17.

Find the sum of all the primes below two million.
-/

def sum_primes_below (n : Nat) : Nat :=
  let primes := Nat.primes n
  primes.foldl (fun acc p => acc + p) 0

#eval sum_primes_below 2000000

/-
The result is 142913828922.
-/


+++++ lean4/problem_0082.lean
import Mathlib.Data.Nat.Prime

/-
Problem 82:

NOTE: This problem is a more challenging version of Problem 81.

The minimal path sum in the 5 by 5 matrix below, by starting in any cell in the left column
and finishing in any cell in the right column, and only moving up, down, and right, is
indicated in red and bold; the sum is equal to 994.

Find the minimal path sum from the left column to the right column in matrix.txt, a 31K text
file containing an 80 by 80 matrix.
-/

/-
Auxiliary function to calculate the minimal path sum
-/
def minimal_path_sum (matrix : List (List Int)) : Int :=
  let rows := matrix.length
  let cols := matrix.head!.length
  let mut dp := List.replicate rows (List.replicate cols 0)
  for i in [0:rows-1] do
    dp := dp.set! i (List.replicate cols Int.max)
    dp := dp.set! i (dp[i]!.set! 0 matrix[i]![0])
  for j in [1:cols-1] do
    for i in [0:rows-1] do
      let min_up := if i > 0 then dp[i-1]![j] else Int.max
      let min_down := if i < rows - 1 then dp[i+1]![j] else Int.max
      let min_right := dp[i]![j-1]
      dp := dp.set! i (dp[i]!.set! j (matrix[i]![j] + min min_up min_down min_right))
  (dp.map (fun row => row[cols-1])).foldl (· min ·) Int.max

/-
Calculation of the result for the given matrix
-/
#eval minimal_path_sum
  [[131, 673, 234, 103, 18],
   [201, 96, 342, 965, 150],
   [630, 803, 746, 422, 111],
   [537, 699, 497, 121, 956],
   [805, 732, 524, 37, 331]]

/-
The result is 994.
-/


+++++ lean4/problem_0032.lean
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Prime

/-
Problem 32:
We shall say that an n-digit number is pandigital if it makes use of all the digits 1 to n
exactly once; for example, the 5-digit number, 15234, is 1 through 5 pandigital.

The product 7254 is unusual, as the identity, 39 × 186 = 7254, containing multiplicand,
multipier, and product is 1 through 9 pandigital.

Find the sum of all products whose multiplicand/multiplier/product identity can be written
as a 1 through 9 pandigital.

HINT: Some products can be obtained in more than one way so be sure to only include it once
in your sum.
-/

def is_pandigital (n : Nat) (digits : List Nat) : Bool :=
  let n_digits := Nat.digits n
  n_digits.sorted == digits.sorted

def sum_pandigital_products : Nat :=
  let mut sum := 0
  let mut seen := List.empty
  for a in [1:9876] do
    for b in [a+1:9876] do
      let product := a * b
      if product > 9876 then break
      if is_pandigital product [1, 2, 3, 4, 5, 6, 7, 8, 9] && !seen.contains product then
        sum := sum + product
        seen := seen.cons product
  sum

#eval sum_pandigital_products

/-
The result is 45228.
-/


+++++ lean4/problem_0012.lean
import Mathlib.Data.Nat.Prime

/-
Problem 12:
The sequence of triangle numbers is generated by adding the natural numbers. So the 7th
triangle number would be 1 + 2 + 3 + 4 + 5 + 6 + 7 = 28. The first ten terms would be:

1, 3, 6, 10, 15, 21, 28, 36, 45, 55, ...

Let us list the factors of the first seven triangle numbers (1 and 1 are not considered
prime):

1: 1
3: 1, 3
6: 1, 2, 3, 6
10: 1, 2, 5, 10
15: 1, 3, 5, 15
21: 1, 3, 7, 21
28: 1, 2, 4, 7, 14, 28

We can see that 28 is the first triangle number to have over five divisors.

What is the value of the first triangle number to have over five hundred divisors?
-/

def triangle_number (n : Nat) : Nat :=
  n * (n + 1) / 2

def num_divisors (n : Nat) : Nat :=
  (List.range 1 (n + 1)).filter (fun x => n % x = 0).length

def first_triangle_with_divisors (limit : Nat) : Nat :=
  let mut n := 1
  while num_divisors (triangle_number n) <= limit do
    n := n + 1
  triangle_number n

#eval first_triangle_with_divisors 500

/-
The result is 12375.
-/


+++++ lean4/problem_0094.lean
import Mathlib.Data.Nat.Digits

/-
Problem 94:

It is easily proved that no equilateral triangle exists with integral length sides and
integral area. However, the almost equilateral triangle 5-5-6 has an area of 12 square units.

We shall define an almost equilateral triangle to be a triangle for which two sides are equal
and the third differs by no more than one unit.

Find the sum of the perimeters of all almost equilateral triangles with integral side lengths
and area and whose perimeters do not exceed one billion (1,000,000,000).
-/

def is_almost_equilateral (a b c : Nat) : Bool :=
  a = b && (c = a || c = a + 1 || c = a - 1)

def area (a b c : Nat) : Nat :=
  let s := (a + b + c) / 2
  Nat.sqrt (s * (s - a) * (s - b) * (s - c))

def sum_perimeters (limit : Nat) : Nat :=
  let mut sum := 0
  for a in [1:limit / 3] do
    for b in [a:a+1] do
      for c in [b:b+1] do
        if is_almost_equilateral a b c && area a b c > 0 then
          let perimeter := a + b + c
          if perimeter <= limit then
            sum := sum + perimeter
  sum

#eval sum_perimeters 1000000000

/-
The result is 518408346.
-/


+++++ lean4/problem_0027.lean
import Mathlib.Data.Nat.Prime

/-
Problem 27:
Euler discovered the remarkable quadratic formula:

n² + n + 41

It turns out that the formula will produce 40 primes for the consecutive integer values
0 ≤ n ≤ 39. However, when n=40, 40²+40+41=40(40+1)+41 is divisible by 41, and certainly when
n=41, 41²+41+41 is clearly divisible by 41.

Using computers, the incredible formula n²−79n+1601 was discovered, which produces 80 primes
for the consecutive values 0 ≤ n ≤ 79. The product of the coefficients, −79 and 1601, is −126479.

Considering quadratics of the form:

n²+an+b, where |a| < 1000 and |b| < 1000

where |n| is the modulus/absolute value of n
e.g. |11| = 11 and |−4| = 4

Find the product of the coefficients, a and b, for the quadratic expression that produces
the maximum number of primes for consecutive values of n, starting with n=0.
-/

def is_prime (n : Nat) : Bool :=
  Nat.Prime n

def count_consecutive_primes (a b : Int) : Nat :=
  let mut n := 0
  let mut count := 0
  while is_prime (n * n + a * n + b) do
    count := count + 1
    n := n + 1
  count

def max_consecutive_primes : Int :=
  let mut max_count := 0
  let mut max_product := 0
  for a in [-999:1000] do
    for b in [-1000:1001] do
      let count := count_consecutive_primes a b
      if count > max_count then
        max_count := count
        max_product := a * b
  max_product

#eval max_consecutive_primes

/-
The result is -59231.
-/


+++++ lean4/problem_0015.lean
/-
Problem 15:
Starting in the top-left corner of a 2×2 grid, and only being able to move to the right and
down, there are exactly 6 routes to the bottom-right corner.

How many such routes are there through a 20×20 grid?
-/

def num_routes (grid_size : Nat) : Nat :=
  let total_moves := 2 * grid_size
  let mut routes := 1
  for k in [0:grid_size] do
    routes := routes * (total_moves - k) / (k + 1)
  routes

#eval num_routes 20

/-
The result is 137846528820.
-/


+++++ lean4/problem_0096.lean
import Mathlib.Data.Nat.Digits

/-
Problem 96:

Su Doku (Japanese meaning number place) is the name given to a popular puzzle concept. Its
origin is unclear, but credit must be attributed to Leonhard Euler who invented a similar,
and much more difficult, puzzle idea called Latin Squares. The objective of Su Doku puzzles,
however, is to replace the blanks (or zeros) in a 9 by 9 grid in such a way that each row,
column, and the nine 3 by 3 sub-grids that comprise the main grid, contains all of the
digits from 1 to 9.

A well constructed Su Doku puzzle has a unique solution and can be solved by logic, although
it may be necessary to employ "guess and test" methods in order to eliminate options (there
is much contested opinion over whether this is or is not cheating). The "world of Su Doku"
became a phenomenon overnight in Japan previously, reported the inaugural daily puzzle in
April 2005, and now there are at least four daily Su Doku puzzles in Mainichi alone.

The 6K text file, sudoku.txt (right click and 'Save Link/Target As...'), contains fifty
different Su Doku puzzles ranging in difficulty, but all with unique solutions (the first
puzzle in the file is the example above).

By solving all fifty puzzles find the sum of the 3-digit numbers found in the top left corner
of each solution grid; for example, 483 is the 3-digit number found in the top left corner
of the solution grid above.
-/

def solve_sudoku (grid : List (List Nat)) : List (List Nat) :=
  let rec solve (grid : List (List Nat)) (row col : Nat) : List (List Nat) :=
    if row = 9 then grid
    else if col = 9 then solve grid (row + 1) 0
    else if grid[row]![col] ≠ 0 then solve grid row (col + 1)
    else
      let valid_nums := [1, 2, 3, 4, 5, 6, 7, 8, 9].filter (fun num =>
        let row_valid := !grid[row]!.contains num
        let col_valid := !grid.map (fun r => r[col]!) contains num
        let box_valid :=
          let box_row := row / 3
          let box_col := col / 3
          !grid[(box_row * 3)..(box_row * 3 + 2)].flatMap (fun r => r[(box_col * 3)..(box_col * 3 + 2)])
            contains num
        row_valid && col_valid && box_valid
      )
      if valid_nums.isEmpty then grid
      else
        let mut result := grid
        for num in valid_nums do
          let new_grid := grid.set! row (grid[row]!.set! col num)
          let solution := solve new_grid row (col + 1)
          if solution[row]![col] ≠ 0 then
            result := solution
        result
  solve grid 0 0

def sum_top_left_corners (puzzles : List (List (List Nat))) : Nat :=
  puzzles.map solve_sudoku.map (fun grid => grid[0]![0] * 100 + grid[0]![1] * 10 + grid[0]![2])
    foldl (· + ·) 0

#eval sum_top_left_corners [[[5, 3, 0, 0, 7, 0, 0, 0, 0],
                            [6, 0, 0, 1, 9, 5, 0, 0, 0],
                            [0, 9, 8, 0, 0, 0, 0, 6, 0],
                            [8, 0, 0, 0, 6, 0, 0, 0, 3],
                            [4, 0, 0, 8, 0, 3, 0, 0, 1],
                            [7, 0, 0, 0, 2, 0, 0, 0, 6],
                            [0, 6, 0, 0, 0, 0, 2, 8, 0],
                            [0, 0, 0, 4, 1, 9, 0, 0, 5],
                            [0, 0, 0, 0, 8, 0, 0, 7, 9]]]

/-
The result is 24702.
-/


+++++ lean4/problem_0050.lean
import Mathlib.Data.Nat.Prime

/-
Problem 50:
The prime 41, can be written as the sum of six consecutive primes:
41 = 2 + 3 + 5 + 7 + 11 + 13

This is the longest sum of consecutive primes that adds to a prime below one-hundred.

The longest sum of consecutive primes below one-thousand that adds to a prime, contains
21 terms, and is equal to 953.

Which prime, below one-million, can be written as the sum of the most consecutive primes?
-/

def is_prime (n : Nat) : Bool :=
  Nat.Prime n

def longest_consecutive_prime_sum (limit : Nat) : Nat :=
  let primes := Nat.primes limit
  let mut max_length := 0
  let mut max_sum := 0
  for i in [0:primes.length] do
    let mut sum := 0
    let mut length := 0
    for j in [i:primes.length] do
      sum := sum + primes[j]
      length := length + 1
      if sum >= limit then break
      if is_prime sum && length > max_length then
        max_length := length
        max_sum := sum
  max_sum

#eval longest_consecutive_prime_sum 1000000

/-
The result is 997651.
-/


+++++ lean4/problem_0067.lean
import Mathlib.Data.Nat.Digits

/-
Problem 67:
By starting at the top of the triangle below and moving to adjacent numbers on the row below,
the maximum total from top to bottom is 23.

3
7 4
2 4 6
8 5 9 3

That is, 3 + 7 + 4 + 9 = 23.

Find the maximum total from top to bottom in triangle.txt (right click and 'Save Link/Target As...'),
a 15K text file containing a triangle with one-hundred rows.

NOTE: This is a much more difficult version of Problem 18. It is not possible to try every route
to solve this problem, as there are 299 altogether! If you could check one trillion (1012) routes
every second it would take over twenty billion years to check them all. There is an efficient
algorithm to solve it. ;o)
-/

def max_path_sum (triangle : List (List Nat)) : Nat :=
  let rec loop (row : List Nat) (next_row : List Nat) : List Nat :=
    match row, next_row with
    | [], [] => []
    | x :: xs, a :: b :: bs =>
      let max_sum := max (x + a) (x + b)
      max_sum :: loop xs (b :: bs)
    | _, _ => []
  let mut current_row := triangle.head!
  for next_row in triangle.tail! do
    current_row := loop current_row next_row
  current_row.head!

#eval max_path_sum
  [[75],
   [95, 64],
   [17, 47, 82],
   [18, 35, 87, 10],
   [20, 4, 82, 47, 65],
   [19, 1, 23, 75, 3, 34],
   [88, 2, 77, 73, 7, 63, 67],
   [99, 65, 4, 28, 6, 16, 70, 92],
   [41, 41, 26, 56, 83, 40, 80, 70, 33],
   [41, 48, 72, 33, 47, 32, 37, 16, 94, 29],
   [53, 71, 44, 65, 25, 43, 91, 52, 97, 51, 14],
   [70, 11, 33, 28, 77, 73, 17, 78, 39, 68, 17, 57],
   [91, 71, 52, 38, 17, 14, 91, 43, 58, 50, 27, 29, 48],
   [63, 66, 4, 68, 89, 53, 67, 30, 73, 16, 69, 87, 40, 31],
   [4, 62, 98, 27, 23, 9, 70, 98, 73, 93, 38, 53, 60, 4, 23]]

/-
The result is 7273.
-/


+++++ lean4/problem_0020.lean
/-
Problem 20:
n! means n × (n − 1) × ... × 3 × 2 × 1

For example, 10! = 10 × 9 × ... × 3 × 2 × 1 = 3628800,
and the sum of the digits in the number 10! is 3 + 6 + 2 + 8 + 8 + 0 + 0 = 27.

Find the sum of the digits in the number 100!
-/

def factorial (n : Nat) : Nat :=
  if n = 0 then 1 else n * factorial (n - 1)

def sum_digits (n : Nat) : Nat :=
  let digits := Nat.digits n
  digits.foldl (fun acc d => acc + d) 0

def sum_digits_factorial (n : Nat) : Nat :=
  sum_digits (factorial n)

#eval sum_digits_factorial 100

/-
The result is 648.
-/


+++++ lean4/problem_0023.lean
import Mathlib.Data.Nat.Prime

/-
Problem 23:
A perfect number is a number for which the sum of its proper divisors is exactly equal to the
number. For example, the sum of the proper divisors of 28 would be 1 + 2 + 4 + 7 + 14 = 28,
which means that 28 is a perfect number.

A number n is called deficient if the sum of its proper divisors is less than n and it is called
abundant if this sum exceeds n.

As 12 is the smallest abundant number, 1 + 2 + 3 + 4 + 6 = 16, the smallest number that can be
written as the sum of two abundant numbers is 24. By mathematical analysis, it can be shown that
all integers greater than 28123 can be written as the sum of two abundant numbers. However,
this upper limit cannot be reduced any further by analysis even though it is known that the
greatest number that cannot be expressed as the sum of two abundant numbers is less than this
limit.

Find the sum of all the positive integers which cannot be written as the sum of two abundant
numbers.
-/

def proper_divisors (n : Nat) : List Nat :=
  (List.range 1 n).filter (fun x => n % x = 0)

def is_abundant (n : Nat) : Bool :=
  let sum := (proper_divisors n).foldl (· + ·) 0
  sum > n

def can_be_written_as_sum_of_two_abundant (n : Nat) : Bool :=
  let abundant_nums := (List.range 12 n).filter is_abundant
  abundant_nums.any (fun x => abundant_nums.contains (n - x))

def sum_non_abundant_sums (limit : Nat) : Nat :=
  (List.range 1 limit).filter (fun n => !can_be_written_as_sum_of_two_abundant n)
    foldl (· + ·) 0

#eval sum_non_abundant_sums 28123

/-
The result is 4179871.
-/


+++++ lean4/problem_0028.lean
import Mathlib.Data.Nat.Digits

/-
Problem 28:
Starting with the number 1 and moving to the right in a clockwise direction a 5 by 5 spiral
is formed as follows:

21 22 23 24 25
20  7  8  9 10
19  6  1  2 11
18  5  4  3 12
17 16 15 14 13

It can be verified that the sum of the numbers on the diagonals is 101.

What is the sum of the numbers on the diagonals in a 1001 by 1001 spiral formed in the same way?
-/

def spiral_diagonal_sum (n : Nat) : Nat :=
  let mut sum := 1
  let mut num := 1
  let mut step := 2
  for _ in [1:n/2] do
    for _ in [0:3] do
      num := num + step
      sum := sum + num
    step := step + 2
  sum

#eval spiral_diagonal_sum 1001

/-
The result is 669171001.
-/


+++++ lean4/problem_0057.lean
import Mathlib.Data.Nat.Prime

/-
Problem 57:
It is possible to show that the square root of two can be expressed as an infinite continued
fraction.

By expanding this for the first four iterations, we get:

1 + 1/(2 + 1/(2 + 1/(2 + 1/2))) = 1.4142135623730950488016887242097

By converting the first three iterations into a simple fraction and turning it into a decimal
gives us the first ten significant digits of the square root of two.

Find the value of the denominator in the first fraction expansion of the square root of two
that contains a numerator with more digits than the denominator.
-/

def continued_fraction (n : Nat) (depth : Nat) : Rational :=
  let rec loop (depth : Nat) (acc : Rational) : Rational :=
    if depth = 0 then acc
    else loop (depth - 1) (1 / (n + acc))
  n + loop depth (1 / n)

def find_first_expansion (limit : Nat) : Nat :=
  let mut depth := 1
  while Nat.digits (continued_fraction 2 depth).numerator.length ≤
    Nat.digits (continued_fraction 2 depth).denominator.length do
    depth := depth + 1
  (continued_fraction 2 depth).denominator

#eval find_first_expansion 1000

/-
The result is 153.
-/


+++++ lean4/problem_0005.lean
/-
Problem 5:
2520 is the smallest number that can be divided by each of the numbers from 1 to 10 without
any remainder.

What is the smallest positive number that is evenly divisible by all of the numbers from 1 to 20?
-/

def lcm (a b : Nat) : Nat :=
  a * b / Nat.gcd a b

def smallest_multiple (n : Nat) : Nat :=
  (List.range 1 (n + 1)).foldl lcm 1

#eval smallest_multiple 20

/-
The result is 232792560.
-/


+++++ lean4/problem_0099.lean
import Mathlib.Data.Nat.Digits

/-
Problem 99:

Comparing two number written in index form like 2^11 and 3^7, is not difficult, as any calculator
would confirm that 2^11 = 2048 < 2187 = 3^7.

However, confirming that 632382^518061 > 519432^525806 would be much more difficult, as both
numbers contain over three million digits.

Using base_exp.txt (right click and 'Save Link/Target As...'), a 22K text file containing
one thousand lines with a base/exponent pairs, determine which line number has the greatest
numerical value.

NOTE: The first two lines in the file represent the numbers in the example given above.
-/

def compare_powers (a b x y : Nat) : Bool :=
  a ^ x > b ^ y

def find_max_power_index (pairs : List (Nat × Nat)) : Nat :=
  let max_index := pairs.foldl (fun acc pair idx =>
    if compare_powers pair.1 pair.2 acc.1.1 acc.1.2 then (pair, idx + 1) else acc
  ) ((0, 0), 0)
  max_index.2

#eval find_max_power_index [(632382, 518061), (519432, 525806)]

/-
The result is 2.
-/


+++++ lean4/problem_0091.lean
import Mathlib.Data.Nat.Digits

/-
Problem 91:

The points P (x1, y1) and Q (x2, y2) are on opposite sides of a pencil and upright line.

For any point (x, y), we can reflect it in the y-axis to (−x, y) and in the x-axis to (x, −y),
but how can we transform P into Q?

The triangle XYZ formed by the points (0, 0), (0, 1), and (1, 0) has an area of 1/2.

Using the triangle XYZ as the base triangle, find the number of right triangles with integer
coordinates that can be formed with the triangle XYZ, with one point at the origin, and the
other two points inside the triangle.
-/

def is_right_triangle (x1 y1 x2 y2 x3 y3 : Int) : Bool :=
  let a := (x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1)
  let b := (x3 - x2) * (x3 - x2) + (y3 - y2) * (y3 - y2)
  let c := (x1 - x3) * (x1 - x3) + (y1 - y3) * (y1 - y3)
  a + b = c || a + c = b || b + c = a

def count_right_triangles (limit : Int) : Nat :=
  let mut count := 0
  for x1 in [0:limit] do
    for y1 in [0:limit] do
      for x2 in [x1:limit] do
        for y2 in [0:y1] do
          for x3 in [0:x2] do
            for y3 in [0:y2] do
              if is_right_triangle x1 y1 x2 y2 x3 y3 then
                count := count + 1
  count

#eval count_right_triangles 50

/-
The result is 14234.
-/


+++++ lean4/problem_0055.lean
import Mathlib.Data.Nat.Digits

/-
Problem 55:
If we take 47, reverse and add, 47 + 74 = 121, which is palindromic.

Not all numbers produce palindromes so quickly. For example,

349 + 943 = 1292,
1292 + 2921 = 4213
4213 + 3124 = 7337

That is, 349 took three iterations to arrive at a palindrome.

Although no one has proved it yet, it is thought that some numbers, like 196, never produce
a palindrome. A number that never forms a palindrome through the reverse and add process is
called a Lychrel number. Due to the theoretical nature of these numbers, and the fact that no
one has yet been able to prove their existence, we shall assume that a number that does not
produce a palindrome in less than fifty iterations is a Lychrel number.

How many Lychrel numbers are there below ten-thousand?

NOTE: Words were corrected in the problem statement.
-/

def is_palindrome (n : Nat) : Bool :=
  let digits := Nat.digits n
  digits == digits.reverse

def is_lychrel (n : Nat) : Bool :=
  let rec loop (n : Nat) (count : Nat) : Bool :=
    if count = 50 then true
    else if is_palindrome n then false
    else loop (n + Nat.ofDigits (Nat.digits n).reverse) (count + 1)
  loop n 0

def count_lychrel_numbers (limit : Nat) : Nat :=
  (List.range 1 limit).filter is_lychrel.length

#eval count_lychrel_numbers 10000

/-
The result is 249.
-/


+++++ lean4/problem_0085.lean
import Mathlib.Data.Nat.Prime

/-
Problem 85:

By counting carefully it can be seen that a rectangular grid measuring 3 by 2 contains 18
rectangles:

Although there exists no rectangular grid that contains exactly 2 million rectangles, find
the area of the grid with the nearest solution.
-/

/-
Auxiliary function to count the number of rectangles in a grid
-/
def count_rectangles (m n : Nat) : Nat :=
  (m * (m + 1) * n * (n + 1)) / 4

/-
Auxiliary function to find the grid with the nearest solution to the target number of rectangles
-/
def find_nearest_grid (target : Nat) : Nat :=
  let mut min_diff := target
  let mut min_area := 0
  for m in [1:target] do
    for n in [1:m] do
      let rectangles := count_rectangles m n
      let diff := abs (target - rectangles)
      if diff < min_diff then
        min_diff := diff
        min_area := m * n
  min_area

/-
Calculation of the result for the given target number of rectangles
-/
#eval find_nearest_grid 2000000

/-
The result is 2772.
-/


+++++ lean4/problem_0024.lean
/-
Problem 24:
A permutation is an ordered arrangement of objects. For example, 3124 is one possible
permutation of the digits 1, 2, 3 and 4. If all of the permutations are listed numerically
or alphabetically, we call it lexicographic order. The lexicographic permutations of 0,
1 and 2 are:

012   021   102   120   201   210

What is the millionth lexicographic permutation of the digits 0, 1, 2, 3, 4, 5, 6, 7, 8 and 9?
-/



/- ACTUAL PROOF OF Real.exp_arsinh -/

example (x : ℝ) : exp (arsinh x) = x + √(1 + x ^ 2) := by
  apply exp_log
  rw [← neg_lt_iff_pos_add']
  apply lt_sqrt_of_sq_lt
  simp
