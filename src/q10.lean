import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Chain

def func : List ℕ → ℕ → List ℕ
| s, n =>
  if h : s.length ≤ n then
    s
  else
    have h2 : List.length s - (n + 1) < List.length s - n := by
      apply Nat.sub_add_lt_sub _ zero_lt_one
      push_neg at h
      exact Nat.succ_le_of_lt h
    func s (n + 1)
  termination_by _ s n => s.length - n

def filter' : List ℕ → List ℕ → List ℕ
| s, [] => s
| s, (p :: ps) => filter' (s.filter (λ n => n = p ∨ n % p ≠ 0)) ps

def isPrime_aux : ℕ → ℕ → Bool
| 0, _ => false
| 1, _ => false
| 2, _ => true
| n, k =>
  if h : n ≤ k then
    true
  else if n < k * k then
    true
  else if n % k = 0 then
    false
  else
    have h1 : n - (k + 1) < n - k := by
      rw [← Nat.sub_sub]
      apply Nat.pred_lt
      simp [h]
    have h2 : n - (k + 2) < n - k := by
      apply Nat.lt_of_le_of_lt (Nat.pred_le _) h1
    isPrime_aux n (k + 2)
  termination_by _ n k => n - k

def isPrime (n : ℕ) := isPrime_aux n 3

def prefilter (l r : ℕ) := (List.range' l (r - l + 1)).filter (λ n => n = 2 ∨ n % 2 ≠ 0)

set_option profiler true

-- #eval ((prefilter 2 100).filter isPrime).sum
-- #eval ((prefilter 2 100000).filter isPrime).sum
-- #eval ((prefilter 2 500000).filter isPrime).sum
-- #eval ((prefilter 2 2000000).filter isPrime).sum

-- #eval (List.)

-- #eval (overflow [] (List.range' 0 10000)).sum
-- #eval (overflow [] (List.range' 0 100000)).sum

def base : List ℕ := List.range' 2 2000000
def small_primes : List ℕ := filter' (List.range' 2 1499) [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

-- #eval (filter' (List.range' 2 500000) small_primes).sum

-----------------------------------------------------------------------------------------

open Array Std.RBMap

-- Array implementation - Apparently arrays have builtin VM implementation, so it should be faster
def prime_sieve (n : ℕ) : Array ℕ := Id.run do
  let mut primes : Array ℕ := Array.empty
  let mut isp : Array Bool := Array.mkArray (n + 1) true
  for i in [2 : n + 1] do
    if isp[i]! then
      primes ← primes.push i
      for j in [i : n : i] do
        isp ← isp.modify j (λ _ => false)
  return primes

-- 7.25s
-- #eval (prime_sieve 2000000).toList.sum

-----------------------------------------------------------------------------------------

def linear_prime_sieve (n : ℕ) : Array ℕ := Id.run do
  let mut primes : Array ℕ := Array.empty
  let mut isp : Array Bool := Array.mkArray (n + 1) true
  for i in [2 : n + 1] do
    if isp[i]! then
      primes ← primes.push i
    for j in [: primes.size] do
      if i * primes[j]! > n then
        break
      isp ← isp.modify (i * primes[j]!) (λ _ => false)
      if i % primes[j]! = 0 then
        break
  return primes

-- 5.8s
-- #eval (linear_prime_sieve 2000000).toList.sum

-----------------------------------------------------------------------------------------

-- Project Euler, Problem 10 forum, Lucy_Hedgehog
def lucy_hedgehog (n : ℕ) : ℕ := Id.run do
  let r := n.sqrt
  let mut V := Array.empty
  let mut S := Std.HashMap.empty
  for i in [1 : r + 1] do
    V ← V.push (n / i)
  let f := n / r
  for i in [1 : f] do
    V ← V.push (f - i)
  for k in V do
    S ← S.insert k (k * (k + 1) / 2 - 1)
  for p in [2 : r + 1] do
    if S.find! p > S.find! (p - 1) then
      let sp := S.find! (p - 1)
      let p2 := p ^ 2
      for v in V do
        if v < p2 then
          break
        S ← S.insert v (S.find! v - p * (S.find! (v / p) - sp))
  return S.find! n

#eval lucy_hedgehog 2000000
#eval lucy_hedgehog 20000000
-- n = 10^8, 5.21sec
#eval lucy_hedgehog 100000000

example : lucy_hedgehog 100 = 1060 := sorry