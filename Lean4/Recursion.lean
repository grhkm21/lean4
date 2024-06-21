import Mathlib.Data.Nat.Basic

open Nat

def recursion1 : ℕ → ℕ → ℕ → ℕ → ℕ
| 0, sum, _, _ => sum
| (fuel + 1), sum, start, stop =>
  recursion1 fuel (sum + start) (start + 1) stop

def f1 (n : ℕ) := recursion1 n 0 0 n

def recursion2 : ℕ → ℕ → ℕ → ℕ 
| sum, start, stop =>
  if h : stop ≤ start then
    sum
  else
    have : stop - (start + 1) < stop - start := by
      apply sub_lt_self Nat.zero_lt_one $ succ_le_of_lt $ zero_lt_sub_of_lt $ lt_of_not_ge h
    recursion2 (sum + start) (start + 1) stop
  termination_by _ sum start stop => stop - start

def f2 (n : ℕ) := recursion2 0 0 n

set_option profiler true

#eval f1 1000000  -- 236ms
#eval f2 1000000  -- 173ms
#eval f1 5000000  -- 1.23s
#eval f2 5000000  -- 878ms
#eval f1 10000000 -- 2.34s
#eval f2 10000000 -- 1.71s