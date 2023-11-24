import Mathlib.Data.ZMod.Basic

open Nat
/- open Finset -- makes it slow -/

set_option profiler true
set_option trace.profiler true
example (n k p : ℕ) : (choose n k) % p = (choose n k + choose n k) % p := by
  sorry
