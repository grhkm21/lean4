import Mathlib.Data.ZMod.Basic

open Nat Finset

set_option trace.profiler true
set_option trace.Meta.synthInstance true

#check Finset.choose
example (n k p : ℕ) : n.choose k % p = (n.choose k + n.choose k) % p := by
  save
  sorry
