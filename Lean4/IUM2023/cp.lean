import Mathlib.Tactic

open Nat

theorem SoBad1 (h : a * b = c) (ha : 1 < a) (hb : 1 < b) : a < c :=
  lt_of_lt_of_eq (lt_mul_of_one_lt_right (zero_lt_of_lt ha) hb) h
