import Mathlib.Tactic.Linarith

/-
Credits to @SabrinaJewson for the idea!
-/

/-
Grid:
.X..
..XX
.X.X

Filled grid:
112X
2X21
X210

Initial:
11??
2???
????

Next:
112?
2X2?
????

Next:
112?
2X2?
?210

Next:
112?
2X21
?210

All numbers revealed, end.
-/

-- variable {x00 x01 x02 x03 x10 x11 x12 x13 x20 x21 x22 x23 : Nat}

-- def grid00 := x00 = 0 → x01 + x10 + x11 = 1
-- def grid01 := x01 = 0 → x00 + x02 + x10 + x11 + x12 = 0
-- def grid02 := x02 = 0 → x01 + x03 + x11 + x12 + x13 = 3
-- def grid03 := x03 = 0 → x02 + x12 + x13 = 2
-- def grid10 := x10 = 0 → x00 + x01 + x11 + x20 + x21 = 2
-- def grid11 := x11 = 0 → x00 + x01 + x02 + x10 + x12 + x20 + x21 + x22 = 3
-- def grid12 := x12 = 0 → x01 + x02 + x03 + x11 + x13 + x21 + x22 + x23 = 0
-- def grid13 := x13 = 0 → x02 + x03 + x12 + x22 + x23 = 0
-- def grid20 := x20 = 0 → x10 + x11 + x21 = 1
-- def grid21 := x21 = 0 → x10 + x11 + x12 + x20 + x22 = 0
-- def grid22 := x22 = 0 → x11 + x12 + x13 + x21 + x23 = 4
-- def grid23 := x23 = 0 → x12 + x13 + x22 = 0

open Nat

def game
  {x00 x01 x02 x03 x10 x11 x12 x13 x20 x21 x22 x23 : Nat}
  -- Mine count
  (mines : x00 + x01 + x02 + x03 + x10 + x11 + x12 + x13 + x20 + x21 + x22 + x23 = 3)
  -- Grid information
  (grid00 : x00 = 0 → x01 + x10 + x11 = 1)
  (grid01 : x01 = 0 → x00 + x02 + x10 + x11 + x12 = 1)
  (grid02 : x02 = 0 → x01 + x03 + x11 + x12 + x13 = 2)
  (grid10 : x10 = 0 → x00 + x01 + x11 + x20 + x21 = 2)
  (grid12 : x12 = 0 → x01 + x02 + x03 + x11 + x13 + x21 + x22 + x23 = 2)
  (grid13 : x13 = 0 → x02 + x03 + x12 + x22 + x23 = 1)
  (grid21 : x21 = 0 → x10 + x11 + x12 + x20 + x22 = 2)
  (grid22 : x22 = 0 → x11 + x12 + x13 + x21 + x23 = 1)
  (grid23 : x23 = 0 → x12 + x13 + x22 = 0)
  -- Assumptions that shouldn't be here - should be encoded in type
  (f00 : x00 = 0 ∨ x00 = 1) (f01 : x01 = 0 ∨ x01 = 1)
  (f02 : x02 = 0 ∨ x02 = 1) (f03 : x03 = 0 ∨ x03 = 1)
  (f10 : x10 = 0 ∨ x10 = 1) (f11 : x11 = 0 ∨ x11 = 1)
  (f12 : x12 = 0 ∨ x12 = 1) (f13 : x13 = 0 ∨ x13 = 1)
  (f20 : x20 = 0 ∨ x20 = 1) (f21 : x21 = 0 ∨ x21 = 1)
  (f22 : x22 = 0 ∨ x22 = 1) (f23 : x23 = 0 ∨ x23 = 1)
  -- Initial board state (from the left) - we only need to indicate which are revealed
  (s00 : x00 = 0) (s01 : x01 = 0) (s10 : x10 = 0) :
  -- End goal
  x00 = 0 ∧ x01 = 0 ∧ x02 = 0 ∧ x10 = 0 ∧ x12 = 0 ∧ x13 = 0 ∧ x21 = 0 ∧ x22 = 0 ∧ x23 = 0 := by

  -- Step 0: Simplify with given information
  simp [*] at *

  -- Step 1: At the corner, x11 is a mine (x11 = 1)]
  have s11 : x11 = 1 := by linarith
  simp [*] at *
  
  -- Step 2: Reveal x02 and x12 from new information (x02 = 0, x12 = 0)
  have s02 : x02 = 0 := by linarith
  have s12 : x12 = 0 := by linarith
  simp [*] at *
  
  -- Step 3: Deduce that one of x03 and x13 is a mine (x03 + x13 = 1)
  -- Step 4: Reveal x21, x22 and x23 from new information (x21 = 0, x22 = 0, x23 = 0)
  -- Step 5: Reveal x13 (x13 = 0)
  have s21 : x21 = 0 := by linarith
  have s22 : x22 = 0 := by linarith
  have s23 : x23 = 0 := by linarith
  simp [*] at *