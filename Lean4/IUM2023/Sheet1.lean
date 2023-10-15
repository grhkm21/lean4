import Mathlib.Tactic
import Mathlib.Data.Nat.Prime

open Nat

/- If you see me type FIX everywhere, it is because
   Lean induction is being annoying :( -/
macro "FIX" : tactic => `(tactic | try rewrite [zero_eq] at *)

variable {x y z a b c d m n : ℕ}

namespace Problem1

theorem PartA : x * 1 = x := by rw [one_eq_succ_zero, mul_succ, mul_zero, zero_add]

theorem PartB : 0 * x = 0 := by
  induction' x with x hx
  FIX
  · rw [mul_zero]
  · rw [mul_succ, add_zero, hx]

theorem PartC : (succ x) * y = x * y + y := by
  induction' y with y hy
  FIX
  · rw [mul_zero, mul_zero, add_zero]
  · rw [mul_succ, hy, mul_succ, add_right_comm, add_succ, succ_add, add_succ]

theorem PartD : x * y = y * x := by
  induction' y with y hy
  FIX
  · rw [PartB, mul_zero]
  · rw [mul_succ, PartC, ←hy]

theorem PartE : 1 * x = x := by rw [PartD, PartA]

theorem PartF : x * (y + z) = x * y + x * z := by
  induction' z with z hz
  FIX
  · rw [add_zero, mul_zero, add_zero]
  · rw [add_succ, mul_succ, hz, mul_succ, add_assoc]

theorem PartG : (x + y) * z = x * z + y * z := by
  rw [PartD, PartF, PartD, @PartD z]

theorem PartH : (x * y) * z = x * (y * z) := by
  induction' z with z hz
  FIX
  · rw [mul_zero, mul_zero, mul_zero]
  · rw [mul_succ, mul_succ, hz, PartF]

end Problem1

-------------------------------------------------------------------------------

namespace Problem2

theorem PartA (h1 : x ≤ y) (h2 : y ≤ z) : x ≤ z := by
  sorry

theorem PartB (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  sorry

end Problem2

-------------------------------------------------------------------------------

namespace Problem3

/- We can assume this -/
#check succ_le_iff

theorem PartA : x < succ x := by sorry

theorem PartB : 0 < succ x := by sorry

theorem PartC : ¬(x < 0) := by sorry

theorem PartD : (x < y → x ≤ y) ∧ (x = y → x ≤ y) := sorry

theorem PartE : x ≤ y → (x < y ∨ x = y) := sorry

theorem PartF : ¬(x < x) := sorry

end Problem3

-------------------------------------------------------------------------------

namespace Problem4

example (h : x ≠ 0) : ∃ y, x = succ y := exists_eq_succ_of_ne_zero h

theorem Problem (hx : x ≠ 0) (h : a * x = b * x) : a = b := by
  let ⟨y, hy⟩ := exists_eq_succ_of_ne_zero hx
  rw [hy] at h
  induction' a with a ha generalizing b
  induction' b with b hb <;> FIX
  · trivial
  · exfalso
    rw [zero_mul] at h
    trivial
  · cases' b with b
    FIX
    · rw [zero_mul] at h
      trivial
    · rw [succ_mul, succ_mul, Nat.add_right_cancel_iff] at h
      rw [ha h]

/- Alternative solution below without induction -/
lemma le_or_le (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction' x with x hx
  · left
    exact Nat.zero_le y
  · cases' hx with h h
    · let ⟨z, hz⟩ := Nat.le.dest h
      cases' z with z ; FIX
      · right
        rw [←hz, add_zero]
        exact le_succ x
      · left
        rw [←hz, add_succ, succ_eq_add_one, succ_eq_add_one, add_comm x z, add_assoc, add_comm z]
        exact le_add_right _ _
    · right
      exact le_trans h (le_succ x)

example (h : a ≤ b) : ∃ c, a + c = b := le.dest h
lemma eq_of_mul_eq_right_and_le (h : x ≠ 0) (h' : a * x = b * x) (hab : a ≤ b) : a = b := by
  let ⟨c, hc⟩ := Nat.le.dest hab
  rw [←hc, ←add_zero (a * x), add_mul] at h'
  have hcx : c = 0 ∨ x = 0 := Nat.mul_eq_zero.mp (add_left_cancel h'.symm)
  have hc' : c = 0 := (or_iff_not_imp_right.mp hcx) h
  rw [←hc, hc', add_zero]

lemma mul_left_cancel (h : x ≠ 0) (h' : a * x = b * x) : a = b := by
  cases' le_or_le a b with hab hab
  · exact eq_of_mul_eq_right_and_le h h' hab
  · exact (eq_of_mul_eq_right_and_le h h'.symm hab).symm

end Problem4

-------------------------------------------------------------------------------

namespace Problem5

theorem PartA (h : a * b = c) (h' : c ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  by_contra h
  rw [not_and_or] at h
  push_neg at h
  cases' h with ha hb
  · rw [ha, zero_mul] at h
    exact h' h.symm
  · rw [hb, mul_zero] at h
    exact h' h.symm

lemma PartB' (h : a * b = c) (h' : c ≠ 0) : a ≤ c := by
  let ⟨_, hb⟩ := PartA h h'
  rw [←h]
  cases' b with b hb
  FIX
  · exfalso
    exact hb (refl 0)
  · rw [mul_succ]
    apply Nat.le_add_left

theorem PartB (h : a * b = c) (h' : c ≠ 0) : a ≤ c ∧ b ≤ c := by
  exact ⟨PartB' h h', PartB' (by rw [←h, mul_comm]) h'⟩

lemma PartC_lemma1 (h : 1 < a) : ∃ b, a = succ b :=
  exists_eq_succ_of_ne_zero $ not_eq_zero_of_lt h

theorem PartC' (h : a * b = c) (ha : 1 < a) (hb : 1 < b) : a < c := by
  have hc : c ≠ 0 := by
    by_contra' hc
    have ⟨a', ha'⟩ := PartC_lemma1 ha
    have ⟨b', hb'⟩ := PartC_lemma1 hb
    rw [hc, ha', hb'] at h
    exact (succ_ne_zero _) h
  have := PartB' h hc
  by_cases h' : a = c
  · exfalso
    rw [←mul_one c, ←h', mul_comm, mul_comm a] at h
    rw [Problem4.Problem (not_eq_zero_of_lt ha) h] at hb
    exact hb.false
  · exact lt_of_le_of_ne this h'

theorem PartC (h : a * b = c) (ha : 1 < a) (hb : 1 < b) : a < c ∧ b < c := by
  exact ⟨PartC' h ha hb, PartC' (by rw [←h, mul_comm]) hb ha⟩

/- What is the definition of .Prime? The `irreducible` one? -/
theorem PartD (h : 1 < c) (hc : ¬c.Prime) : ∃ a b, c = a * b ∧ 1 < a ∧ a < c ∧ 1 < b ∧ b < c := by
  rw [Nat.prime_iff, _root_.Prime] at hc
  push_neg at hc
  rw [Nat.isUnit_iff] at hc
  let ⟨a, b, h₁, h₂, h₃⟩ := hc (not_eq_zero_of_lt h) (Nat.ne_of_gt h)
  sorry

/- This should be earlier -/
theorem PartE (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_contra' h'
  let ⟨a, ha⟩ := exists_eq_succ_of_ne_zero $ h'.left
  let ⟨b, hb⟩ := exists_eq_succ_of_ne_zero $ h'.right
  rw [ha, hb, succ_mul, add_succ] at h
  exact succ_ne_zero _ h

theorem PartF (h : a * b = a) : a = 0 ∨ b = 1 := by
  match b with
  | zero => FIX ; left ; rw [←h, mul_zero]
  | succ b =>
      nth_rw 2 [←zero_add a] at h
      rw [one_eq_succ_zero, succ_inj']
      exact PartE (add_right_cancel h)

lemma PartG' (h : a ≤ 1) (h' : a ≠ 0) : a = 1 := Problem2.PartB h (zero_lt_of_ne_zero h')

theorem PartG (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have h' : a ≤ 1 ∧ b ≤ 1 := PartB h one_ne_zero
  have h'' : a ≠ 0 ∧ b ≠ 0 := by
    by_contra h
    rw [not_and_or, not_not, not_not] at h
    cases' h with ha hb
    · rw [ha, zero_mul] at h
      exact zero_ne_one h
    · rw [hb, mul_zero] at h
      exact zero_ne_one h
  exact ⟨PartG' h'.left h''.left, PartG' h'.right h''.right⟩

end Problem5