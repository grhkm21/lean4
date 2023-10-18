import Mathlib.Tactic

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
  let ⟨_, hdx⟩ := le.dest h1
  let ⟨_, hdy⟩ := le.dest h2
  rw [←hdy, ←hdx, add_assoc]
  apply Nat.le_add_right

theorem PartB (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  let ⟨u, hu⟩ := le.dest h1
  let ⟨v, hv⟩ := le.dest h2
  rw [←add_zero x, ←hu, add_assoc] at hv
  rw [←hu, Nat.eq_zero_of_add_eq_zero_right $ add_left_cancel hv, add_zero]

end Problem2

-------------------------------------------------------------------------------

namespace Problem3

theorem PartA : x < succ x := lt_of_succ_le $ le_refl _

theorem PartB : 0 < succ x := lt_of_succ_le $ succ_le_succ $ Nat.zero_le _

theorem PartC : ¬(x < 0) := not_succ_le_zero _

theorem PartD : (x < y → x ≤ y) ∧ (x = y → x ≤ y) := ⟨le_trans (le_succ _), le_of_eq⟩

theorem PartE : x ≤ y → (x < y ∨ x = y) := by
  intro h
  let ⟨z, hz⟩ := le.dest h
  cases' z with z hz
  FIX
  · right ; rw [←hz, add_zero]
  · left ; rw [←add_zero x, ←hz, add_succ]
    exact lt_of_succ_le $ succ_le_succ $ (Nat.add_le_add_iff_left x 0 z).mpr $ Nat.zero_le _

theorem PartF : ¬(x < x) :=
  match x with
  | 0 => not_succ_le_zero _
  | succ n => fun h => absurd (le_of_succ_le_succ h) (not_succ_le_self n)

end Problem3

-------------------------------------------------------------------------------

namespace Problem4

theorem Problem (hx : x ≠ 0) (h : a * x = b * x) : a = b := by
  let ⟨y, hy⟩ := exists_eq_succ_of_ne_zero hx
  rw [hy] at h
  induction' a with a ha generalizing b <;>
  induction' b with b hb <;> FIX <;> simp only [zero_mul, succ_mul] at h <;> try trivial
  rw [ha $ add_right_cancel h]

/- Alternative solution below -/
lemma le_or_le (x y : ℕ) : x ≤ y ∨ y ≤ x := by
  induction' x with x hx
  · left
    exact Nat.zero_le y
  · cases' hx with h h
    · let ⟨z, hz⟩ := le.dest h
      cases' z with z ; FIX
      · right
        rw [←hz, add_zero]
        exact le_succ x
      · left
        rw [←hz, add_succ, succ_eq_add_one, succ_eq_add_one, add_comm x z, add_assoc, add_comm z]
        exact le_add_right _ _
    · right
      exact le_trans h (le_succ x)

lemma eq_of_mul_eq_right_and_le (h : x ≠ 0) (h' : a * x = b * x) (hab : a ≤ b) : a = b := by
  let ⟨c, hc⟩ := le.dest hab
  rw [←hc, ←add_zero (a * x), add_mul] at h'
  have hcx : c = 0 ∨ x = 0 := Nat.mul_eq_zero.mp (add_left_cancel h'.symm)
  have hc' : c = 0 := (or_iff_not_imp_right.mp hcx) h
  rw [←hc, hc', add_zero]

lemma Problem' (h : x ≠ 0) (h' : a * x = b * x) : a = b := by
  cases' le_or_le a b with hab hab
  · exact eq_of_mul_eq_right_and_le h h' hab
  · exact (eq_of_mul_eq_right_and_le h h'.symm hab).symm

end Problem4

-------------------------------------------------------------------------------

namespace Problem5

theorem PartA (h : a * b = c) (h' : c ≠ 0) : a ≠ 0 ∧ b ≠ 0 := by
  by_contra h''
  cases' (not_and_or.mp h'') with hab hab
  <;> refine h' ?_
  <;> push_neg at hab
  <;> simp only [hab, zero_mul] at h
  <;> exact h.symm

lemma PartB' (h : a * b = c) (h' : c ≠ 0) : a ≤ c := by
  let ⟨_, hb⟩ := PartA h h'
  cases' b with b hb <;> try rw [zero_eq] at *
  · exfalso ; exact hb (refl 0)
  · rw [←h, mul_succ] ; apply Nat.le_add_left

theorem PartB (h : a * b = c) (h' : c ≠ 0) : a ≤ c ∧ b ≤ c :=
  ⟨PartB' h h', PartB' (Nat.mul_comm _ _ ▸ h) h'⟩

lemma PartC_lemma1 (h : 1 < a) : ∃ b, a = succ b := exists_eq_succ_of_ne_zero $ not_eq_zero_of_lt h

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

theorem PartC (h : a * b = c) (ha : 1 < a) (hb : 1 < b) : a < c ∧ b < c :=
  ⟨PartC' h ha hb, PartC' (Nat.mul_comm _ _ ▸ h) hb ha⟩

/- We have a different definition from Lean's -/
def OurPrime (n : ℕ) : Prop := 2 ≤ n ∧ ∀ k, k ∣ n → k = 1 ∨ k = n

theorem PartD (h : 1 < c) (hc : ¬OurPrime c) :
  ∃ a b, c = a * b ∧ 1 < a ∧ a < c ∧ 1 < b ∧ b < c :=
by
  rw [OurPrime] at hc
  push_neg at hc
  let ⟨k, ⟨⟨k', hk'⟩, hk, h''⟩⟩ := hc h
  have hk' := hk'.symm
  have hk1 : k ≠ 0 := fun ha => not_eq_zero_of_lt h $ (mul_eq_zero_of_left ha k' ▸ hk').symm
  have ⟨hk2, hk3⟩ := Problem5.PartB hk' $ not_eq_zero_of_lt h
  have hk4 : k' ≠ c := fun hkc => hk $ (mul_eq_right₀ $ not_eq_zero_of_lt h).mp $ hkc ▸ hk'
  refine ⟨k, k', ⟨hk'.symm, ?_, lt_of_le_of_ne hk2 h'', ?_, lt_of_le_of_ne hk3 hk4⟩⟩
  · iterate 2 cases' k with k <;> try trivial
    linarith
  · iterate 2 cases' k' with k' <;> try simp [←one_eq_succ_zero, h''] at hk' <;> try linarith
    linarith

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

example (h : ¬P → Q) : P ∨ Q := or_iff_not_imp_left.mpr h
example : ¬P → Q ↔ P ∨ Q := Iff.symm or_iff_not_imp_left

theorem PartG (h : a * b = 1) : a = 1 ∧ b = 1 := by
  have h' : a ≤ 1 ∧ b ≤ 1 := PartB h one_ne_zero
  have h'' : a ≠ 0 ∧ b ≠ 0 := by
    by_contra' hab
    cases' (or_iff_not_imp_left.mpr hab) with hab hab
    <;> try simp only [hab, zero_mul] at h
    <;> contradiction
  exact ⟨PartG' h'.left h''.left, PartG' h'.right h''.right⟩

end Problem5

-------------------------------------------------------------------------------

namespace Problem6

open Dvd

structure PartialOrder' (α : Type) (R : α → α → Prop) : Prop where
  rRefl : ∀ a : α, R a a
  rTrans : ∀ a b c : α, R a b → R b c → R a c
  rAntisymm : ∀ a b : α, R a b → R b a → a = b

structure TotalOrder' (α : Type) (R : α → α → Prop) extends PartialOrder' α R : Prop where
  rConn : ∀ a b : α, R a b ∨ R b a

theorem Problem : PartialOrder' ℕ dvd where
  rRefl := fun a => ⟨1, (mul_one a).symm⟩
  rTrans := fun a b c => by rintro ⟨d, rfl⟩ ⟨e, rfl⟩ ; exact ⟨d * e, by rw [mul_assoc]⟩
  rAntisymm := fun a b ⟨c, hc⟩ ⟨d, hd⟩ => by
    rw [hd, mul_assoc] at hc
    cases' (Problem5.PartF hc.symm) with hb hdc
    · rw [hd, hb, zero_mul]
    · rw [hd, (Problem5.PartG hdc).left, mul_one]

theorem notTotalOrder' : ¬TotalOrder' ℕ dvd := fun ⟨_, h⟩ => by specialize h 3 5 ; norm_num at h

end Problem6

-------------------------------------------------------------------------------

namespace Problem7

theorem Problem (h : a * d + b * c = a * c + b * d) : a = b ∨ c = d := by
  by_contra' hnq
  cases' hnq.left.lt_or_lt with h' h' <;> let ⟨e, he⟩ := le.dest (le_of_lt h')
  /- This proof is so bad... -/
  · rw [←he, add_mul, add_mul, ←add_assoc, ←add_assoc, add_comm (a * d), mul_comm e c, mul_comm e d] at h
    refine hnq.right $ Problem4.Problem ?_ $ add_left_cancel h
    by_contra' he'
    rw [he', add_zero] at he
    exact (Nat.ne_of_lt h') he
  · rw [←he, add_mul, add_mul, add_comm, add_assoc (b * c), add_comm (b * d), mul_comm e, mul_comm e] at h
    refine hnq.right.symm $ Problem4.Problem ?_ $ add_right_cancel $ add_left_cancel h
    by_contra' he'
    rw [he', add_zero] at he
    exact (Nat.ne_of_lt h') he

end Problem7
