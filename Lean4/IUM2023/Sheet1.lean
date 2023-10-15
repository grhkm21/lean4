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
  induction' x with x hx generalizing y <;>
  induction' y with y hy <;> intro h <;> FIX
  · trivial
  · exact Or.inl $ zero_lt_succ _
  · exfalso ; exact not_succ_le_zero _ h
  · rw [succ_eq_add_one, succ_eq_add_one] at h
    cases' hx $ le_of_lt_succ h with h' h'
    · left ; exact lt_succ_of_le h'
    · right ; rw [h']

theorem PartF : ¬(x < x) := not_succ_le_self _

end Problem3

-------------------------------------------------------------------------------

namespace Problem4

theorem Problem (hx : x ≠ 0) (h : a * x = b * x) : a = b := by
  let ⟨y, hy⟩ := exists_eq_succ_of_ne_zero hx
  rw [hy] at h
  induction' a with a ha generalizing b <;>
  induction' b with b hb <;> FIX
  · trivial
  · rw [zero_mul] at h ; trivial
  · rw [zero_mul] at h ; trivial
  · rw [succ_mul, succ_mul] at h ; rw [ha $ add_right_cancel h]

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

/- We have a different definition from Lean's -/
def OurPrime (n : ℕ) : Prop := 2 ≤ n ∧ ∀ k, k ∣ n → k = 1 ∨ k = n

theorem PartD (h : 1 < c) (hc : ¬OurPrime c) : ∃ a b, c = a * b ∧ 1 < a ∧ a < c ∧ 1 < b ∧ b < c := by
  rw [OurPrime] at hc
  push_neg at hc
  have ⟨k, ⟨⟨k', hk'⟩, hk, h''⟩⟩ := hc h
  refine ⟨k, k', ⟨hk', ?_, ?_, ?_, ?_⟩⟩
  · match k with
    | 0 => exfalso ; rw [zero_mul] at hk' ; exact h'' hk'.symm
    | 1 => exfalso ; trivial
    | succ (succ k) => exact one_lt_succ_succ k
  · have h' := Problem3.PartE $ And.left $ Problem5.PartB hk'.symm (not_eq_zero_of_lt h)
    rw [←@not_not (k = c)] at h'
    exact imp_iff_not_or.mpr h'.symm h''
  · match k' with
    | 0 => exfalso ; rw [hk', mul_zero] at h ; exact not_succ_le_zero 1 h
    | 1 => exfalso ; rw [hk', mul_one] at h'' ; trivial
    | succ (succ k') => exact one_lt_succ_succ k'
  · have h' := Problem3.PartE $ And.right $ Problem5.PartB hk'.symm (not_eq_zero_of_lt h)
    rw [←@not_not (k' = c)] at h'
    have h'' : k' ≠ c := by
      by_contra' h''
      rw [h''] at hk'
      exact hk $ (mul_eq_right₀ $ not_eq_zero_of_lt h).mp hk'.symm
    refine imp_iff_not_or.mpr h'.symm h''

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
