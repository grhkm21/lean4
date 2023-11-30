import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction

open Nat BigOperators Finset ArithmeticFunction

variable [Ring α] (f g : ArithmeticFunction α)

theorem Finset.sum_union_inter' {s t : Finset α} {f : α → β} [Ring β] [DecidableEq α] :
    (∑ x in s ∪ t, f x) = (∑ x in s, f x) + (∑ x in t, f x) - (∑ x in s ∩ t, f x) := by
  rw [←sum_union_inter, add_sub_cancel]

example (s : Finset ℕ) :
    ∑ d in s.filter (fun d ↦ d < x), f d =
      ∑ a in range x, ∑ d in filter (fun d ↦ d = a) s, f d := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl (fun a _ ↦ ?_)
  simp_rw [sum_ite_eq, mem_range]

/- divisorsAntidiagonal with arbitrary bounds -/
theorem divisorsAntidiagonal_eq (N : ℕ) (hN : n < N) :
    divisorsAntidiagonal n = filter (fun d ↦ d.fst * d.snd = n) (Ico 1 N ×ˢ Ico 1 N) := by
  rw [divisorsAntidiagonal]
  ext ⟨a, b⟩
  simp only [add_le_iff_nonpos_left, mem_product, mem_Ico, mem_filter, and_congr_left_iff]
  intro h
  simp_rw [lt_succ_iff]
  constructor <;> intro h'
  · have : a < N := lt_of_le_of_lt (by tauto) hN
    have : b < N := lt_of_le_of_lt (by tauto) hN
    tauto
  · have hn : 1 ≤ n := by rw [←h, ←mul_one 1] ; apply Nat.mul_le_mul <;> tauto
    have := le_of_dvd hn (Dvd.intro b h)
    have := le_of_dvd hn (Dvd.intro_left a h)
    tauto

lemma aux1 (x : ℕ) :
    ∑ n in range x, (f * g) n
      = ∑ d in (Ico 1 x ×ˢ Ico 1 x).filter (fun d ↦ d.fst * d.snd < x), f d.fst * g d.snd := by
  simp_rw [mul_apply]
  rw [sum_congr rfl fun n h ↦ sum_congr (divisorsAntidiagonal_eq x $ mem_range.mp h) fun _ _ ↦ rfl]
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl (fun a _ ↦ ?_)
  simp only [sum_ite_eq, mem_range]

lemma mul_lt_mul_of_lt_lt {a b c d : ℕ} (h : a < b) (h' : c < d) : a * c < b * d := by
  by_cases hc : c = 0
  · subst hc
    rw [mul_zero]
    exact Nat.mul_pos (zero_lt_of_lt h) h'
  · exact Nat.mul_lt_mul h (le_of_lt h') (Nat.pos_of_ne_zero hc)

lemma aux2 {x U V : ℕ} (h : x = U * V) (h' : a * b ≤ x) : a ≤ U ∨ b ≤ V := by
  by_contra'
  subst h
  exact (lt_self_iff_false _).mp $ lt_of_le_of_lt h' $ mul_lt_mul_of_lt_lt this.left this.right

lemma aux3 {x U V : ℕ} (h : x = U * V) :
    (Ico 1 (x + 1) ×ˢ Ico 1 (x + 1)).filter (fun d ↦ d.fst * d.snd ≤ x)
      = (Ico 1 (x + 1) ×ˢ Ico 1 (x + 1)).filter (fun d ↦ d.fst * d.snd ≤ x ∧ d.fst ≤ U)
      ∪ (Ico 1 (x + 1) ×ˢ Ico 1 (x + 1)).filter (fun d ↦ d.fst * d.snd ≤ x ∧ d.snd ≤ V) := by
  ext d
  simp only [mem_filter, mem_union]
  constructor <;> intro h'
  · simp only [h', true_and, aux2 h h'.right]
  · cases' h' <;> tauto

lemma aux3' {U V : ℕ} :
    (Ico 1 (U * V + 1) ×ˢ Ico 1 (U * V + 1)).filter (fun d ↦ d.fst * d.snd ≤ U * V)
      = (Ico 1 (U * V + 1) ×ˢ Ico 1 (U * V + 1)).filter (fun d ↦ d.fst * d.snd ≤ U * V ∧ d.fst ≤ U)
      ∪ (Ico 1 (U * V + 1) ×ˢ Ico 1 (U * V + 1)).filter
        (fun d ↦ d.fst * d.snd ≤ U * V ∧ d.snd ≤ V) := by
    set x := U * V with hx
    exact aux3 hx

lemma aux4 {a : ℕ} (f : ℕ → β) [Ring β] (h : 0 < a) :
    (∑ b in Ico 1 (x + 1), if a * b ≤ x then f b else 0) = ∑ b in Ico 1 (x / a + 1), f b := by
  rw [←sum_filter]
  refine sum_congr ?_ (fun _ _ ↦ rfl)
  ext b
  simp only [mem_filter, mem_Ico, lt_succ]
  constructor <;> intro h'
  · constructor
    tauto
    exact (Nat.le_div_iff_mul_le' h).mpr (mul_comm a b ▸ h'.right)
  · have : b ≤ x := le_trans h'.right $ Nat.div_le_self x a
    have : a * b ≤ x := le_trans (Nat.mul_le_mul_left a h'.right) (mul_div_le x a)
    tauto

theorem hyperbola {U V : ℕ} (hx : x = U * V) :
    ∑ n in range (x + 1), (f * g) n
      = ∑ a in Ico 1 (U + 1), ∑ b in Ico 1 (x / a + 1), f a * g b
      + ∑ b in Ico 1 (V + 1), ∑ a in Ico 1 (x / b + 1), f a * g b
      - ∑ a in Ico 1 (U + 1), ∑ b in Ico 1 (V + 1), f a * g b := by
  subst hx
  by_cases hU : U = 0
  · subst hU ; simp
  by_cases hV : V = 0
  · subst hV ; simp
  have hU' := @Nat.le_mul_of_pos_right U _ $ Nat.pos_of_ne_zero hV
  have hV' := @Nat.le_mul_of_pos_left V _ $ Nat.pos_of_ne_zero hU
  simp_rw [aux1, lt_succ_iff]
  rw [aux3', sum_union_inter']
  congr 1 ; congr 1
  · have : (Ico 1 (U * V + 1) ×ˢ Ico 1 (U * V + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V ∧ d.1 ≤ U)
        = (Ico 1 (U + 1) ×ˢ Ico 1 (U * V + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V) := by
      ext d
      simp only [mem_filter, mem_product, mem_Ico, lt_succ_iff]
      constructor <;> intro h'
      · tauto
      · have : d.1 ≤ U * V := le_trans ?_ hU'
        all_goals tauto
    rw [this, sum_filter, sum_product]
    refine sum_congr rfl (fun a ha ↦ ?_)
    exact aux4 _ (mem_Ico.mp ha).left
  · have : (Ico 1 (U * V + 1) ×ˢ Ico 1 (U * V + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V ∧ d.2 ≤ V)
        = (Ico 1 (U * V + 1) ×ˢ Ico 1 (V + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V) := by
      ext d
      simp only [mem_filter, mem_product, mem_Ico, lt_succ_iff]
      constructor <;> intro h'
      · tauto
      · have : d.2 ≤ U * V := le_trans ?_ hV'
        all_goals tauto
    rw [this, sum_filter, sum_product_right]
    refine sum_congr rfl (fun a ha ↦ ?_)
    simp only [mul_comm, aux4 _ (mem_Ico.mp ha).left]
  · save
    rw [←filter_and, ←sum_product']
    congr
    ext a
    simp only [mem_product, mem_Ico, mem_filter, lt_succ]
    constructor <;> intro h
    · tauto
    · have : a.1 ≤ U * V := le_trans ?_ hU'
      have : a.2 ≤ U * V := le_trans ?_ hV'
      have : a.1 * a.2 ≤ U * V := Nat.mul_le_mul ?_ ?_
      all_goals tauto
