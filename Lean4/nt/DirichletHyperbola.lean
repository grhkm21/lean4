import Mathlib.Tactic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.NumberTheory.ArithmeticFunction

open Nat BigOperators Finset ArithmeticFunction

variable [Ring α] (f g : ArithmeticFunction α)

section ForMathlib

theorem Finset.sum_union_inter' {s t : Finset α} {f : α → β} [Ring β] [DecidableEq α] :
    (∑ x in s ∪ t, f x) = (∑ x in s, f x) + (∑ x in t, f x) - (∑ x in s ∩ t, f x) := by
  rw [←sum_union_inter, add_sub_cancel]

lemma Nat.mul_lt_mul_of_lt_lt {a b c d : ℕ} (h : a < c) (h' : b < d) : a * b < c * d := by
  by_cases hb : b = 0
  · subst hb
    rw [mul_zero]
    exact Nat.mul_pos (zero_lt_of_lt h) h'
  · exact Nat.mul_lt_mul h (le_of_lt h') (Nat.pos_of_ne_zero hb)

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

lemma filter_or' {α : Type*} [DecidableEq α] {f p q : α → Prop}
    [DecidablePred f] [DecidablePred p] [DecidablePred q] (s : Finset α)
    (hf : ∀ a ∈ s, f a → p a ∨ q a) :
    s.filter f = s.filter (fun a ↦ f a ∧ p a) ∪ s.filter (fun a ↦ f a ∧ q a) := by
  ext a
  simp only [mem_filter, mem_union]
  constructor <;> intro h
  · specialize hf a h.left h.right ; tauto
  · tauto

end ForMathlib

section DirichletHyperbola

lemma aux1 (x : ℕ) :
    ∑ n in range x, (f * g) n
      = ∑ d in (Ico 1 x ×ˢ Ico 1 x).filter (fun d ↦ d.fst * d.snd < x), f d.fst * g d.snd := by
  simp_rw [mul_apply]
  rw [sum_congr rfl fun n h ↦ sum_congr (divisorsAntidiagonal_eq x $ mem_range.mp h) fun _ _ ↦ rfl]
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl (fun a _ ↦ ?_)
  simp only [sum_ite_eq, mem_range]

lemma aux2 {x U V : ℕ} (h : x = U * V) (h' : a * b ≤ x) : a ≤ U ∨ b ≤ V := by
  by_contra'
  subst h
  exact (lt_self_iff_false _).mp $ lt_of_le_of_lt h' $ mul_lt_mul_of_lt_lt this.left this.right

lemma aux2_real {x U V : ℝ} (h : x = U * V) (h' : a * b ≤ x) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    a ≤ U ∨ b ≤ V := by
  by_contra'
  subst h
  apply (lt_self_iff_false _).mp $ lt_of_le_of_lt h' ?_
  apply mul_lt_mul'' <;> tauto

lemma aux3 {x U V : ℕ} (h : x = U * V) :
    (Ico 1 (x + 1) ×ˢ Ico 1 (x + 1)).filter (fun d ↦ d.fst * d.snd ≤ x)
      = (Ico 1 (x + 1) ×ˢ Ico 1 (x + 1)).filter (fun d ↦ d.fst * d.snd ≤ x ∧ d.fst ≤ U)
      ∪ (Ico 1 (x + 1) ×ˢ Ico 1 (x + 1)).filter (fun d ↦ d.fst * d.snd ≤ x ∧ d.snd ≤ V) :=
  filter_or' _ (fun _ _ hf ↦ aux2 h hf)

lemma aux3_real {x U V : ℝ} (h : x = U * V) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    (Ico 1 (⌊x⌋₊ + 1) ×ˢ Ico 1 (⌊x⌋₊ + 1)).filter (fun d ↦ d.fst * d.snd ≤ x)
      = (Ico 1 (⌊x⌋₊ + 1) ×ˢ Ico 1 (⌊x⌋₊ + 1)).filter (fun d ↦ d.fst * d.snd ≤ x ∧ d.fst ≤ U)
      ∪ (Ico 1 (⌊x⌋₊ + 1) ×ˢ Ico 1 (⌊x⌋₊ + 1)).filter (fun d ↦ d.fst * d.snd ≤ x ∧ d.snd ≤ V) :=
  filter_or' _ (fun _ _ hf ↦ aux2_real h hf hU hV)

lemma aux4_real {a : ℕ} {x : ℝ} (f : ℕ → β) [Ring β] (h : 0 < a) :
    (∑ b in Ico 1 (⌊x⌋₊ + 1), if a * b ≤ x then f b else 0) = ∑ b in Ico 1 (⌊x⌋₊ / a + 1), f b := by
  by_cases hx : x < 0
  · simp only [floor_of_nonpos $ le_of_lt hx, Nat.zero_div, zero_add, Ico_self, sum_empty]
  push_neg at hx
  rw [←sum_filter]
  refine sum_congr ?_ (fun _ _ ↦ rfl)
  ext b
  simp only [mem_filter, mem_Ico, lt_succ]
  constructor <;> intro h'
  · constructor
    tauto
    refine (Nat.le_div_iff_mul_le' h).mpr (mul_comm a b ▸ le_floor ?_)
    rw [←cast_mul] at h'
    tauto
  · have : b ≤ ⌊x⌋₊ := le_trans h'.right $ Nat.div_le_self _ a
    have := le_trans (Nat.mul_le_mul_left a h'.right) (mul_div_le _ a)
    have := le_trans (cast_le.mpr this) (floor_le hx)
    rw [cast_mul] at this
    tauto

lemma aux4 {a : ℕ} (f : ℕ → β) [Ring β] (h : 0 < a) :
    (∑ b in Ico 1 (x + 1), if a * b ≤ x then f b else 0) = ∑ b in Ico 1 (x / a + 1), f b := by
  convert aux4_real f h (x := x) <;> simp only [←cast_mul, cast_le, floor_coe]

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
  rw [aux3 rfl, sum_union_inter']
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

theorem hyperbola_real {x : ℝ} (hx : x = U * V) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ∑ n in range (⌊x⌋₊ + 1), (f * g) n
      = ∑ a in Ico 1 (⌊U⌋₊ + 1), ∑ b in Ico 1 (⌊x / a⌋₊ + 1), f a * g b
      + ∑ b in Ico 1 (⌊V⌋₊ + 1), ∑ a in Ico 1 (⌊x / b⌋₊ + 1), f a * g b
      - ∑ a in Ico 1 (⌊U⌋₊ + 1), ∑ b in Ico 1 (⌊V⌋₊ + 1), f a * g b := by
  subst hx
  have hU₀ := zero_le_one.trans hU
  have hV₀ := zero_le_one.trans hV
  have hU' := le_mul_of_one_le_right (le_trans zero_le_one hU) hV
  have hV' := le_mul_of_one_le_left (le_trans zero_le_one hV) hU
  have hUV : 0 ≤ U * V := mul_zero (0 : ℝ) ▸ mul_le_mul hU₀ hV₀ (le_refl _) hU₀
  simp_rw [aux1, lt_succ_iff]
  simp_rw [show fun d : ℕ × ℕ ↦ d.1 * d.2 ≤ ⌊U * V⌋₊ = fun d ↦ d.1 * d.2 ≤ U * V by
    ext d ; rw [←cast_mul, le_floor_iff hUV]]
  rw [aux3_real rfl (zero_le_one.trans hU) (zero_le_one.trans hV), sum_union_inter']
  congr 1 ; congr 1
  · have :
        (Ico 1 (⌊U * V⌋₊ + 1) ×ˢ Ico 1 (⌊U * V⌋₊ + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V ∧ d.1 ≤ U)
        = (Ico 1 (⌊U⌋₊ + 1) ×ˢ Ico 1 (⌊U * V⌋₊ + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V) := by
      ext d
      simp only [mem_filter, mem_product, mem_Ico, lt_succ_iff, le_floor_iff hU₀, le_floor_iff hV₀,
        le_floor_iff hUV]
      constructor <;> intro h'
      · tauto
      · have : d.1 ≤ U * V := le_trans ?_ hU'
        all_goals tauto
    simp_rw [this, sum_filter, sum_product, floor_div_nat]
    refine sum_congr rfl fun a ha ↦ aux4_real _ (mem_Ico.mp ha).left
  · have :
        (Ico 1 (⌊U * V⌋₊ + 1) ×ˢ Ico 1 (⌊U * V⌋₊ + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V ∧ d.2 ≤ V)
        = (Ico 1 (⌊U * V⌋₊ + 1) ×ˢ Ico 1 (⌊V⌋₊ + 1)).filter (fun d ↦ d.1 * d.2 ≤ U * V) := by
      ext d
      simp only [mem_filter, mem_product, mem_Ico, lt_succ_iff, le_floor_iff hU₀, le_floor_iff hV₀,
        le_floor_iff hUV]
      constructor <;> intro h'
      · tauto
      · have : d.2 ≤ U * V := le_trans ?_ hV'
        all_goals tauto
    simp_rw [this, sum_filter, sum_product_right, floor_div_nat, mul_comm]
    refine sum_congr rfl fun a ha ↦ aux4_real _ (mem_Ico.mp ha).left
  · rw [←filter_and, ←sum_product']
    congr
    ext a
    simp only [mem_product, mem_Ico, mem_filter, lt_succ, le_floor_iff hU₀, le_floor_iff hV₀,
      le_floor_iff hUV]
    constructor <;> intro h
    · tauto
    · have : a.1 ≤ U * V := le_trans ?_ hU'
      have : a.2 ≤ U * V := le_trans ?_ hV'
      have : a.1 * a.2 ≤ U * V :=
        mul_le_mul ?_ ?_ (zero_le_one.trans $ one_le_cast.mpr ?_) (zero_le_one.trans ?_)
      all_goals tauto

/- Starting with 0 and using `range` instead of `Ico` -/
theorem hyperbola_real' {x : ℝ} (hx : x = U * V) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ∑ n in range (⌊x⌋₊ + 1), (f * g) n
      = ∑ a in range (⌊U⌋₊ + 1), ∑ b in range (⌊x / a⌋₊ + 1), f a * g b
      + ∑ b in range (⌊V⌋₊ + 1), ∑ a in range (⌊x / b⌋₊ + 1), f a * g b
      - ∑ a in range (⌊U⌋₊ + 1), ∑ b in range (⌊V⌋₊ + 1), f a * g b := by
  rw [hyperbola_real _ _ hx hU hV]
  simp only [range_eq_Ico, sum_eq_sum_Ico_succ_bot (succ_pos _), cast_zero, div_zero, floor_zero,
    f.map_zero, g.map_zero, zero_mul, mul_zero, zero_add, sum_const_zero]

end DirichletHyperbola
