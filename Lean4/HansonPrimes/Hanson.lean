import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Pointwise.Interval
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

theorem Order.Iio_succ_eq_insert'
    {α : Type*} [PartialOrder α] [SuccOrder α] [LocallyFiniteOrderBot α]
    [DecidableEq α] [NoMaxOrder α] (a : α) : Finset.Iio (succ a) = insert a (Finset.Iio a) := by
  ext a
  simp

theorem Order.Iio_succ'
    {α : Type*} [PartialOrder α] [SuccOrder α] [LocallyFiniteOrderBot α]
    [DecidableEq α] [NoMaxOrder α] (a : α) : Finset.Iio (succ a) = Finset.Iic a := by
  ext a
  simp

theorem Order.Iic_pred'
    {α : Type*} [PartialOrder α] [PredOrder α] [LocallyFiniteOrderBot α]
    [DecidableEq α] [NoMinOrder α] (a : α) : Finset.Iic (pred a) = Finset.Iio a := by
  ext a
  simp

theorem Nat.Iio_zero : Finset.Iio 0 = ∅ := rfl

theorem Nat.Iic_zero : Finset.Iic 0 = {0} := rfl

theorem Nat.Iio_succ_eq_insert' {a : ℕ} : Finset.Iio a.succ = insert a (Finset.Iio a) :=
  Order.Iio_succ_eq_insert' _

theorem Nat.Iio_succ {a : ℕ} : Finset.Iio a.succ = Finset.Iic a :=
  Order.Iio_succ' _

theorem Nat.Iic_pred {a : ℕ} (hn : 0 < a) : Finset.Iic a.pred = Finset.Iio a := by
  ext
  simp
  omega

/- I can't find this in Mathlib -/
theorem Fin.prod_univ_eq_prod_Iio {α : Type*} [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ x : Fin n, f x = ∏ x < n, f x :=
  match n with
  | 0 => by rfl
  | Nat.succ n => by
    rw [Fin.prod_univ_castSucc, Nat.Iio_succ_eq_insert', Finset.prod_insert Finset.not_mem_Iio_self,
      Fin.val_last, mul_comm, ← Fin.prod_univ_eq_prod_Iio]
    rfl

theorem Fin.prod_univ_succ_eq_prod_Iic {α : Type*} [CommMonoid α] (f : ℕ → α) (n : ℕ) :
    ∏ x : Fin n.succ, f x = ∏ x ≤ n, f x :=
  prod_univ_eq_prod_Iio _ _

theorem Int.div_mul_pos_le_self (a b : ℤ) (hb : 0 < b) : a / b * b ≤ a := by
  rw [← Int.sub_nonneg]
  convert @Int.emod_nonneg a b (by exact_mod_cast hb.ne.symm) using 1
  linarith [Int.ediv_add_emod' a b]

theorem Real.floor_div_floor {x : ℝ} (m : ℕ) : ⌊(⌊x⌋ : ℝ) / m⌋ = ⌊x / m⌋ := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm : 0 < (m : ℝ) := by norm_cast; omega
    apply eq_of_forall_le_iff
    intro c
    simp only [Int.le_floor, le_div_iff hm]
    constructor <;> intro hc
    · exact hc.trans (Int.floor_le x)
    · norm_cast
      simpa [Int.le_floor] using hc

theorem Rat.floor_div_floor {x : ℚ} (m : ℕ) : ⌊(⌊x⌋ : ℚ) / m⌋ = ⌊x / m⌋ := by
  by_cases hm : m = 0
  · simp [hm]
  · have hm : 0 < (m : ℚ) := by norm_cast; omega
    apply eq_of_forall_le_iff
    intro c
    simp only [Int.le_floor, le_div_iff hm]
    constructor <;> intro hc
    · exact hc.trans (Int.floor_le x)
    · norm_cast
      simpa [Int.le_floor] using hc

/- Reference: "On the product of the primes" by Denis Hanson (1972) -/

open scoped Nat
open BigOperators Int Fin Finset GCDMonoid

lemma lemma_1
    {k : ℕ} {a : Fin k.succ → ℕ} (ha_pos : ∀ i, 0 < a i) (ha_sum : ∑ i, 1 / (a i : ℝ) ≤ 1)
    (x : ℝ) (hx₁ : 1 ≤ x) (hx₂ : x < a k) :
    ∑ i, ⌊x / a i⌋ < ⌊x⌋ := (cast_lt (R := ℝ)).mp <| calc
  ((∑ i : Fin k.succ, ⌊x / a i⌋ : ℤ) : ℝ) = ∑ i : Fin k, ⌊x / a i.castSucc⌋ := by
    rw_mod_cast [sum_univ_castSucc, ← natCast_eq_last]
    simp only [add_right_eq_self, floor_eq_zero_iff, Set.mem_Ico]
    exact ⟨by positivity, (div_lt_iff (by simpa using ha_pos k)).mpr <| by simpa using hx₂⟩
  _ = ∑ i : Fin k, ⌊(⌊x⌋ : ℝ) / a i.castSucc⌋ := by
    exact_mod_cast sum_congr rfl fun i _ ↦ (Real.floor_div_floor _).symm
  _ ≤ ∑ i : Fin k, (⌊x⌋ : ℝ) / a i.castSucc := by
    simp [cast_sum, sum_le_sum, floor_le]
  _ = (⌊x⌋ : ℝ) * ∑ i : Fin k, 1 / (a i.castSucc : ℝ) := by
    simp [-one_div, mul_sum, sum_congr, mul_one_div]
  _ ≤ (⌊x⌋ : ℝ) * (1 - 1 / (a (last k) : ℝ)) := by
    gcongr
    rwa [le_sub_iff_add_le, ← sum_univ_castSucc fun i ↦ 1 / (a i : ℝ)]
  _ < ⌊x⌋ := by
    rw [mul_lt_iff_lt_one_right (by exact_mod_cast Int.floor_pos.mpr hx₁)]
    have ha_pos' : (0 : ℝ) < a (last k) := by exact_mod_cast ha_pos _
    linarith [one_div_pos.mpr ha_pos']

section Definition

def a : ℕ → ℕ
| 0 => 1
| Nat.succ n => ∏ k : Fin n.succ, a k + 1

@[simp] lemma a_zero : a 0 = 1 := by rfl
@[simp] lemma a_one : a 1 = 2 := by rfl
@[simp] lemma a_two : a 2 = 3 := by rfl
@[simp] lemma a_three : a 3 = 7 := by rfl
@[simp] lemma a_four : a 4 = 43 := by rfl

lemma a_succ (n : ℕ) : a n.succ = ∏ k : Fin n.succ, a k + 1 := by
  rw [a]

lemma a_succ' (n : ℕ) : a n.succ = ∏ k ≤ n, a k + 1 := by
  rw [a_succ, Fin.prod_univ_succ_eq_prod_Iic]

lemma a_pos (n : ℕ) : 0 < a n := by
  cases' n <;> simp [a_zero, a_succ]

lemma one_lt_a (n : ℕ) (hn : 0 < n) : 1 < a n := by
  cases' n with n n
  · omega
  · simp [a_succ', a_pos]

lemma a_rec (n : ℕ) : a n.succ.succ = a n.succ ^ 2 - a n.succ + 1 := by
  have h_prod := (tsub_eq_iff_eq_add_of_le (by simpa using a_pos _)).mpr <| a_succ' n
  rw [a_succ', ← mul_prod_Iio_eq_prod_Iic, Nat.Iio_succ, ← h_prod, mul_tsub, mul_one, sq]

lemma a_rec_pos (n : ℕ) (hn : 0 < n) : a n.succ = a n ^ 2 - a n + 1 := by
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne.symm
  exact a_rec _

lemma self_le_a (n : ℕ) : n ≤ a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [a_succ', ← mul_prod_Iio_eq_prod_Iic]
    apply add_le_add_right <| le_mul_of_le_of_one_le ih <| prod_pos fun _ _ ↦ a_pos _

theorem asdf (n : ℕ) : ∑ i ≤ n, 1 / (a i : ℝ) = 2 - 1 / (a n.succ - 1) := by
  rw [eq_sub_iff_add_eq]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Iic_succ]

theorem a_bound {n : ℕ} : ∑ i ∈ Ico 1 n, 1 / (a i : ℝ) < 1 := by
  sorry

end Definition

theorem lcm_lt_three_pow (n : ℕ) : lcm (Icc 1 n) id < 3 ^ n := by
  sorry
