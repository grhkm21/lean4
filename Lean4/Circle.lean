import Mathlib.Algebra.Group.Subgroup.ZPowers
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.GroupTheory.Coset
import Mathlib.Init.Classical
import Mathlib.Topology.Covering
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.UnitInterval

open Int hiding mem_zmultiples_iff
open Topology Metric Set Filter AddSubgroup Complex AddCircle Pointwise

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem Continuous.subtype_iff (f : X → Y) {p : Y → Prop} (hp : ∀ x, p (f x)) :
    Continuous f ↔ Continuous (fun x ↦ (⟨f x, hp x⟩ : { x // p x })) :=
  ⟨fun a ↦ subtype_mk a hp, continuous_subtype_val.comp⟩

#check Subtype.map
#check Subtype

theorem IsOpen.subtype (s : Set X) {p : X → Prop} (hs : IsOpen s) :
    IsOpen (Subtype.val (p := p) ⁻¹' s) :=
  isOpen_induced hs

theorem isOpen_iff_isClosed_compl {s : Set X} : IsOpen s ↔ IsClosed sᶜ :=
  /- This doesn't work: compl_compl s ▸ isOpen_compl_iff -/
  (congrArg _ $ compl_compl s).symm.to_iff.trans isOpen_compl_iff

theorem circle_eq : (circle : Set ℂ) = univ \ (ball 0 1) ∩ closedBall 0 1 := by
  ext a
  simp
  rw [le_antisymm_iff, and_comm]

theorem isClosed_circle : IsClosed (circle : Set ℂ) :=
  circle_eq ▸ (compl_eq_univ_diff _ ▸ isOpen_iff_isClosed_compl.mp isOpen_ball).inter isClosed_ball

@[simp] theorem expMapCircle_int_mul_two_pi {k : ℤ} : expMapCircle (k * (2 * Real.pi)) = 1 := by
  simpa using periodic_expMapCircle.int_mul_eq k


theorem fract_mem_Ico {x : ℝ} : fract x ∈ Ico 0 1 :=
  mem_Ico.mpr ⟨fract_nonneg _, fract_lt_one _⟩

noncomputable def trivial_thing1 {a : ℝ} (ha : 0 < a) : ℝ ≃ Ico 0 a × zmultiples a where
  toFun := fun x ↦ by
    refine ⟨⟨a * fract (x / a), ?_⟩, ⟨x - a * fract (x / a), ?_⟩⟩
    · have : fract (x / a) ∈ Ico 0 1 := fract_mem_Ico
      rw [mem_Ico] at *
      constructor
      · exact (mul_nonneg_iff_of_pos_left ha).mpr this.left
      · exact mul_lt_of_lt_one_right ha this.right
    · rw [fract, mul_sub, ← sub_add, mul_div_cancel₀ _ ha.ne.symm, sub_self, zero_add,
        mem_zmultiples_iff]
      use ⌊x / a⌋, by simp [mul_comm]
  invFun := fun x ↦ x.fst + x.snd
  left_inv := fun x ↦ by simp
  right_inv := fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ by
    obtain ⟨k, rfl⟩ := mem_zmultiples_iff.mp hy
    have h₁ : 0 ≤ x / a ∧ x / a < 1 := by
      rw [mem_Ico] at hx
      exact ⟨div_nonneg hx.left ha.le, (div_lt_one ha).mpr hx.right⟩
    have h₂ : fract ((x + k * a) / a) = x / a := by
      rw [add_div, mul_div_cancel_right₀ _ ha.ne.symm, fract_add_int,
        fract_eq_self.mpr ⟨h₁.left, h₁.right⟩]
    simp [h₂]
    constructor
    · exact mul_div_cancel₀ _ ha.ne.symm
    · rw [mul_div_cancel₀ _ ha.ne.symm, add_sub_cancel_left]

theorem zmultiples_eq_iUnion (r : ℝ) : zmultiples r = ⋃ n : ℤ, {n * r} := by
  ext; simp [mem_zmultiples_iff]

theorem real_eq_iUnion (r : ℝ) (hr : 0 < r) :
    (univ : Set ℝ) = ⋃ n : ℤ, Ico (n * r : ℝ) (n * r + r) := by
  ext x
  simp
  rw [← div_mul_cancel₀ x hr.ne.symm]
  use ⌊x / r⌋, (by gcongr; apply floor_le), (by rw [← add_one_mul]; gcongr; apply lt_floor_add_one)

theorem zmultiples_compl_eq_iUnion (r : ℝ) (hr : 0 < r) :
    (zmultiples r : Set ℝ)ᶜ = ⋃ n : ℤ, Ioo (n * r : ℝ) (n * r + r) := by
  have (n : ℤ) : Ico (n * r) (n * r + r) ∩ (zmultiples r) = {n * r} := by
    ext x
    simp [mem_zmultiples_iff]
    constructor <;> intro h
    · rcases h with ⟨h₁, k, rfl⟩
      have : (n : ℝ) ≤ k := (mul_le_mul_right hr).mp h₁.left
      have : (k : ℝ) < n + 1 := by
        rw [← add_one_mul] at h₁
        simpa using (mul_lt_mul_right hr).mp h₁.right
      norm_cast at *
      rw [show k = n by omega]
    · subst h; simp [hr]
  rw [compl_eq_univ_diff, real_eq_iUnion r hr, iUnion_diff]
  congr! with n
  rw [← diff_self_inter, this, Ico_diff_left]

theorem isOpen_zmultiples_pos_compl {r : ℝ} (hr : 0 < r) :
    IsOpen ((zmultiples r)ᶜ : Set ℝ) := by
  simp [zmultiples_compl_eq_iUnion _ hr, isOpen_iUnion, isOpen_Ioo]

theorem isOpen_zmultiples_coset {r t : ℝ} (hr : 0 < r) :
    IsOpen ((univ : Set ℝ) \ (t +ᵥ (zmultiples r : Set ℝ))) := by
  rw [← compl_eq_univ_diff, ← vadd_set_compl]
  exact isOpenMap_vadd _ _ $ isOpen_zmultiples_pos_compl hr

theorem expMapCircle_arg' {c : ℂ} (hc : ‖c‖ = 1) : expMapCircle c.arg = c := by
  nth_rw 1 [show c = (⟨c, mem_circle_iff_abs.mpr hc⟩ : circle) by rfl, expMapCircle_arg]

theorem expMapCircle_preimage (c : circle) :
    expMapCircle ⁻¹' {c} = arg c +ᵥ (zmultiples (2 * Real.pi) : Set ℝ) := by
  ext x
  simp [mem_leftAddCoset_iff, mem_zmultiples_iff]
  constructor <;> intro h
  · rw [← expMapCircle_arg c, expMapCircle_eq_expMapCircle] at h
    obtain ⟨k, rfl⟩ := h
    use k, by simp
  · obtain ⟨k, hk⟩ := h
    rw [neg_add_eq_sub, eq_sub_iff_add_eq, eq_comm] at hk
    simp [hk]

theorem expMapCircle_preimage' (s : Set circle) :
    expMapCircle ⁻¹' s = arg '' s +ᵥ (zmultiples (2 * Real.pi) : Set ℝ) := by
  ext x
  simp [-vadd_eq_add, Set.mem_vadd, mem_zmultiples_iff]
  constructor <;> intro h
  · simp_rw [vadd_eq_add]
    use expMapCircle x
    constructor
    · simpa using h
    · obtain ⟨m, hm⟩ := expMapCircle_eq_expMapCircle.mp $ expMapCircle_arg (expMapCircle x)
      use -m
      rw [hm, add_assoc, ← add_mul, ← cast_add, add_neg_self, cast_zero, zero_mul, add_zero]
  · obtain ⟨k, ⟨⟨ha₁, ha₂⟩, ⟨b, ⟨⟨b, rfl⟩, rfl⟩⟩⟩⟩ := h
    rw [vadd_eq_add, periodic_expMapCircle.int_mul]
    convert ha₂
    rw [expMapCircle_arg' ha₁]

noncomputable def asdf0 : ℝ ≃ Ico (0 : ℝ) 1 × zmultiples (1 : ℝ) where
  toFun := fun x ↦ ⟨⟨fract x, fract_mem_Ico⟩, ⟨⌊x⌋, intCast_mem_zmultiples_one _⟩⟩
  invFun := fun ⟨x, y⟩ ↦ x.val + y.val
  left_inv := fun x ↦ by simp
  right_inv := fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ by
    obtain ⟨y', hy'⟩ := mem_zmultiples_iff.mpr hy
    simp at hx hy' ⊢
    subst hy'
    simpa

def asdf1 : Ico (0 : ℝ) 1 ≃ Ioc (0 : ℝ) 1 :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨1 - x, by simp at hx ⊢; tauto⟩, fun ⟨x, hx⟩ ↦ ⟨1 - x, by simp at hx ⊢; tauto⟩,
   fun ⟨x, hx⟩ ↦ by simp, fun ⟨x, hx⟩ ↦ by simp⟩

noncomputable def asdf2 (r : ℝ) (hr : r ≠ 0) : zmultiples (1 : ℝ) ≃ zmultiples r :=
  ⟨fun ⟨x, hx⟩ ↦ ⟨x * r, by simpa [mem_zmultiples_iff, hr] using hx⟩,
   fun ⟨x, hx⟩ ↦ ⟨x / r, by simpa [mem_zmultiples_iff, hr, eq_div_iff_mul_eq hr] using hx⟩,
   fun ⟨x, hx⟩ ↦ by simp [mul_div_cancel_right₀ _ hr],
   fun ⟨x, hx⟩ ↦ by simp [div_mul_cancel₀ _ hr]⟩

noncomputable def asdf0 : ℝ ≃ Ico (0 : ℝ) 1 × zmultiples (1 : ℝ) where
