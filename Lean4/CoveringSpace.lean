import Mathlib.Algebra.Group.Subgroup.ZPowers
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Init.Classical
import Mathlib.Topology.Covering
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homotopy.HomotopyGroup

open Complex hiding I
open Int Topology Metric Set Filter AddSubgroup

variable {E X : Type*} [TopologicalSpace X] [TopologicalSpace E]
variable (a : Type*) {b : Type*}

/- instance {f : α → β} {x : α} {y : β} [Decidable (f x = y)] : Decidable (x ∈ f⁻¹' {y}) := by -/
/-   rw [Set.mem_preimage, Set.mem_singleton_iff] -/
/-   infer_instance -/

theorem thing : expMapCircle ⁻¹' {1} = (fun t : ℤ ↦ t * (2 * Real.pi)) '' univ := by
  ext t
  constructor <;> intro h <;> simp_all
  · simp_rw [← expMapCircle_zero, expMapCircle_eq_expMapCircle, zero_add] at h
    simp only [eq_comm, h]
  · obtain ⟨y, rfl⟩ := h
    simp [expMapCircle, mul_assoc (y : ℂ)]

noncomputable def EquivThing : ℝ ≃ Ico (0 : ℝ) 1 × ℤ where
  toFun := fun r ↦ ⟨⟨fract r, mem_Ico.mpr ⟨fract_nonneg _, fract_lt_one _⟩⟩, ⌊r⌋⟩
  invFun := fun ⟨⟨f, _⟩, a⟩ ↦ a + f
  left_inv := fun r ↦ by simp
  right_inv := fun ⟨⟨f, hf⟩, a⟩ ↦ by simp [mem_Ico.mp hf]

noncomputable def EquivThingAgain : Ico (0 : ℝ) 1 ≃ UnitAddCircle := by
  convert (AddCircle.equivIco (1 : ℝ) (0 : ℝ)).symm
  rw [zero_add]

theorem fract_mem_Ico {x : ℝ} : fract x ∈ Ico 0 1 :=
  mem_Ico.mpr ⟨fract_nonneg _, fract_lt_one _⟩

theorem mul_fract_div_mem_Ico {x a : ℝ} (ha : 0 < a) : a * fract (x / a) ∈ Ico 0 a := by
  have := fract_mem_Ico (x := x / a)
  rw [mem_Ico] at *
  constructor
  · exact (mul_nonneg_iff_of_pos_left ha).mpr this.left
  · exact mul_lt_of_lt_one_right ha this.right

theorem sub_mul_fract_mem_zmultiples {x a : ℝ} (ha : a ≠ 0) :
    x - a * fract (x / a) ∈ zmultiples a := by
  rw [fract, mul_sub, ← sub_add, mul_div_cancel₀ _ ha, sub_self, zero_add,
    AddSubgroup.mem_zmultiples_iff]
  use ⌊x / a⌋, by simp [mul_comm]

noncomputable def trivial_thing1 {a : ℝ} (ha : 0 < a) : ℝ ≃ Ico 0 a × zmultiples a where
  toFun := fun x ↦
    ⟨⟨a * fract (x / a), mul_fract_div_mem_Ico ha⟩,
      ⟨x - a * fract (x / a), sub_mul_fract_mem_zmultiples ha.ne.symm⟩⟩
  invFun := fun x ↦ x.fst + x.snd
  left_inv := fun x ↦ by simp
  right_inv := fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ by
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
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

#check Real.instLE
#check expMapCircle
noncomputable def trivial_thing2 {p : ℝ} (hp : 0 < p) : ℝ ≃ ↥circle × (zmultiples p) := by
  refine (trivial_thing1 hp).trans $ Equiv.prodCongrLeft fun _ ↦ ?_
  have := circle.argEquiv
  have := Ioc_equiv_Ico

/-
  ⟨⟨a * fract (x / a), mul_fract_div_mem_Ico ha⟩,
    ⟨x - a * fract (x / a), sub_mul_fract_mem_zmultiples ha.ne.symm⟩⟩
-/

noncomputable def trivial_thing3 : PartialHomeomorph ℝ (↥circle × (zmultiples (2 * Real.pi))) := by
  /- refine Homeomorph.toPartialHomeomorph $ Homeomorph.mk ?_ ?_ ?_ -/
  /- · refine (trivial_thing1 (by positivity)).trans $ Equiv.prodCongrLeft fun _ ↦ ?_ -/
  /-   have hpi : 0 < 2 * Real.pi := by positivity -/
  /-   exact -/
  /-     (zero_add (2 * Real.pi) ▸ AddCircle.equivIco (p := 2 * Real.pi) (hp := .mk hpi) _).symm.trans -/
  /-     (AddCircle.homeomorphCircle hpi.ne.symm).toEquiv -/
  /- · simp -/
  /-   apply Continuous.comp -/
  /-   · done -/
  /-   · done -/
  /- · simp -/

/- def funny : Trivialization (expMapCircle ⁻¹' {1}) expMapCircle where -/
def funny : Trivialization (zmultiples (2 * Real.pi)) expMapCircle where
  /- PartialEquiv -/
  toFun := fun x ↦ by
    refine ⟨AddCircle.homeomorphCircle' ?_, ?_⟩
    rw [AddCircle]
  invFun := fun x ↦ arg x.fst
  source := univ \ zmultiples (2 * Real.pi)
  target := (univ \ {1}) ×ˢ {⟨0, by simp⟩}
  map_source' := by
    simp
    intro x hx₁ hx₂
    sorry
  map_target' := by
    simp
    sorry
  left_inv' := fun x hx ↦ by
    sorry
  right_inv' := by simp

  /- PartialHomeomorph -/
  open_source := by
    simp only
    rw [← Set.compl_eq_univ_diff, isOpen_compl_iff]
    sorry
  open_target := by
    simp only [isOpen_prod_iff']
    left
    simp
  continuousOn_toFun := expMapCircle.continuous.continuousOn.prod continuousOn_const
  continuousOn_invFun := by
    sorry
    /- apply Continuous.continuousOn -/
    /- simp only at * -/
    /- rw [continuous_iff_continuousAt] -/
    /- apply continuousAt_arg -/

  /- Trivialization -/
  baseSet := univ \ {1}
  open_baseSet := _
  source_eq := by simp
  target_eq := by simp
  proj_toFun := by intros; simp_all

#check NormedSpace.discreteTopology_zmultiples

example {f : ℝ → ℝ} {A : Set ℝ} (hf : ContinuousOn f A) :
    ContinuousOn (fun x ↦ (⟨f x, ⟨0, True.intro⟩⟩ : ℝ × { x : ℝ // True })) A := by
  sorry

example : IsCoveringMap expMapCircle := by
  simp only [IsCoveringMap, IsEvenlyCovered]
  refine fun x ↦ ⟨?_, ?_⟩
  · cases' x with x hx
    -- refine forall_open_iff_discrete.mp fun s ↦ ?_
    -- apply Continuous.isOpen_preimage
    rw [discreteTopology_iff_nhds]
    intro s
    ext y
    simp
    use mem_of_mem_nhds, fun h ↦ ?_
    rw [_root_.mem_nhds_iff]
    sorry
  · exact ⟨funny, ?_⟩
