import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Homotopy.HomotopyGroup

-- In this file, I try to formalise some parts of the (homological) proof of the Brouwer Fixed Point
-- Theorem while procrasting on my third year project presentation

open Metric Filter Set Function TopologicalSpace Topology FundamentalGroupoid
open CategoryTheory CategoryStruct Complex

variable {X : Type*} [TopologicalSpace X]
variable {x : circle}

def id_path : Path x x where
  toFun := fun _ ↦ x
  source' := rfl
  target' := rfl

@[simp] noncomputable def helix : ℝ → ℝ × ℝ × ℝ :=
  fun s ↦ (Real.cos (2 * Real.pi * s), Real.sin (2 * Real.pi * s), s)

@[simp] def ρ : ℝ × ℝ × ℝ → ℝ × ℝ :=
  fun ⟨x, y, _⟩ ↦ ⟨x, y⟩

@[simp] def toComplex : ℝ × ℝ → ℂ :=
  fun ⟨x, y⟩ ↦ x + y * I

@[simp] noncomputable def ω : ℝ → ℂ := toComplex ∘ ρ ∘ helix

@[simp] noncomputable def ω' : ℝ → ↥circle :=
  fun t ↦ ⟨(toComplex ∘ ρ ∘ helix) t, by
    simp [-ofReal_cos, -ofReal_sin]
    rw [ofReal_cos, ofReal_sin, abs_cos_add_sin_mul_I]
  ⟩

/- TODO: Put to Mathlib -/
@[simp]
theorem Real.sin_int_mul_two_pi (n : ℤ) : (n * (2 * Real.pi)).sin = 0 :=
  (Real.sin_periodic.int_mul_eq n).trans Real.sin_zero
#check Real.cos_int_mul_two_pi

noncomputable def nth_loop (n : ℤ) : Path x x where
  toFun := (· * x) ∘ ω' ∘ (· * n) ∘ (↑)
  source' := by simp
  target' := by simp [-ofReal_cos, -ofReal_sin, mul_comm _ (n : ℝ)]

open Path Homotopy Homotopic in
noncomputable def nth_loop' (n : ℤ) : FundamentalGroup circle x where
  hom := Quot.mk _ (nth_loop n)
  inv := Quot.mk _ (nth_loop n).symm
  hom_inv_id := Quot.sound ⟨(reflTransSymm _).symm⟩
  inv_hom_id := Quot.sound ⟨(reflSymmTrans _).symm⟩

open scoped unitInterval

def lift_path_to_real {f : I → circle} {x₀ : circle} {x₁ : ω ⁻¹' {↑x₀}} :
    { f : I → ℝ // f 0 = x₁ } := by
  sorry

example (x) : Multiplicative ℤ ≃* FundamentalGroup circle x where
  toFun := nth_loop'
  invFun := by
    /- path: x ≃ x modulo homotopy -/
    intro ⟨p, p_inv, hp₁, hp₂⟩
  left_inv := _
  right_inv := _
  map_mul' := _
