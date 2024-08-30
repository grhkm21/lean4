import Mathlib
import Lean4.E8Def.Defs

open EuclideanSpace Matrix algebraMap

noncomputable section Def

def E₈' : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix E₈
def F₈' : Matrix (Fin 8) (Fin 8) ℝ := (algebraMap ℚ ℝ).mapMatrix F₈

theorem E₈'_mul_F₈'_eq_one : E₈' * F₈' = 1 := by
  rw [E₈', F₈', RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
    E₈_mul_F₈_eq_one, map_one _ coe_zero coe_one]

theorem F₈'_mul_E₈'_eq_one : F₈' * E₈' = 1 := by
  rw [E₈', F₈', RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← Matrix.map_mul,
    F₈_mul_E₈_eq_one, map_one _ coe_zero coe_one]

#check isUnit_of_mul_eq_one
example : LinearIndependent ℝ E₈' ∧ Submodule.span ℝ (Set.range E₈') = ⊤ := by
  rw [is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det]
  change IsUnit E₈'.det
  apply isUnit_of_mul_eq_one E₈'.det F₈'.det
  rw [← det_mul, E₈'_mul_F₈'_eq_one, det_one]

#print E₈_mul_F₈_eq_one

end Def
