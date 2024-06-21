import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic

variable {a b c d : ℝ} (hab : a < b) (hcd : c < d)

def Ico_equiv_unit_Ico : Ico 0 1 ≃ Ico a b := where
  toFun := fun ⟨x, hx⟩ ↦ sorry
  invFun := _
  left_inv := _
  right_inv := _

def Ioc_equiv_Ico {a b c d : ℝ} (hab : a < b) (hcd : c < d) : Ico a b ≃ Ico c d where
  toFun := fun ⟨x, hx⟩ ↦ 
  invFun := _
  left_inv := _
  right_inv := _

