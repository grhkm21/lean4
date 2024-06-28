import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Multiset.Fintype

open Function CategoryTheory Category Limits

variable {G H : AddCommGrp} (f g : G ⟶ H)

open Group AddSubgroup

-- I need this cuz .mk' gives a →+ and type checker doesn't like it in place of ⟶
abbrev cocone_quotient_map : H ⟶ AddCommGrp.of (H ⧸ (f - g).range) :=
  QuotientAddGroup.mk' (AddMonoidHom.range (f - g))

-- Define the cocone over parallelPair f g
noncomputable def cocone_coequalizer : Cocone (parallelPair f g) where
  pt := AddCommGrp.of (H ⧸ (f - g).range)
  ι := {
    app := fun
      | .zero => f ≫ cocone_quotient_map f g
      | .one => cocone_quotient_map f g
    naturality := sorry
  }
