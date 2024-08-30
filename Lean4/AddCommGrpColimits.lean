import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

open scoped DirectSum
open FiniteDimensional Function Set
open CategoryTheory Category Limits Preadditive

universe w v u u'

section CoequalizerResult

variable
  {J : Type u} [Category.{v} J] [DecidableEq J] (F : J ⥤ AddCommGrp.{max u v w})
  {α : Type u'} [DecidableEq α] (ι : α → J)
  {G H : AddCommGrp.{u'}} (f g : G ⟶ H)

open Group AddSubgroup QuotientAddGroup
-- I need this cuz .mk' gives a →+ and type checker doesn't like it in place of ⟶
abbrev cocone_quotient_map : H ⟶ AddCommGrp.of (H ⧸ f.range) :=
  QuotientAddGroup.mk' (AddMonoidHom.range f)

noncomputable def cocone_cokernel : CokernelCofork f := by
  apply CokernelCofork.ofπ (cocone_quotient_map f)
  symm
  ext a
  apply (mk'_eq_mk' _).mpr
  simp

noncomputable def cocone_cokernel_isColimit : IsColimit (cocone_cokernel f) := by
  refine Cofork.IsColimit.mk _ ?_ ?_ ?_
  · intro s
    refine AddCommGrp.ofHom <| lift _ s.π <| (AddMonoidHom.range_le_ker_iff _ _).mpr ?_
    change f ≫ s.π = 0
    simp
  · intro s
    ext h
    simp [cocone_cokernel]
  · intro s m hm
    ext ⟨t⟩
    simp_rw [← hm]
    rfl

noncomputable def cokernelEquiv : cokernel f ≅ AddCommGrp.of (H ⧸ f.range) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (cocone_cokernel_isColimit f)

variable (h : G ⟶ H) in
noncomputable def coequalizerEquivAdd : coequalizer f g ≅ coequalizer (f + h) (g + h) := by
    let π₁ := coequalizer.π f g
    let π₂ := coequalizer.π (f + h) (g + h)
    have h₁ : f ≫ π₂ = g ≫ π₂ := by simpa using coequalizer.condition (f + h) (g + h)
    have h₂ : (f + h) ≫ π₁ = (g + h) ≫ π₁ := by simpa using coequalizer.condition f g
    refine ⟨coequalizer.desc π₂ h₁, coequalizer.desc π₁ h₂,
      coequalizer.hom_ext ?_, coequalizer.hom_ext ?_⟩
    all_goals simp [← assoc, coequalizer.π_desc π₂ h₁, coequalizer.π_desc π₁ h₂]

noncomputable def coequalizerEquivCokernel : coequalizer f g ≅ cokernel (f - g) := by
  convert coequalizerEquivAdd f g (-g) using 2 <;> simp only [← sub_eq_add_neg, sub_self]

noncomputable def coequalizerEquiv : coequalizer f g ≅ AddCommGrp.of (H ⧸ (f - g).range) :=
  (coequalizerEquivCokernel f g).trans (cokernelEquiv (f - g))

end CoequalizerResult



section ColimitResult

variable
  {J : Type u} [Category.{v} J] [DecidableEq J] (F : J ⥤ AddCommGrp.{max u v})
  [∀ X Y : J, DecidableEq (X ⟶ Y)]

noncomputable abbrev f₁ :
    AddCommGrp.of (⨁ (f : Σ p : J × J, p.fst ⟶ p.snd), F.obj f.fst.fst)
      ⟶ AddCommGrp.of (⨁ j, F.obj j) :=
  DirectSum.toAddMonoid fun ⟨⟨_, p₂⟩, fp⟩ ↦ (DirectSum.of _ p₂).comp (F.map fp)

noncomputable abbrev f₂ :
    AddCommGrp.of (⨁ (f : Σ p : J × J, p.fst ⟶ p.snd), F.obj f.fst.fst)
      ⟶ AddCommGrp.of (⨁ j, F.obj j) :=
  DirectSum.toAddMonoid fun ⟨⟨p₁, _⟩, _⟩ ↦ DirectSum.of (fun j ↦ F.obj j) p₁

noncomputable def buildColimit : Cocone F where
  pt := coequalizer (f₁ F) (f₂ F)
  ι := {
    app := fun X ↦ AddCommGrp.ofHom (DirectSum.of (fun j ↦ F.obj j) X) ≫ coequalizer.π _ _
    naturality := fun X Y f ↦ by
      ext m
      let m' := DirectSum.of (fun (f : Σ p : J × J, p.fst ⟶ p.snd) ↦ F.obj f.fst.fst) ⟨⟨X, Y⟩, f⟩ m
      convert congrArg (fun F' ↦ F' m') (coequalizer.condition (f₁ F) (f₂ F)) <;> simp [f₁, f₂, m']
  }

noncomputable def buildColimit_pt_eq : (buildColimit F).pt = coequalizer (f₁ F) (f₂ F) :=
  rfl

noncomputable def buildColimit_pt_iso :
    (buildColimit F).pt ≅ AddCommGrp.of ((⨁ j, F.obj j) ⧸ (f₁ F - f₂ F).range) :=
  coequalizerEquiv _ _

theorem buildColimit_desc (s : Cocone F) :
    f₁ F ≫ (DirectSum.toAddMonoid s.ι.app : _ ⟶ s.pt) = f₂ F ≫ DirectSum.toAddMonoid s.ι.app := by
  apply DirectSum.addHom_ext'
  intro ⟨⟨p₁, p₂⟩, (fp : p₁ ⟶ p₂)⟩
  ext
  let hs (x) : (s.ι.app p₂) ((F.map fp) x) = (s.ι.app p₁ x) := congrArg (fun f ↦ f x) (s.w fp)
  simpa [f₁, f₂] using hs _

noncomputable def buildIsColimit : IsColimit (buildColimit F) where
  desc s := coequalizer.desc (DirectSum.toAddMonoid s.ι.app) (buildColimit_desc F s)
  fac s j := by ext; simp [buildColimit]
  uniq s m hm := coequalizer.hom_ext <| DirectSum.addHom_ext' <| fun j ↦ by
    ext t; simp [buildColimit, coequalizer.π_desc, ← hm j]

noncomputable def colimitEquiv : colimit F ≅ AddCommGrp.of ((⨁ j, F.obj j) ⧸ (f₁ F - f₂ F).range) :=
  ((colimit.isColimit F).coconePointUniqueUpToIso (buildIsColimit F)) ≪≫ buildColimit_pt_iso F

end ColimitResult
