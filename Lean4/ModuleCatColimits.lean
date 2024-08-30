import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

-- Kind of just importing everything
-- Goal: Reprove that MonCat has colimits by constructing equivalence between MonCat and
-- category of finitely supported functions, or something

open scoped DirectSum
open Set hiding range
open FiniteDimensional Function
open CategoryTheory Category Limits Preadditive

universe w v₁ v₂ u₁ u₂
variable {R : Type u₁} [Ring R]



section MathlibResult

-- TODO: Replace               vvvvvv with Fintype
#check Finsupp.linearEquivFunOnFinite

open Module

variable
  {ι : Type*} [Fintype ι]
  (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] [∀ i, Finite R (M i)]

def DFinsupp.linearEquivFunOnFintype : (Π₀ (i : ι), M i) ≃ₗ[R] ((i : ι) → M i) :=
  Equiv.toLinearEquiv equivFunOnFintype (by constructor <;> simp [equivFunOnFintype])

instance Module.Finite.instFiniteDirectSum : Finite R (⨁ j, M j) :=
  Finite.equiv (DFinsupp.linearEquivFunOnFintype M).symm

end MathlibResult




section CoprodResult

variable
  {J : Type u₂} [DecidableEq J] [SmallCategory J]
  (F : J ⥤ ModuleCatMax.{v₁, u₂} R) {G H : ModuleCat R} (f g : G ⟶ H)
  {α : Type u₂} [DecidableEq α] (ι : α → J)

def cocone_coprod : Cocone (Discrete.functor F.obj) where
  pt := ModuleCat.of R (⨁ j, F.obj j)
  ι := Discrete.natTrans <| fun ⟨j⟩ ↦ DirectSum.lof _ _ (fun j ↦ F.obj j) j

def cocone_coprod' : Cocone (Discrete.functor (F.obj ∘ ι)) where
  pt := ModuleCat.of R (⨁ j, (F.obj ∘ ι) j)
  ι := Discrete.natTrans fun ⟨j⟩ ↦ DirectSum.lof _ _ (fun j ↦ (F.obj ∘ ι) j) j

def cocone_coprod_isColimit : IsColimit (cocone_coprod F) where
  desc := fun s ↦ DirectSum.toModule _ _ _ <| fun j ↦ s.ι.app (Discrete.mk j)
  fac := fun _ ⟨_⟩ ↦ by
    ext
    simp [cocone_coprod]
    exact DirectSum.toModule_lof (M := fun j ↦ F.obj j) ..
  uniq := fun s m hm ↦ by
    ext t
    convert DirectSum.toModule.unique _ _ _
    ext j
    simp at j
    simp [← hm, cocone_coprod]
    rfl

def cocone_coprod_isColimit' : IsColimit (cocone_coprod' F ι) where
  desc := fun s ↦ DirectSum.toModule _ _ _ <| fun j ↦ s.ι.app (Discrete.mk j)
  fac := fun _ ⟨_⟩ ↦ by
    ext
    simp [cocone_coprod]
    exact DirectSum.toModule_lof (M := fun j ↦ (F.obj ∘ ι) j) ..
  uniq := fun s m hm ↦ by
    ext t
    convert DirectSum.toModule.unique _ _ _
    ext j
    simp at j
    simp [← hm, cocone_coprod]
    rfl

noncomputable def coprodEquivDirectSum : ∐ F.obj ≅ ModuleCat.of R (⨁ j, F.obj j) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (cocone_coprod_isColimit F)

noncomputable def coprodEquivDirectSum' : ∐ F.obj ∘ ι ≅ ModuleCat.of R (⨁ j, (F.obj ∘ ι) j) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (cocone_coprod_isColimit' F ι)

end CoprodResult



section CoequalizerResult

variable {G H : ModuleCatMax.{v₁, u₂} R} (f g : G ⟶ H)

open Module Submodule LinearMap

abbrev cocone_quotient_map : H ⟶ ModuleCat.of R (H ⧸ range f) :=
  (range f).mkQ

noncomputable def cocone_cokernel : CokernelCofork f := by
  apply CokernelCofork.ofπ (cocone_quotient_map f)
  ext t
  change (range f).mkQ (f t) = 0
  rw [← mem_ker]
  simp

noncomputable def cocone_cokernel_isColimit : IsColimit (cocone_cokernel f) := by
  refine Cofork.IsColimit.mk _ ?_ ?_ ?_
  · intro s
    apply liftQ _ s.π _
    apply range_le_ker_iff.mpr
    change f ≫ s.π = 0
    simp
  · intro s
    rfl
  · intro s m hm
    ext ⟨t⟩
    simp_rw [← hm]
    rfl

noncomputable def cokernelEquiv : cokernel f ≅ ModuleCat.of R (H ⧸ range f) :=
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

noncomputable def coequalizerEquiv : coequalizer f g ≅ ModuleCat.of R (H ⧸ range (f - g)) :=
  (coequalizerEquivCokernel f g).trans (cokernelEquiv (f - g))

end CoequalizerResult



section ColimitResult

variable {J : Type u₂} [DecidableEq J] [SmallCategory J] (F : J ⥤ ModuleCatMax.{v₁, u₂} R)
variable [∀ X Y : J, DecidableEq (X ⟶ Y)]

open Module Submodule LinearMap

namespace ModuleCat.HasColimitOfHasCoproductsOfHasCoequalizers

noncomputable def f₁ :
    ModuleCat.of R (⨁ (f : Σ p : J × J, p.fst ⟶ p.snd), F.obj f.fst.fst)
      ⟶ ModuleCat.of R (⨁ j, F.obj j) :=
  DirectSum.toModule _ _ _ fun ⟨⟨_, p₂⟩, fp⟩ ↦ DirectSum.lof _ _ _ p₂ ∘ₗ F.map fp

noncomputable def f₂ :
    ModuleCat.of R (⨁ (f : Σ p : J × J, p.fst ⟶ p.snd), F.obj f.fst.fst)
      ⟶ ModuleCat.of R (⨁ j, F.obj j) :=
  DirectSum.toModule _ _ _ fun ⟨⟨p₁, _⟩, _⟩ ↦ DirectSum.lof _ _ (fun j ↦ F.obj j) p₁

noncomputable def buildColimit : Cocone F where
  pt := coequalizer (f₁ F) (f₂ F)
  ι := {
    app := fun X ↦ DirectSum.lof _ _ (fun j ↦ F.obj j) X ≫ coequalizer.π _ _
    naturality := fun X Y f ↦ by
      ext m
      let m' := DirectSum.lof R (Σ p : J × J, p.fst ⟶ p.snd) (fun f ↦ F.obj f.fst.fst) ⟨⟨X, Y⟩, f⟩ m
      -- rw / simp really doesn't like me here...
      have h₁ : (f₁ F) m' = (DirectSum.lof R J (fun j ↦ F.obj j) Y) ((F.map f) m) := by
        simp_rw [f₁, m', ModuleCat.of]
        apply DirectSum.toModule_lof
      have h₂ : (f₂ F) m' = (DirectSum.lof R J (fun j ↦ F.obj j) X) m := by
        simp_rw [f₂, m', ModuleCat.of]
        apply DirectSum.toModule_lof
      convert congrArg (fun F' ↦ F' m') (coequalizer.condition (f₁ F) (f₂ F))
      all_goals simpa [h₁, h₂] using by rfl
  }

noncomputable def buildColimit_pt_eq : (buildColimit F).pt = coequalizer (f₁ F) (f₂ F) :=
  rfl

noncomputable def buildColimit_pt_iso :
    (buildColimit F).pt ≅ ModuleCat.of R ((⨁ j, F.obj j) ⧸ range (f₁ F - f₂ F)) :=
  coequalizerEquiv.{v₁, u₁, u₂} _ _

theorem buildColimit_desc (s : Cocone F) :
    f₁ F ≫ DirectSum.toModule _ _ _ s.ι.app = f₂ F ≫ DirectSum.toModule _ _ _ s.ι.app := by
  apply DirectSum.linearMap_ext
  intro ⟨⟨p₁, p₂⟩, (fp : p₁ ⟶ p₂)⟩
  ext (x : F.obj p₁)
  let hs : (s.ι.app p₂) ((F.map fp) x) = (s.ι.app p₁ x) := congrArg (fun f ↦ f x) (s.w fp)
  simpa [f₁, f₂, ModuleCat.of, ModuleCat.comp_def] using hs

noncomputable def buildIsColimit : IsColimit (buildColimit F) where
  desc s := coequalizer.desc (DirectSum.toModule _ _ _ s.ι.app) (buildColimit_desc F s)
  fac s j := by
    ext
    simp_rw [buildColimit, assoc, colimit.ι_desc]
    exact DirectSum.toModule_lof ..
  uniq s m hm := by
    apply coequalizer.hom_ext
    apply DirectSum.linearMap_ext
    intro j
    ext t
    replace hm := congrArg (fun F' ↦ F' t) (hm j)
    dsimp [buildColimit, ModuleCat.comp_def] at hm
    rw [coequalizer.π_desc, ModuleCat.comp_def, LinearMap.comp_assoc, hm, eq_comm]
    exact DirectSum.toModule_lof ..

end ModuleCat.HasColimitOfHasCoproductsOfHasCoequalizers

open ModuleCat.HasColimitOfHasCoproductsOfHasCoequalizers

noncomputable def ModuleCat.colimitEquiv :
    colimit F ≅ ModuleCat.of R ((⨁ j, F.obj j) ⧸ range (f₁ F - f₂ F)) :=
  ((colimit.isColimit F).coconePointUniqueUpToIso (buildIsColimit F)) ≪≫ buildColimit_pt_iso F

instance ModuleCat.instFiniteColimit [Fintype J] [∀ j, Finite R (F.obj j)] :
    Finite R ↑(colimit F) :=
  have : Finite R ↑(of R ((⨁ (j : J), ↑(F.obj j)) ⧸ range (f₁ F - f₂ F))) :=
    Finite.quotient (A := R) _ _
  Finite.equiv (Iso.toLinearEquiv (colimitEquiv F)).symm

end ColimitResult



section ColimitFGResult

/- TODO: Allow J to be in Type u₂, and everything above as well,
and forget₂, and FGModuleCat, and FullSubcategory as well -/

variable {J : Type u₂} [SmallCategory J] [FinCategory J] (F : J ⥤ FGModuleCat R)

open Module Finite DFinsupp Classical

instance [Fintype J] : Finite R (colimit (F ⋙ forget₂ (FGModuleCat R) (ModuleCat R)) : ModuleCat R) :=
  have (j : J) : Finite R ((F ⋙ forget₂ (FGModuleCat R) (ModuleCat R)).obj j) :=
    (inferInstance : Finite R (F.obj j))
  inferInstance

namespace FGModuleCat

noncomputable def forget₂CreatesColimit [Fintype J] :
    CreatesColimit F (forget₂ (FGModuleCat R) (ModuleCat R)) :=
  createsColimitOfFullyFaithfulOfIso
    ⟨colimit (F ⋙ forget₂ (FGModuleCat R) (ModuleCat R)), inferInstance⟩ (Iso.refl _)

noncomputable instance [Fintype J] :
    CreatesColimitsOfShape J (forget₂ (FGModuleCat R) (ModuleCat R)) where
  CreatesColimit {F} := forget₂CreatesColimit F

noncomputable instance asdf [FinCategory J] : HasColimitsOfShape J (FGModuleCat R) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (forget₂ (FGModuleCat R) (ModuleCat R))

instance : HasFiniteColimits (FGModuleCat R) :=
  hasFiniteColimits_of_hasFiniteColimits_of_size _ (fun _ _ _ ↦ asdf)

end FGModuleCat

end ColimitFGResult

