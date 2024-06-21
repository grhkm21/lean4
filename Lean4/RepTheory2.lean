import Mathlib.Algebra.Category.GroupCat.Zero
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Simple
import Mathlib.Order.BoundedOrder
import Mathlib.RepresentationTheory.Action.Limits
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule

open scoped ZeroObject
open Module Submodule Representation FiniteDimensional Function Pointwise CategoryTheory
  MonoidAlgebra Limits

universe u
variable {k G : Type u} [Field k] [Group G]

--------------------------------------------------------------------------------------------

section instances

theorem CategoryTheory.Functor.map_isZero_iff {C D} [Category C] [Category D] (F : C ⥤ D)
    [HasZeroMorphisms C] [HasZeroMorphisms D] [PreservesZeroMorphisms F] [Faithful F] {X} :
    IsZero (F.obj X) ↔ IsZero X := by
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero, ← F.map_id, F.map_eq_zero_iff]

theorem ModuleCat.isZero_iff {R} [Ring R] {M : ModuleCat R} : IsZero M ↔ Subsingleton M :=
  ⟨fun h ↦ @Equiv.subsingleton _ _
    ((forget _).mapIso (h.iso (isZero_of_subsingleton (ModuleCat.of R PUnit)))).toEquiv
    (inferInstanceAs (Subsingleton PUnit)), fun _ ↦ isZero_of_subsingleton _⟩

theorem FdRep.isZero_iff {V : FdRep k G} : IsZero V ↔ Subsingleton V := by
  rw [← (forget₂ (FdRep k G) (FGModuleCat k)).map_isZero_iff,
    ← (FGModuleCat.forget₂Monoidal _).map_isZero_iff, ModuleCat.isZero_iff]
  rfl

theorem Rep.isZero_iff {V : Rep k G} : IsZero V ↔ Subsingleton V := by
  rw [← (forget₂ (Rep k G) (ModuleCat k)).map_isZero_iff, ModuleCat.isZero_iff]
  rfl

instance {V : FdRep k G} [Simple V] : Nontrivial V := by
  rw [← not_subsingleton_iff_nontrivial, ← FdRep.isZero_iff]
  exact Simple.not_isZero V

instance {V : Rep k G} [Simple V] : Nontrivial V := by
  rw [← not_subsingleton_iff_nontrivial, ← Rep.isZero_iff]
  exact Simple.not_isZero V

instance {V : Rep k G} [Simple V] : Nontrivial V.ρ.asModule := (inferInstance : Nontrivial V)

def Rep.zero (k G) [Monoid G] [Ring k] : Rep k G :=
  ⟨ModuleCat.of k PUnit, ⟨1, fun _ _ ↦ rfl⟩⟩

theorem Rep.zero_isZero : IsZero (Rep.zero k G) := by
  exact (IsZero.iff_id_eq_zero (zero k G)).mpr rfl

instance : HasZeroObject (Rep k G) :=
  ⟨⟨Rep.zero k G, Rep.isZero_iff.mpr (inferInstance : Subsingleton PUnit)⟩⟩

instance {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {W : Submodule R V} :
    Mono (ModuleCat.ofHom W.subtype) :=
  ConcreteCategory.mono_of_injective _ <| (Set.injective_codRestrict Subtype.prop).mp fun _ _ h ↦ h

end instances

--------------------------------------------------------------------------------------------

section CategoryTheory

@[simp]
theorem Mono.iff {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

theorem Mono.comp_iso_hom {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ≅ Z) :
    Mono (f ≫ g.hom) ↔ Mono f := by
  simp

theorem Mono.comp_iso_inv {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Z ≅ Y) :
    Mono (f ≫ g.inv) ↔ Mono f := by
  simp

end CategoryTheory

--------------------------------------------------------------------------------------------

section Results

variable {V : Rep k G}

local notation:arg k:75"⟦"G:75"⟧" => MonoidAlgebra k G

-- This should be in Mathlib
noncomputable def FdRep.toRep (V : FdRep k G) : Rep k G :=
  (forget₂ (FdRep k G) (Rep k G)).obj V

section SubmoduleResults

variable (W : Submodule k⟦G⟧ V.ρ.asModule)

/- These exist for type checking. -/
noncomputable def Rep.ofSubmodule : Rep k G :=
  equivalenceModuleMonoidAlgebra.inverse.obj (ModuleCat.of k⟦G⟧ W)

noncomputable def Rep.ofSubmoduleHom : ofSubmodule W ⟶ V :=
  (equivalenceModuleMonoidAlgebra.inverse.map <| ModuleCat.ofHom <| W.subtype) ≫ V.unitIso.inv

theorem Rep.ofSubmoduleHom_mono : Mono (ofSubmoduleHom W) := by
  rw [ofSubmoduleHom, Mono.comp_iso_inv]
  infer_instance

end SubmoduleResults

theorem Rep.isSimpleModule_of_Simple [hV : Simple V] : IsSimpleModule k⟦G⟧ V.ρ.asModule := by
  /- Strategy:
    1. Construct the (W' : Rep k G) attached to W (done)
    2. Construct a Rep hom (Action.Hom) W' ⟶ V, which should be easy but I can't??
    3. Prove this hom is Mono, i.e. injective, which is again easy
    4. Conclude with that -/
  apply IsSimpleOrder.mk fun W ↦ ?_
  have hW_mono := Rep.ofSubmoduleHom_mono W
  have hV' := hV.mono_isIso_iff_nonzero (Y := ofSubmodule W) (ofSubmoduleHom W)
  by_cases hW : IsIso (ofSubmoduleHom W)
  /- If the embedding W → V is bijective, then all elements in V are of the form ↑w, so W = ⊤ -/
  · right
    have : Bijective W.subtype := ConcreteCategory.bijective_of_isIso (ofSubmoduleHom W)
    obtain ⟨inv, ⟨_, h_inv₂⟩⟩ := bijective_iff_has_inverse.mp this
    ext w
    rw [← show inv w = w from h_inv₂ w]
    simp [coe_mem]
  /- Otherwise, W → V is the zero map but also mono, meaning W = ⊥ -/
  · left
    simp only [hW, ne_eq, false_iff, not_not] at hV'
    simp_rw [ofSubmoduleHom, Preadditive.IsIso.comp_right_eq_zero] at hV' hW_mono
    simp [hV'] at hW_mono
    ext w
    constructor <;> intro hw
    · apply (AddSubmonoid.mk_eq_zero _).mp
      exact congrArg (fun f ↦ f.hom ⟨w, hw⟩) (@hW_mono (ofSubmodule W) (𝟙 _) 0)
    · simp only [(mem_bot _).mp hw, Submodule.zero_mem]

theorem Rep.simple_of_isSimpleModule [hV : IsSimpleModule k⟦G⟧ V.ρ.asModule] : Simple V := by
  cases' hV with hV_nontrivial hV_top_bot
  constructor
  intro W f f_mono
  constructor
  · rintro hf rfl
    exact ((Submodule.nontrivial_iff _).mp (orderIsoMapComap <| linearEquivIsoModuleIso.inv <|
      equivalenceModuleMonoidAlgebra.functor.mapIso (isIsoZeroEquivIsoZero _ _ hf).snd
      ).toEquiv.symm.nontrivial).exists_pair_ne.2.2 <| (Rep.isZero_iff.mp (isZero_zero _)).allEq _ _
  · intro hf
    sorry
#check Exists

noncomputable example {k G : Type u} [Field k] [Group G]
    (V W : Rep k G) (h : V ≅ W) (M : Submodule k⟦G⟧ V.ρ.asModule) : Submodule k⟦G⟧ W.ρ.asModule :=
  orderIsoMapComap (linearEquivIsoModuleIso.inv
    <| Rep.equivalenceModuleMonoidAlgebra.functor.mapIso h) M

#check Representation
#check LinearEquiv.toModuleIso
#check Iso.toLinearEquiv
#check Equivalence.changeFunctor

example {R V W : Type u} [Ring R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
    (M : Submodule R V) (h : ModuleCat.of R V ≅ ModuleCat.of R W) : Submodule R W :=
  orderIsoMapComap (linearEquivIsoModuleIso.inv h) M

noncomputable example {V W : Rep k G} (M : Submodule k⟦G⟧ V.ρ.asModule) (h : V ≅ W) :
    Submodule k⟦G⟧ W.ρ.asModule :=
  orderIsoMapComap (linearEquivIsoModuleIso.inv
    <| Rep.equivalenceModuleMonoidAlgebra.functor.mapIso h) M

example {C D : Type u} [Category C] [Category D]
    {X Y : C} {F : C ⥤ D} (h : X ≅ Y) : F.obj X ≅ F.obj Y := by
  exact F.mapIso h
