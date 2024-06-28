import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Simple
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Order.BoundedOrder
import Mathlib.RepresentationTheory.Action.Limits
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule

open scoped ZeroObject
open Module Submodule Representation FiniteDimensional Pointwise CategoryTheory MonoidAlgebra Limits

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

theorem Mono.iff {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ ∀ {Z : C} (g h : Z ⟶ X), g ≫ f = h ≫ f → g = h :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

theorem Mono.comp_iso_hom {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ≅ Z) :
    Mono (f ≫ g.hom) ↔ Mono f := by
  simp [Mono.iff]

theorem Mono.comp_iso_inv {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Z ≅ Y) :
    Mono (f ≫ g.inv) ↔ Mono f := by
  simp [Mono.iff]

end CategoryTheory

--------------------------------------------------------------------------------------------

section Results

variable {V : Rep k G}

open Function

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
    simp [Mono.iff, hV'] at hW_mono
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
  · /- If f : W ⟶ V is iso, then f ≠ 0 -/
    /- If the zero map is an isomorphism, then V ≅ 0, but that contradicts that V is nontrivial -/
    rintro hf rfl
    obtain ⟨_, _, hW'⟩ := (Submodule.nontrivial_iff _).mp (orderIsoMapComap <|
      linearEquivIsoModuleIso.inv <| equivalenceModuleMonoidAlgebra.functor.mapIso
        (isIsoZeroEquivIsoZero _ _ hf).snd).toEquiv.symm.nontrivial
    exact hW' <| (Rep.isZero_iff.mp (isZero_zero _)).allEq _ _
  · intro hf
    let map : W.ρ.asModule →ₗ[k⟦G⟧] V.ρ.asModule := equivalenceModuleMonoidAlgebra.functor.map f
    let im := Submodule.map map ⊤
    replace hV_top_bot := (hV_top_bot im).resolve_left ?_
    /- Given that im = ⊤, prove f is iso -/
    /- I go for the lazy route of unwrapping definitionds and proving the result in module land -/
    · have : IsIso (equivalenceModuleMonoidAlgebra.functor.map f) := by
        refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
        · apply (ModuleCat.mono_iff_injective _).mp
          exact equivalenceModuleMonoidAlgebra.functor.map_mono f
        · apply (Set.range_iff_surjective (f := map)).mp
          rw [← LinearMap.range_coe, ← Submodule.map_top]
          exact congrArg (fun f ↦ f.carrier) hV_top_bot
      exact (NatIso.isIso_map_iff equivalenceModuleMonoidAlgebra.unitIso.symm f).mp
        <| equivalenceModuleMonoidAlgebra.inverse.map_isIso _
    /- Prove that im ≠ ⊥ -/
    · contrapose! hf
      have (w) : f.hom w = 0 := by
        apply Set.mem_singleton_iff.mp
        change map w ∈ (⊥ : Submodule k⟦G⟧ _)
        exact hf ▸ Set.mem_image_of_mem _ (mem_top (R := k⟦G⟧) (M := W.ρ.asModule))
      ext w
      convert this w

theorem Rep.simple_iff : Simple V ↔ IsSimpleModule k⟦G⟧ V.ρ.asModule :=
  ⟨fun _ ↦ isSimpleModule_of_Simple, fun _ ↦ simple_of_isSimpleModule⟩

end Results

--------------------------------------------------------------------------------------------

section FdTodo1

open FGModuleCat

variable {V W : FdRep k G}

/-
## TODO
[X] `FdRep k G ≌ FullSubcategory (FiniteDimensional k)`
[X] Upgrade the right rigid structure to a rigid structure (this just needs to be done for `FGModuleCat`).
[ ] `FdRep k G` has all finite colimits.
  Note: Probably want to show that (FGModuleCat k) has finite colimits (and abelian below).
  See "RepresentationTheory/Action/Limits.lean" about this
[ ] `FdRep k G` is abelian.
[ ] `FdRep k G ≌ FGModuleCat (MonoidAlgebra k G)`.
-/

/- Can we agree on how to phrase theorems/lemmas? Use V? V.toRep? V.ρ.asModule? -/
instance FdRep.toRep_finiteDimensional : FiniteDimensional k V.toRep :=
  FGModuleCat.instFiniteCarrier k _

instance FdRep.toRep_finiteDimensional' : FiniteDimensional k ((forget₂ _ (Rep k G)).obj V) :=
  FGModuleCat.instFiniteCarrier k _

noncomputable def FdRep.lift_hom (f : V ⟶ W) : V.toRep ⟶ W.toRep :=
  (forget₂ _ _).map f

/- Bundles Rep with a FiniteDimensional into a FdRep -/
noncomputable def FdRep.ofRep (V : Rep k G) [hV : FiniteDimensional k V] : FdRep k G :=
  ⟨⟨V.V, hV⟩, V.ρ⟩

noncomputable def FdRep.toFiniteDimensionalSubcategory :
    FdRep k G ⥤ FullSubcategory (fun V : Rep k G ↦ FiniteDimensional k V) :=
  FullSubcategory.lift _ (forget₂ _ _) inferInstance

noncomputable def FdRep.ofFiniteDimensionalSubcategory :
    FullSubcategory (fun V : Rep k G ↦ FiniteDimensional k V) ⥤ FdRep k G where
  obj := fun ⟨V, _⟩ ↦ FdRep.ofRep V
  map := fun f ↦ ⟨f.hom, f.comm⟩

noncomputable def FdRep.equivalenceFiniteDimensionalSubcategory :
    FdRep k G ≌ FullSubcategory (fun V : Rep k G ↦ FiniteDimensional k V) where
  functor := toFiniteDimensionalSubcategory
  inverse := ofFiniteDimensionalSubcategory
  unitIso := by aesop_cat
  counitIso := by aesop_cat

end FdTodo1

--------------------------------------------------------------------------------------------

section BraidedResults

variable {C : Type u} [Category C] [MonoidalCategory C] [BraidedCategory C] {X Y : C}

namespace BraidedCategory

open Category BraidedCategory MonoidalCategory

/- yang baxter but with β_.inv instead of β_.hom.
Maybe there is a proof via duality, but proving it directly is just copy and pasting -/
theorem yang_baxter_inv (X Y Z : C) :
    (α_ X Y Z).inv ≫ (β_ Y X).inv ▷ Z ≫ (α_ Y X Z).hom
      ≫ Y ◁ (β_ Z X).inv ≫ (α_ Y Z X).inv ≫ (β_ Z Y).inv ▷ X ≫ (α_ Z Y X).hom
        = X ◁ (β_ Z Y).inv ≫ (α_ X Z Y).inv
          ≫ (β_ Z X).inv ▷ Y ≫ (α_ Z X Y).hom ≫ Z ◁ (β_ Y X).inv := by
  rw [← braiding_inv_tensor_left_assoc, ← cancel_mono (α_ Z Y X).inv]
  repeat rw [assoc]
  rw [Iso.hom_inv_id, comp_id, ← braiding_inv_naturality_right, braiding_inv_tensor_left]

theorem yang_baxter_inv' (X Y Z : C) :
    (β_ Y X).inv ▷ Z ⊗≫ Y ◁ (β_ Z X).inv ⊗≫ (β_ Z Y).inv ▷ X =
      𝟙 _ ⊗≫ (X ◁ (β_ Z Y).inv ⊗≫ (β_ Z X).inv ▷ Y ⊗≫ Z ◁ (β_ Y X).inv) ⊗≫ 𝟙 _ := by
  rw [← cancel_epi (α_ X Y Z).inv, ← cancel_mono (α_ Z Y X).hom]
  convert yang_baxter_inv X Y Z using 1
  all_goals coherence

end BraidedCategory

end BraidedResults

--------------------------------------------------------------------------------------------

section FdTodo2

variable {C : Type u} [Category C] [MonoidalCategory C] [BraidedCategory C] {X Y : C}

/-
[X] Upgrade the right rigid structure to a rigid structure (this just needs to be done for `FGModuleCat`).
-/

open Category BraidedCategory MonoidalCategory

namespace BraidedCategory

/- coevaluation_evaluation' field of ExactPairing Y X in a braided category -/
theorem coevaluation_evaluation_braided' [inst : ExactPairing X Y] :
    X ◁ (η_ X Y ≫ (β_ Y X).inv) ≫ (α_ X Y X).inv ≫ ((β_ X Y).hom ≫ ε_ X Y) ▷ X
      = (ρ_ X).hom ≫ (λ_ X).inv := by
  /- Rearrange into _ = 𝟙 _ -/
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  /- Whitney trick transcribed: https://mathoverflow.net/a/162729/493261 -/
  calc
    _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (X ◁ (β_ Y X).inv ⊗≫ (β_ X Y).hom ▷ X) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
      coherence
    _ = 𝟙 X ⊗≫ X ◁ η_ X Y ⊗≫ (𝟙 (X ⊗ X ⊗ Y) ⊗≫ (β_ X X).hom ▷ Y ⊗≫ X ◁ (β_ X Y).hom
        ⊗≫ (β_ Y X).inv ▷ X ⊗≫ Y ◁ (β_ X X).inv ⊗≫ 𝟙 ((Y ⊗ X) ⊗ X)) ⊗≫ ε_ X Y ▷ X ⊗≫ 𝟙 X := by
      congr 3
      simp [monoidalComp]
      rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 5 rw [← IsIso.comp_inv_eq]
      simpa using yang_baxter _ _ _
    _ = 𝟙 X ⊗≫ (X ◁ η_ X Y ≫ (β_ X (X ⊗ Y)).hom) ⊗≫ ((β_ (Y ⊗ X) X).inv ≫ ε_ X Y ▷ X) ⊗≫ 𝟙 X := by
      simp [monoidalComp, braiding_tensor_right, braiding_inv_tensor_left]
    _ = _ := by
      rw [braiding_naturality_right, ← braiding_inv_naturality_right]
      simp [monoidalComp]

theorem evaluation_coevaluation_braided' [inst : ExactPairing X Y] :
    (η_ X Y ≫ (β_ Y X).inv) ▷ Y ≫ (α_ Y X Y).hom ≫ Y ◁ ((β_ X Y).hom ≫ ε_ X Y) =
      (λ_ Y).hom ≫ (ρ_ Y).inv := by
  rw [Iso.eq_comp_inv, ← Iso.inv_comp_eq_id]
  calc
    _ = 𝟙 Y ⊗≫ η_ X Y ▷ Y ⊗≫ ((β_ Y X).inv ▷ Y ⊗≫ Y ◁ (β_ X Y).hom) ≫ Y ◁ ε_ X Y ⊗≫ 𝟙 Y := by
      coherence
    _ = 𝟙 Y ⊗≫ η_ X Y ▷ Y ⊗≫ (𝟙 ((X ⊗ Y) ⊗ Y) ⊗≫ X ◁ (β_ Y Y).hom ⊗≫ (β_ X Y).hom ▷ Y
        ⊗≫ Y ◁ (β_ Y X).inv ⊗≫ (β_ Y Y).inv ▷ X ⊗≫ 𝟙 (Y ⊗ Y ⊗ X)) ⊗≫ Y ◁ ε_ X Y ⊗≫ 𝟙 Y := by
      congr 3
      all_goals simp [monoidalComp]
      iterate 2 rw [← IsIso.eq_inv_comp]
      repeat rw [← assoc]
      iterate 4 rw [← IsIso.comp_inv_eq]
      simpa using (yang_baxter Y X Y).symm
    _ = 𝟙 Y ⊗≫ (η_ X Y ▷ Y ≫ (β_ (X ⊗ Y) Y).hom) ⊗≫ ((β_ Y (Y ⊗ X)).inv ≫ Y ◁ ε_ X Y) ⊗≫ 𝟙 Y := by
      simp [monoidalComp, braiding_tensor_left, braiding_inv_tensor_right]
    _ = _ := by
      rw [braiding_naturality_left, ← braiding_inv_naturality_left]
      simp [monoidalComp]

def exactPairing_braided (X Y : C) [ExactPairing X Y] : ExactPairing Y X where
  coevaluation' := η_ X Y ≫ (β_ Y X).inv
  evaluation' := (β_ X Y).hom ≫ ε_ X Y
  coevaluation_evaluation' := coevaluation_evaluation_braided'
  evaluation_coevaluation' := evaluation_coevaluation_braided'

def leftDualOfRightDual [HasRightDual X] : HasLeftDual X where
  leftDual := Xᘁ
  exact := exactPairing_braided X Xᘁ

def rightDualOfLeftDual [HasLeftDual X] : HasRightDual X where
  rightDual := ᘁX
  exact := exactPairing_braided ᘁX X

instance leftRigidCategoryOfRightRigidCategory [RightRigidCategory C] : LeftRigidCategory C where
  leftDual X := leftDualOfRightDual (X := X)

instance rightRigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RightRigidCategory C where
  rightDual X := rightDualOfLeftDual (X := X)

instance rigidCategoryOfRightRigidCategory [RightRigidCategory C] : RigidCategory C where
  rightDual := inferInstance
  leftDual := inferInstance

instance rigidCategoryOfLeftRigidCategory [LeftRigidCategory C] : RigidCategory C where
  rightDual := inferInstance
  leftDual := inferInstance

#synth BraidedCategory (FGModuleCat k)

#synth LeftRigidCategory (FGModuleCat k)
#synth RightRigidCategory (FGModuleCat k)
#synth RigidCategory (FGModuleCat k)

#synth LeftRigidCategory (FdRep k G)
#synth RightRigidCategory (FdRep k G)
#synth RigidCategory (FdRep k G)

end BraidedCategory

end FdTodo2

--------------------------------------------------------------------------------------------

section FdTodo3

variable {C : Type u} [Category C] [MonoidalCategory C] [BraidedCategory C] {X Y : C}

/-
[ ] `FdRep k G` has all finite colimits.
  Note: Probably want to show that (FGModuleCat k) has finite colimits (and abelian below).
  See "RepresentationTheory/Action/Limits.lean" about this
  Useful: "Algebra/Category/ModuleCat/Colimits.lean"

By a theorem, we want to show that it has coproducts and coequalizers.
-/

#check limitSubobjectProduct_mono
#check FGModuleCat.instHasFiniteLimits

variable (G : Type u) [AddCommGroup G]
variable (k : Type*) [Field k]

#check ModuleCat.hasLimits'
#synth HasLimits (ModuleCat k)
#synth HasLimits AddCommGrp
#synth HasFiniteLimits (ModuleCat k)
#synth HasLimits AddCommGrp
#synth HasColimits AddCommGrp
#check AddCommGrp.instHasColimitsOfSize
/- set_option synthInstance.maxHeartbeats 80000 in -/
/- #synth HasLimitsOfShape WalkingParallelPair (ModuleCat k) -/

-- this is fully faithful, so reflects limits and colimits
#check (fullSubcategoryInclusion _ : FGModuleCat k ⥤ ModuleCat k)
#synth (fullSubcategoryInclusion _ : FGModuleCat k ⥤ ModuleCat k).Full
#synth (fullSubcategoryInclusion _ : FGModuleCat k ⥤ ModuleCat k).Faithful
#check ReflectsLimits
#check PreservesLimits
#synth ReflectsLimits (fullSubcategoryInclusion _ : FGModuleCat k ⥤ ModuleCat k)
#synth ReflectsColimits (fullSubcategoryInclusion _ : FGModuleCat k ⥤ ModuleCat k)

#check CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence
#check CategoryTheory.Limits.hasLimitsOfShape_of_equivalence
-- so (co-)limits in ModuleCat k -> (co-)limits in FGModuleCat k

#synth HasEqualizers (FGModuleCat k)

#check FGModuleCat.instHasFiniteLimits
#check hasFiniteProducts_of_hasFiniteLimits
#check FGModuleCat.instHasLimitsOfShapeOfFinCategory WalkingParallelPair

#check CreatesLimit

end FdTodo3

--------------------------------------------------------------------------------------------

section help_me_consequence

set_option linter.unusedVariables false in
theorem CategoryTheory.simple_iff {C : Type u}  {X : C} [HasZeroMorphisms C] :
    Simple X ↔ ∀ (Y) (f : Y ⟶ X) [inst : Mono f], IsIso f ↔ f ≠ 0 := by
  constructor <;> intro hX
  · cases hX; tauto
  · exact Simple.mk @hX

/- Massive TODO: Define FdRep.ρ.asModule, or at least alias it -/
abbrev FdRep.asModule (V : FdRep k G) := V.toRep.ρ.asModule

#check FdRep
theorem FdRep.simple_iff_simple_toRep {V : FdRep k G} : Simple V ↔ Simple V.toRep := by
  simp_rw [simple_iff]
  constructor <;> intro h W f f_mono
  · done
  · specialize h W.toRep
    let f : W.ρ.asModule →ₗ[k⟦G⟧] V.ρ.asModule := f
    let f' : W.toRep ⟶ V.toRep := f

theorem FdRep.simple_iff {V : FdRep k G} : Simple V ↔ IsSimpleModule k⟦G⟧ V.asModule :=
  simple_iff_simple_toRep.trans Rep.simple_iff

theorem FdRep.thing {V : FdRep k G} (hV : IsSimpleModule k⟦G⟧ V.asModule) :
    IsSimpleModule k⟦G⟧ V.toRep.ρ.asModule := by
  sorry

-- One dimensional representations are simple i.e. irreducible
-- Of course hf can also be dim(V / k[G])
theorem FdRep.rank_one_is_simple_yay
    (V : FdRep k G) (hf : finrank k⟦G⟧ V.toRep.ρ.asModule = 1) : Simple V :=
  FdRep.simple_iff.mpr <| FdRep.thing <| isSimpleModule_iff_finrank_eq_one.mpr hf

end help_me_consequence

--------------------------------------------------------------------------------------------

/- Tada! You have made it here. Here are some results you can enjoy! -/

section tada

-- k cannot be in any universe
variable {n : ℕ} (hn : 1 < n) {k : Type} [Field k] {ζ : k} (hζ : ζ ∈ primitiveRoots n k)

-- this proof should work with just `NeZero n`
lemma zeta_pow_mod_eq {k : ℕ} : ζ ^ (k % n) = ζ ^ k := by
  nth_rw 2 [← Nat.mod_add_div k n]
  rw [mem_primitiveRoots (zero_lt_one.trans hn)] at hζ
  rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

/-- Like `zpowersHom` but for `ZMod` and primitive roots. -/
@[simps]
def zmodpowersHom {ζ : k} (hζ : ζ ∈ primitiveRoots n k) : Multiplicative (ZMod n) →* k where
  toFun := fun mk => (ζ ^ mk.toAdd.val)
  map_one' := by simp
  map_mul' := fun x y => by
    simp
    rw [← pow_add, ← zeta_pow_mod_eq hn hζ, @ZMod.val_add _ ⟨by omega⟩, zeta_pow_mod_eq hn hζ]
    exact zeta_pow_mod_eq hn hζ

def Representation.cyc_rep : Representation k (Multiplicative (ZMod n)) k :=
  (Algebra.lsmul k k k).toMonoidHom.comp (zmodpowersHom hn hζ)

noncomputable def cyc_rep : FdRep k (Multiplicative (ZMod n)) :=
  FdRep.of (Representation.cyc_rep hn hζ)

theorem cyc_rep_irreducible : Simple (_root_.cyc_rep hn hζ) :=
  FdRep.rank_one_is_simple_yay _ <| finrank_self k

end tada

--------------------------------------------------------------------------------------------

section random

universe w w'
-- I want to prove that FGModuleCat R doesn't have all finite colimits when R is not Noetherian
variable {R : Type u} [Ring R]

example (hR : ¬IsNoetherianRing R) : ¬HasFiniteLimits (FGModuleCat R) := by
  intro hR_limits

-- Quotient modules are finitely generated
variable {R : Type u} [Ring R] (M : Type u) [AddCommGroup M] [Module R M] (N : Submodule R M)
example (hM : Module.Finite R M) : Module.Finite R (M ⧸ N) := by
  exact Finite.quotient R N

end random
