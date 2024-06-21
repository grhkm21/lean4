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

--------------------------------------------------------------------------------------------

section help_me_consequence

/- Massive TODO: Define FdRep.ρ.asModule, or at least alias it -/

abbrev FdRep.asModule (V : FdRep k G) := V.toRep.ρ.asModule

theorem FdRep.simple_iff_simple_toRep {V : FdRep k G} : Simple V ↔ Simple V.toRep := by
  sorry

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
@grhkm21
Comment

