import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.RingTheory.SimpleModule
import Mathlib.CategoryTheory.Simple
import Mathlib.Order.BoundedOrder
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

open LinearMap Module Submodule Representation FiniteDimensional Function Pointwise CategoryTheory
  MonoidAlgebra JordanHolderModule Limits

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

instance {V : Rep k G} [Simple V] : Nontrivial V.ρ.asModule := by
  change Nontrivial V
  infer_instance

end instances

--------------------------------------------------------------------------------------------

section help_me_theory

variable {V W : Rep k G}

-- This should be in Mathlib
noncomputable def FdRep.toRep (V : FdRep k G) : Rep k G :=
  (forget₂ (FdRep k G) (Rep k G)).obj V

-- Rewrite lemma
def Rep.smul_def {ρ : Representation k G V} (g : MonoidAlgebra k G) (x : ρ.asModule) :
    g • x = (ρ.asAlgebraHom g) x := by
  rfl

-- This converts Rep Hom to Module LinearMap
def lift_rep_hom' (f : V ⟶ W) :
    V.ρ.asModule →ₗ[MonoidAlgebra k G] W.ρ.asModule := by
  let f_mod : V.ρ.asModule →+ W.ρ.asModule := (f.hom : V.V →+ W.V)
  use f_mod, fun g x ↦ ?_
  simp
  obtain ⟨⟨f', hf'₁⟩, hf'₂⟩ := f
  simp [Rep.smul_def, asAlgebraHom, lift_apply']
  rw [map_finsupp_sum]
  congr! with g c
  change f'.toFun _ = c • (W.ρ g) (f'.toFun x)
  rw [hf'₁]
  congr 1
  exact Rep.hom_comm_apply ⟨⟨f', hf'₁⟩, hf'₂⟩ g x

-- This converts Module LinearMap to Rep Hom
def lift_module_hom (f : V.ρ.asModule →ₗ[MonoidAlgebra k G] W.ρ.asModule) : V ⟶ W := by
  let f' : V.V →+ W.V := (f : V.ρ.asModule →+ W.ρ.asModule)
  use ⟨f', ?_⟩, ?_
  · sorry
  · sorry

-- Create category hom from G-action thing
-- V.ρ.asModule can be replaced by V but that will make make_hom₂ more painful
def make_hom₁ (f : G → W.ρ.asModule →ₗ[k] V.ρ.asModule) : W ⟶ V := by
  sorry

-- Create category hom from ring hom
def make_hom₂ (f : W.ρ.asModule →ₗ[MonoidAlgebra k G] V.ρ.asModule) : W ⟶ V := by
  apply make_hom₁
  sorry

def make_hom₃ (f : W.ρ.asModule →ₗ[MonoidAlgebra k G] V.ρ.asModule) :
    (ModuleCat.of k W.ρ.asModule) ⟶ (ModuleCat.of k V.ρ.asModule) :=
  ModuleCat.ofHom (LinearMap.restrictScalars _ f)

#check Rep.ofModuleMonoidAlgebra.map

#check Action.Hom
def make_hom₄ (f : W.ρ.asModule →ₗ[MonoidAlgebra k G] V.ρ.asModule) : W ⟶ V := by
  refine ⟨make_hom₃ f, ?_⟩
  intro g
  ext x
  simp [make_hom₃]
  sorry

theorem Rep.isSimpleModule_of_Simple [hV : Simple V] :
      IsSimpleModule (MonoidAlgebra k G) V.ρ.asModule := by
  have hV' := fun Y ↦ hV.mono_isIso_iff_nonzero (Y := Y)
  apply IsSimpleOrder.mk
  /- Prove that all k[G]-submodule of V are either ⊥ or ⊤
    Potential strategy:
    1. Construct the (W' : Rep k G) attached to W (done)
    2. Construct a Rep hom (Action.Hom) W' ⟶ V, which should be easy but I can't??
    3. Prove this hom is Mono, i.e. injective, which is again easy
    4. Conclude with that -/
  intro W
  /- step 1 -/
  specialize hV' <| ofModuleMonoidAlgebra.obj $ ModuleCat.of (MonoidAlgebra k G) W
  /- step 2 -/
  -- uhhhh doesn't work. I give up
  /- specialize hV' <| make_hom₄ (k := k) (G := G) W.subtype -/

theorem Rep.is_simple_iff_isSemiSimple {G : Type u} [Group G] {V : Rep k G} :
    Simple V ↔ IsSimpleModule (MonoidAlgebra k G) V.ρ.asModule := by
  constructor <;> intro hV
  · exact Rep.isSimpleModule_of_Simple
  · obtain ⟨t, ht⟩ := show ∃ t : V.ρ.asModule, t ≠ 0 by
      obtain ⟨⟨x, y, hxy⟩⟩ := IsSimpleModule.nontrivial (MonoidAlgebra k G) V.ρ.asModule
      have : x ≠ 0 ∨ y ≠ 0 := by contrapose! hxy; rw [hxy.left, hxy.right]
      cases this <;> exact ⟨_, by assumption⟩
    constructor
    intro W f hf
    set im : Submodule _ V.ρ.asModule := LinearMap.range (toModuleMonoidAlgebra.map f) with h_im
    have : im = ⊥ ∨ im = ⊤ := eq_bot_or_eq_top im
    constructor <;> intro hf'
    · obtain ⟨⟨inv, inv_comm⟩, left_inv, right_inv⟩ := hf'
      rintro rfl
      have : (⟨0, _⟩ : Action.Hom V V).hom = (𝟙 V : Action.Hom V V).hom := congrArg _ right_inv
      exact ht (congrArg (fun f ↦ f t) this).symm
    · have (x) : f.hom x ∈ range (toModuleMonoidAlgebra.map f) := by
        -- simp only infer an instance that I can't get rid of manually without much pain
        simp only [mem_range]
        exact ⟨x, rfl⟩
      have : im ≠ ⊥ := by
        contrapose! hf'
        simp_rw [← h_im, hf', mem_bot] at this
        ext x
        exact this x
      have : im = ⊤ := by tauto
      rw [LinearMap.range_eq_top] at this
      have : Epi f := by
        -- I can't category theory
        -- rw [ConcreteCategory.epi_iff_surjective_of_preservesPushout]
        sorry
      /- Ok so now I want to say that f is isomorphism because f is injective and bijective.
        Give up. -/
      -- rw [@ConcreteCategory.isIso_iff_bijective _ _ _ ?_]
      sorry

end help_me_theory

--------------------------------------------------------------------------------------------

section help_me_consequence

/- lol there is no FdRep.ρ.asModule -/
theorem FdRep.is_simple_iff_is_simple_toRep {V : FdRep k G} : Simple V ↔ Simple V.toRep := by
  sorry

theorem FdRep.is_simple_iff_isSemiSimple {V : FdRep k G} :
    Simple V ↔ IsSimpleModule (MonoidAlgebra k G) V.toRep.ρ.asModule :=
  is_simple_iff_is_simple_toRep.trans Rep.is_simple_iff_isSemiSimple

theorem FdRep.thing {V : FdRep k G} (hV : IsSimpleModule k V) :
    IsSimpleModule (MonoidAlgebra k G) V.toRep.ρ.asModule := by
  sorry

-- One dimensional representations are simple i.e. irreducible
-- Of course hf can also be dim(V / k[G])
theorem FdRep.rank_one_is_simple_yay (V : FdRep k G) (hf : finrank k V = 1) : Simple V :=
  FdRep.is_simple_iff_isSemiSimple.mpr <| FdRep.thing <| isSimpleModule_iff_finrank_eq_one.mpr hf

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

