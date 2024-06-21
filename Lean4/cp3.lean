import Mathlib.GroupTheory.GroupAction.SubMulAction

open scoped Pointwise
open Set Group Function

variable {G H : Type*} [Group G] [Group H] (f : G →* H)

noncomputable def preimageEquiv (g : G) : f ⁻¹' {f g} ≃ f ⁻¹' {1} := by
  have : f ⁻¹' {f g} = g • f.ker := by
    ext t
    simp [MonoidHom.eq_iff]
    change g⁻¹ • t ∈ (f.ker : Set _) ↔ _
    rw [← mem_smul_set_iff_inv_smul_mem (a := g) (x := t) (A := f.ker)]
  rw [this]
  exact (Equiv.Set.imageOfInjOn (fun h : G ↦ g • h) f.ker (MulAction.injective g).injOn).symm

noncomputable def preimageEquiv' (hf : Surjective f) (h h' : H) : f ⁻¹' {h} ≃ f ⁻¹' {h'} := by
  obtain ⟨g, hg⟩ := Classical.indefiniteDescription _ (hf h)
  obtain ⟨g', hg'⟩ := Classical.indefiniteDescription _ (hf h')
  subst hg hg'
  exact (preimageEquiv f g).trans (preimageEquiv f g').symm

