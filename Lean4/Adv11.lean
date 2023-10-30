import Mathlib.Tactic

open Nat Finset

variable (A B X : Finset ℕ) {α : Type*} [LinearOrder α]

def multiples (a : ℕ) := X.filter (fun x ↦ a ∣ x)

def PredElement (a : ℕ) := ¬Even (multiples B a).card

instance : DecidablePred (PredElement X) := by intro ; exact Not.decidable

def Pred : Finset ℕ := X.filter $ PredElement B

theorem min_not_mem {X : Finset α} (hm : ∀ a ∈ X, m < a) : m ∉ X := fun a ↦ (hm m a).false

theorem max_not_mem {X : Finset α} (hm : ∀ a ∈ X, a < m) : m ∉ X := fun a ↦ (hm m a).false

theorem card_filter_lt (s : Finset α) (p : α → Prop) [DecidablePred p] (h' : ∃ a ∈ s, ¬p a) :
    (s.filter p).card < s.card := by
  /- TODO: Try filter_ssubset -/
  let ⟨a, ha⟩ := h'
  nth_rewrite 2 [(filter_union_filter_neg_eq p s).symm]
  rw [card_disjoint_union]
  · simp only [not_not, lt_add_iff_pos_right, card_pos]
    use a
    rwa [mem_filter]
  · exact disjoint_filter_filter_neg s s p

theorem ind_max {p : Finset α → Prop} (s : Finset α) (hz : p ∅)
    (hi : ∀ m t (hm : ∀ a, a ∈ t → a < m), p t → p (cons m t <| max_not_mem hm)) : p s := by
  by_cases hs : s.Nonempty
  rotate_right
  · simpa only [not_nonempty_iff_eq_empty.mp hs]
  · let m := s.max' hs
    set s' := s.filter (fun x ↦ x ≠ m) with hs'
    have h₁ : ∀ a, a ∈ s' → a < m := by
      simp_rw [Finset.mem_filter]
      intro a ⟨ha₁, ha₂⟩
      exact lt_of_le_of_ne (le_max' s a ha₁) ha₂
    have : s'.card < s.card := by
      apply card_filter_lt
      use m
      exact ⟨max'_mem s hs, not_ne_iff.mpr rfl⟩
    have h₃ : p s' := ind_max s' hz hi
    specialize hi m s' h₁ h₃
    convert hi
    apply Subset.antisymm <;> rw [subset_iff] <;> intro x hx
    · rw [mem_cons, hs']
      by_cases hx' : x = m
      · left
        rw [hx']
      · right
        rw [mem_filter]
        exact ⟨hx, hx'⟩
    · rw [mem_cons] at hx
      cases' hx with hx hx
      · rw [hx]
        exact max'_mem s hs
      · exact mem_of_mem_filter x hx
termination_by _ s _ _ => s.card

theorem ind_min {p : Finset α → Prop} (s : Finset α) (hz : p ∅)
    (hi : ∀ m t (hm : ∀ a, a ∈ t → m < a), p t → p (cons m t <| min_not_mem hm)) : p s := by
  by_cases hs : s.Nonempty
  rotate_right
  · simpa only [not_nonempty_iff_eq_empty.mp hs]
  · let m := s.min' hs
    set s' := s.filter (fun x ↦ x ≠ m) with hs'
    have h₁ : ∀ a, a ∈ s' → m < a := by
      simp_rw [Finset.mem_filter]
      intro a ⟨ha₁, ha₂⟩
      refine lt_of_le_of_ne (min'_le s a ha₁) ha₂.symm
    have : s'.card < s.card := by
      apply card_filter_lt
      use m
      exact ⟨min'_mem s hs, not_ne_iff.mpr rfl⟩
    have h₃ : p s' := ind_min s' hz hi
    specialize hi m s' h₁ h₃
    convert hi
    apply Subset.antisymm <;> rw [subset_iff] <;> intro x hx
    · rw [mem_cons, hs']
      by_cases hx' : x = m
      · left
        rw [hx']
      · right
        rw [mem_filter]
        exact ⟨hx, hx'⟩
    · rw [mem_cons] at hx
      cases' hx with hx hx
      · rw [hx]
        exact min'_mem s hs
      · exact mem_of_mem_filter x hx
termination_by _ s _ _ => s.card

lemma filter_eq_filter {A : Finset α} (h : ∀ a ∈ A, f a = g a) [DecidablePred f] [DecidablePred g] :
    A.filter f = A.filter g := by
  apply Subset.antisymm
  <;> apply subset_iff.mpr
  <;> intro x hx
  <;> have h₁ := mem_of_mem_filter x hx
  <;> have h₂ := h x h₁
  <;> simp only [mem_filter, (mem_filter.mp hx).right, h₁, h₂, ←h₂]

lemma wont_change (a : ℕ) (ha₁ : ∀ x ∈ X, a < x) (ha₂ : 0 < a) : Pred ({a} ∪ B) X = Pred B X := by
  apply filter_eq_filter
  intro x hx
  have : ¬(x ∣ a) := by by_contra' hx' ; linarith [le_of_dvd ha₂ hx', ha₁ x hx]
  simp_rw [PredElement, multiples, filter_union, filter_singleton, this, ite_false, empty_union]

lemma predElement_cons_self (hm : m ∉ B) : PredElement (cons m B hm) m = ¬PredElement B m := by
  simp_rw [PredElement, multiples, filter_cons, dvd_refl, ite_true]
  rw [card_disjUnion, card_singleton, add_comm 1, even_add_one]

lemma insert_filter (h : m ∈ A) : insert m (A.filter (fun x ↦ x ≠ m)) = A := by
  change {m} ∪ _ = _
  rw [←show A.filter (fun x ↦ x = m) = {m} by simp_rw [filter_eq', h, ite_true]]
  apply filter_union_filter_neg_eq

theorem A11 (hX : 0 ∉ X) (hA : A ⊆ X) : ∃ B, B ⊆ X ∧ Pred B X = A := by
  /- Strategy: Induction on min B? -/
  induction' X using ind_min with m X hm hind generalizing A
  · use ∅, Subset.rfl
    rw [Pred, subset_empty.mp hA, filter_empty]
  · /- Strategy: Use induction hypothesis on A \ {m}, then construct like the answer does -/
    set A' := A.filter (fun x ↦ x ≠ m) with hA'
    have h₁ : 0 ∉ X := by
      rw [mem_cons, not_or] at hX
      exact hX.right
    have h₂ : A' ⊆ X := by
      rw [hA', subset_iff]
      intro x hx
      cases' mem_cons.mp $ mem_of_subset hA $ mem_of_mem_filter x hx with h
      · rw [h, mem_filter] at hx
        exact (hx.right $ refl _).elim
      · trivial
    have hm'₁ : 0 < m := by
      by_contra' hm₁
      absurd hX
      rw [mem_cons]
      left
      linarith
    let ⟨B', ⟨hB'₁, hB'₂⟩⟩ := hind A' h₁ h₂
    have hB' := subset_trans hB'₁ $ subset_cons $ min_not_mem hm
    have hB''₂ := hB'₂
    rw [Pred] at hB''₂
    have hm'₂ : m ∉ B' := fun hm'₂ ↦ min_not_mem hm $ mem_of_subset hB'₁ hm'₂
    /- We construct B as B' or B' ∪ {m}. The proof is highly repetitive -/
    by_cases hm₁ : m ∈ A <;> by_cases hm₂ : (PredElement B' m)
    rotate_right
    /- First two goals have the same proof -/
    iterate 2
      use B', hB'
      simp only [Pred, filter_cons, hm₂, ite_true, ite_false, hB''₂, disjUnion_eq_union]
      nth_rewrite 2 [←filter_union_filter_neg_eq (fun x => x = m) A]
      congr
      simp only [filter_eq', hm₁, ite_true, ite_false]
    /- The beginning of the other two goals is the same -/
    all_goals
      use cons m B' hm'₂, cons_subset.mpr ⟨mem_cons_self _ _, hB'⟩, ?_
      simp_rw [Pred, filter_cons, predElement_cons_self, hm₂]
      simp only [ite_false, ite_true, cons_eq_insert]
      change disjUnion _ (Pred ({m} ∪ _) _) _ = _
    · rw [singleton_disjUnion, cons_eq_insert, wont_change B' X m hm hm'₁, hB'₂]
      exact insert_filter _ hm₁
    · rw [empty_disjUnion, wont_change B' X m hm hm'₁, hB'₂, filter_eq_self]
      exact fun _ hx ↦ ne_of_mem_of_not_mem hx hm₁
