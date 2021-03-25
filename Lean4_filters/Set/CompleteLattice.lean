import Lean4_filters.Lattice.CompleteLattice

variable {α : Type u}

instance : CompleteLattice (Set α) := {
  top := Set.univ
  leTop := λ s x hx => True.intro
  bot := Set.empty
  botLe := λ s x hx => False.elim hx
  supr := λ C x => ∃ s, s ∈ C ∧ x ∈ s   
  leSupr := λ C s hsC x hxs => ⟨s, hsC, hxs⟩
  suprLe := λ C s h1 x ⟨t, htC, hxt⟩ => h1 t htC hxt
  infi := λ C x => ∀ s, s ∈ C → x ∈ s   
  infiLe := λ X s hsX a h => h _ hsX
  leInfi := λ C s h a has t htC => h t htC has
}

example : CompleteLattice (Set α) := {
  top := Set.univ
  leTop := by
    intros s x hx;
    trivial;
  bot := Set.empty
  botLe := by
    intros s x hx;
    cases hx;
  supr := λ C x => ∃ s, s ∈ C ∧ x ∈ s   
  leSupr := by
    intros C s hsC x hxs;
    exact ⟨s, hsC, hxs⟩;
  suprLe := by
    intros C s h1 x h;
    let ⟨t, htC, hxt⟩ := h;
    exact h1 t htC hxt;
  infi := λ C x => ∀ s, s ∈ C → x ∈ s   
  infiLe := by
    intro X s hsX a h;
    exact h _ hsX;
  leInfi := by
    intro C s h a has t htC;
    exact h t htC has
}

