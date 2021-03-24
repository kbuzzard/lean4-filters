-- import Lean4_filters.lattice.CompleteLattice
-- unknown package Lean4_filters
import Lean4_filters.lattice.completeLattice

variable {α : Type u}

instance : CompleteLattice (Set α) := {
  top := Set.univ
  leTop := by
    intro s x hx;
    trivial;
  bot := Set.empty
  botLe := by
    intro s x hx;
    cases hx;
  supr := λ C x => ∃ s, s ∈ C ∧ x ∈ s   
  leSupr := λ _ s hs _ hx => ⟨s, hs, hx⟩ -- why doesn't `supr` appear here, but instead have the unfolded defn?
  suprLe := λ C s hs x ⟨t, ht, hx⟩ => hs t ht hx
  infi := λ C x => ∀ s, s ∈ C → x ∈ s
  infiLe := λ C s hs x h => h s hs 
  leInfi := λ C s h x hx t ht => h t ht hx
}