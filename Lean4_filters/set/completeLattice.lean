-- import Lean4_filters.lattice.CompleteLattice
-- unknown package Lean4_filters
import Lean4_filters.lattice.completeLattice

variable {α : Type u}

#check True

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
  leSupr := sorry
  suprLe := sorry
  infi := λ C x => ∀ s, s ∈ C ∧ x ∈ s   
  infiLe := sorry
  leInfi := sorry
}