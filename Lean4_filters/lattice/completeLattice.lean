/-
class CompleteLattice (P : Type u) extends Lattice P, HasTop P, HasBot P where
  leTop : ∀ (a : P), a ≤ ⊤
  botLe : ∀ (a : P), ⊥ ≤ a
  Sup : set α → α
  Inf : set α → α
le_Sup : ∀ (s : set α) (a : α), a ∈ s → a ≤ complete_lattice.Sup s
Sup_le : ∀ (s : set α) (a : α), (∀ (b : α), b ∈ s → b ≤ a) → complete_lattice.Sup s ≤ a
Inf_le : ∀ (s : set α) (a : α), a ∈ s → complete_lattice.Inf s ≤ a
le_Inf : ∀ (s : set α) (a : α), (∀ (b : α), b ∈ s → a ≤ b) → a ≤ complete_lattice.Inf s
-/