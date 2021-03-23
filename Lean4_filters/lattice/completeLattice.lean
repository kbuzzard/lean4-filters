import Lean4_filters.tactics.basic
import Lean4_filters.set.basic

class CompleteLattice (P : Type u) extends Lattice P, HasTop P, HasBot P where
  leTop : ∀ (a : P), a ≤ ⊤
  botLe : ∀ (a : P), ⊥ ≤ a
  Supr : Set P → P
  Infi : Set P → P
  leSupr : ∀ (s : Set P) (a : P), a ∈ s → a ≤ Supr s
  suprLe : ∀ (s : Set P) (a : P), (∀ (b : P), b ∈ s → b ≤ a) → Supr s ≤ a
  InfiLe : ∀ (s : Set P) (a : P), a ∈ s → Infi s ≤ a
  LeInfi : ∀ (s : Set P) (a : P), (∀ (b : P), b ∈ s → a ≤ b) → a ≤ Infi s
