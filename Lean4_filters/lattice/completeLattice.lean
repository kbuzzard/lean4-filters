import Lean4_filters.tactics.basic
import Lean4_filters.set.basic

class HasTop (P : Type u) where
  top : P

notation "⊤" => HasTop.top

class HasBot (P : Type u) where
  bot : P

notation "⊥" => HasBot.bot

class CompleteLattice (P : Type u) extends Lattice P, HasTop P, HasBot P where
  leTop : ∀ (a : P), a ≤ ⊤
  botLe : ∀ (a : P), ⊥ ≤ a
  supr : Set P → P
  infi : Set P → P
  leSupr : ∀ (s : Set P) (a : P), a ∈ s → a ≤ supr s
  suprLe : ∀ (s : Set P) (a : P), (∀ (b : P), b ∈ s → b ≤ a) → supr s ≤ a
  infiLe : ∀ (s : Set P) (a : P), a ∈ s → infi s ≤ a
  leInfi : ∀ (s : Set P) (a : P), (∀ (b : P), b ∈ s → a ≤ b) → a ≤ infi s
