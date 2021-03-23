class PartialOrder (P : Type u) extends HasLessEq P where
  refl (s : P) : s ≤ s
  antisymm (s t : P) : s ≤ t → t ≤ s → s = t
  trans (s t u : P) : s ≤ t → t ≤ u → s ≤ u

class HasSup (P : Type u) where
    sup : P → P → P

infix:65 " ⊔ " => HasSup.sup

class HasInf (P : Type u) where
  inf : P → P → P

infix:70 " ⊓ " => HasInf.inf

class Lattice (P : Type u) extends PartialOrder P, HasSup P, HasInf P where
  leSupLeft (a b : P) : a ≤ a ⊔ b
  leSupRight (a b : P) : b ≤ a ⊔ b
  supLe (a b c : P) : a ≤ c → b ≤ c → a ⊔ b ≤ c
  infLeLeft (a b : P) : a ⊓ b ≤ a
  infLeRight (a b : P) : a ⊓ b ≤ b
  leInf (a b c : P) : a ≤ b → a ≤ c → a ≤ b ⊓ c

class HasTop (P : Type u) where
  top : P

notation "⊤" => HasTop.top

class HasBot (P : Type u) where
  bot : P

notation "⊥" => HasBot.bot

#exit
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