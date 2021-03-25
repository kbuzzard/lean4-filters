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

def galoisConnection {α β} [PartialOrder α] [PartialOrder β]
  (l : α → β) (u : β → α) := ∀ a b,  l a ≤ b ↔ a ≤ u b

  #check Nat