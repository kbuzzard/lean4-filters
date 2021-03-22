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
  le_sup_left (a b : P) : a ≤ a ⊔ b
  le_sup_right (a b : P) : b ≤ a ⊔ b
  sup_le (a b c : P) : a ≤ c → b ≤ c → a ⊔ b ≤ c
  inf_le_left (a b : P) : a ⊓ b ≤ a
  inf_le_right (a b : P) : a ⊓ b ≤ b
  le_inf (a b c : P) : a ≤ b → a ≤ c → a ≤ b ⊓ c

