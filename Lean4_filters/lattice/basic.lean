class PartialOrder (P : Type u) extends HasLessEq P where
  refl (s : P) : s ≤ s
  antisymm (s t : P) : s ≤ t → t ≤ s → s = t
  trans (s t u : P) : s ≤ t → t ≤ u → s ≤ u

@[simp] theorem PartialOrder.refl_self {P : Type _} [PartialOrder P] (s : P) : s ≤ s := PartialOrder.refl _

theorem LessEq.trans {P : Type _} [PartialOrder P] {x y z : P} : x ≤ y → y ≤ z → x ≤ z := PartialOrder.trans _ _ _

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

namespace Lattice

open PartialOrder

variable {P : Type _} [Lattice P] (a : P)

@[simp] theorem sup_self : a ⊔ a = a := antisymm _ _ (supLe _ _ _ (refl _) (refl _)) (leSupLeft _ _)

@[simp] theorem inf_self : a ⊓ a = a := antisymm _ _ (infLeLeft _ _) (leInf _ _ _ (refl _) (refl _))

end Lattice
