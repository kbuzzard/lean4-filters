import Lean4_filters.lattice

class HasMem (α : outParam $ Type u) (β : Type v) where
    mem : α → β → Prop

infix:50 " ∈ " => HasMem.mem

def Set (α : Type u) := α → Prop

namespace Set

variable {α : Type u}

instance : HasMem α (Set α) := ⟨λ a s => s a⟩

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext $ λ x=> propext $ h x

instance : HasLessEq (Set α) := ⟨λ s t => ∀ {x : α}, x ∈ s → x ∈ t⟩
  
instance : PartialOrder (Set α) where
  refl := λ s x => id 
  antisymm := λ s t hst hts => ext $ λ x => ⟨hst, hts⟩
  trans := λ s t u hst htu x hxs => htu $ hst hxs

instance : HasSup (Set α) := ⟨λ s t x => x ∈ s ∨ x ∈ t⟩

instance : HasInf (Set α) := ⟨λ s t x => x ∈ s ∧ x ∈ t⟩

#print Or.rec
instance : Lattice (Set α) where
  /-
    le_sup_left (a b : P) : a ≤ a ⊔ b
    le_sup_right (a b : P) : b ≤ a ⊔ b
    sup_le (a b c : P) : a ≤ c → b ≤ c → a ⊔ b ≤ c
    inf_le_left (a b : P) : a ⊓ b ≤ a
    inf_le_right (a b : P) : a ⊓ b ≤ b
    le_inf (a b c : P) : a ≤ b → a ≤ c → a ≤ b ⊓ c
  -/
  le_sup_left := λ a b x => Or.inl
  le_sup_right := λ a b x => Or.inr
  sup_le := λ a b c hac hbc x hx => Or.rec (_) _ _
  inf_le_left := λ a b x x=> _
  inf_le_right := λ a b x => _
  le_inf := λ a b c hab hac x => _

end Set


