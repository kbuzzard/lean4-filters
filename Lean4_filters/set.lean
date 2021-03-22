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
  
class PartialOrder (β : Type u) extends HasLessEq β where
  refl (s : β) : s ≤ s
  antisymm (s t : β) : s ≤ t → t ≤ s → s = t
  trans (s t u : β) : s ≤ t → t ≤ u → s ≤ u

instance : PartialOrder (Set α) where
  refl := λ s x => id 
  antisymm := λ s t hst hts => ext $ λ x => ⟨hst, hts⟩
  trans := λ s t u hst htu x hxs => htu $ hst hxs

end Set


