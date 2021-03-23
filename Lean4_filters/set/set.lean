import Lean4_filters.lattice
import Lean4_filters.tactics

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

instance : Lattice (Set α) where
  leSupLeft := λ a b x => Or.inl
  leSupRight := λ a b x => Or.inr
  supLe := λ a b c hac hbc x => Or.rec hac hbc
  infLeLeft := λ a b x hx => hx.1
  infLeRight := λ a b x hx => hx.2
  leInf := λ a b c hab hac x hx => ⟨hab hx, hac hx⟩

example : Lattice (Set α) where
  leSupLeft := by
    intros a b x hx;
    left;
    assumption;
  leSupRight := by
    intros a b x;
    intro hx;
    right;
    assumption;
  supLe := by
    intros a b c hac hbc x hx;
    cases hx;
      apply hac; assumption
    apply hbc; assumption
  infLeLeft := by
    intros a b x hx;
    cases hx; -- no "with" :-(
    assumption;
  infLeRight := by
    intros _ _ _ hx;
    cases hx;
    assumption;
  leInf := by
    intro a b c hab hac x hx;
    split;
      exact hab hx;
    exact hac hx;

end Set

