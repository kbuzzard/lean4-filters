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
  le_sup_left := λ a b x => Or.inl
  le_sup_right := λ a b x => Or.inr
  sup_le := λ a b c hac hbc x => Or.rec hac hbc
  inf_le_left := λ a b x hx => hx.1
  inf_le_right := λ a b x hx => hx.2
  le_inf := λ a b c hab hac x hx => ⟨hab hx, hac hx⟩

example : Lattice (Set α) where
  le_sup_left := by
    intros a b x hx;
    left;
    assumption;
  le_sup_right := by
    intros a b x;
    intro hx;
    right;
    assumption;
  sup_le := by
    intros a b c hac hbc x hx;
    cases hx;
      apply hac; assumption
    apply hbc; assumption
  inf_le_left := by
    intros a b x hx;
    cases hx; -- no "with" :-(
    assumption;
  inf_le_right := by
    intros _ _ _ hx;
    cases hx;
    assumption;
  le_inf := by
    intro a b c hab hac x hx;
    split;
      exact hab hx;
    exact hac hx;

end Set


