
section Logic

theorem andSymm : p ∧ q → q ∧ p := λ (And.intro x y) => And.intro y x

theorem andComm : p ∧ q ↔ q ∧ p := Iff.intro andSymm andSymm

theorem orSymm : p ∨ q → q ∨ p
| Or.inl x => Or.inr x
| Or.inr x => Or.inl x

theorem orComm : p ∨ q ↔ q ∨ p := Iff.intro orSymm orSymm

end Logic

def Set (α : Type u) : Type u := α → Prop

@[reducible]
def Set.mk (p : α → Prop) : Set α := p

class HasMem (α : outParam $ Type u) (β : Type v) where
    mem : α → β → Prop

infix:50 " ∈ " => HasMem.mem

instance : HasMem α (Set α) where
    mem x s := s x

syntax "{ " ident (" : " term)? " | " term " }" : term

macro_rules
  | `({ $x : $type | $p }) => `(Set.mk (λ ($x:ident : $type) => $p))
  | `({ $x | $p })         => `(Set.mk (λ ($x:ident : _) => $p))

abbrev setOf (b : β) [HasMem α β] : Set α := {x | x ∈ b}


namespace Set

theorem ext {s t : Set α} (h : (x : α) → x ∈ s ↔ x ∈ t) : s = t := by
    funext x
    exact propext (h x)

def univ {α : Type u} : Set α := λ _ => True

def subset (s t : Set α) : Prop := ∀ {x}, x ∈ s → x ∈ t
def inter (s t : Set α) : Set α := {x | x ∈ s ∧ x ∈ t}
def union (s t : Set α) : Set α := {x | x ∈ s ∨ x ∈ t}

infixl:70 " ∩ " => inter
infixl:65 " ∪ " => union
infix:50 " ⊆ " => subset

@[simp] theorem memUniv (a : α) : a ∈ univ := trivial

@[simp] theorem memInter (x : α) (s t : Set α) : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := Iff.rfl
@[simp] theorem memUnion (x : α) (s t : Set α) : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := Iff.rfl

theorem interComm (s t : Set α) : s ∩ t = t ∩ s := by
    apply ext
    simp
    intro
    rw andComm
    exact Iff.rfl

theorem unionComm (s t : Set α) : s ∪ t = t ∪ s := by
    apply ext
    simp
    intro
    rw orComm
    exact Iff.rfl

end Set