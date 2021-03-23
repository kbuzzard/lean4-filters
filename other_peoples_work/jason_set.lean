theorem impNot {p q : Prop} : p → ¬ q ↔ ¬ (p ∧ q) := 
  ⟨ λ hpq h => hpq h.1 h.2, λ h hp hq => h <| And.intro hp hq ⟩  

theorem Exists.impNot {p q : α → Prop} : (∃ x, p x → ¬ q x) ↔ ∃ x, ¬ (p x ∧ q x) := by 
  apply Iff.intro
  intro h
  cases h with | intro x hx => 
  { exact ⟨ x, λ hs => hx hs.1 hs.2 ⟩ }
  intro h 
  cases h with | intro x hx => 
  { exact ⟨ x, λ hpx hqx => hx <| And.intro hpx hqx ⟩ }

namespace Classical

theorem contrapositive {p q : Prop} : (¬ q → ¬ p) → p → q := 
  λ hqp hp => match em q with 
    | Or.inl h => h
    | Or.inr h => False.elim <| hqp h hp
  
theorem notNot {p : Prop} : ¬ ¬ p ↔ p := by 
  apply Iff.intro
  { intro hp; cases em p with 
    | inl   => assumption
    | inr h => exact False.elim <| hp h }
  { exact λ hp hnp => False.elim <| hnp hp }

theorem notForall {p : α → Prop} : (¬ ∀ x, p x) → ∃ x, ¬ p x := by 
  { apply contrapositive; intro hx; rw notNot; intro x;
    cases em (p x); { assumption }
      { apply False.elim <| hx <| Exists.intro x _; assumption } }  

theorem notAnd {p q : Prop} : p ∧ ¬ q ↔ ¬ (p → q) := by
  apply Iff.intro
  { exact λ h himp => h.2 <| himp h.1 }
  { intro h; apply And.intro;
    { revert h; apply contrapositive; rw notNot;
      exact λ hnp hp => False.elim <| hnp hp }
    { exact λ hq => h <| λ _ => hq } }

theorem Exists.notAnd {p q : α → Prop} : 
  (∃ x, p x ∧ ¬ q x) ↔ ∃ x, ¬ (p x → q x) := by
  apply Iff.intro
  { intro h;
    let ⟨ x, ⟨ hp, hnq ⟩ ⟩ := h;
    exact Exists.intro x λ h => hnq <| h hp }
  { intro h;
    let ⟨ x, hx ⟩ := h;
    apply Exists.intro x;
    apply And.intro;
    { revert hx; apply contrapositive;
      exact λ hpx hpq => hpq λ hp => False.elim <| hpx hp }
    { intro foo;
      apply hx;
      intro bar;
      assumption; } }

end Classical

def Set (α : Type u) := α → Prop

def setOf (p : α → Prop) : Set α := p

namespace Set

instance : EmptyCollection (Set α) := ⟨ λ x => False ⟩ 

variable {zzz : Type u}

variable {α : Type u}
variable {s : Set α}

def mem (a : α) (s : Set α) := s a

infix:55 "∈" => Set.mem
notation:55 x "∉" s => ¬ x ∈ s

instance : CoeSort (Set α) (Type u) where 
  coe s := Subtype s

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := 
  funext <| λ x => propext <| h x

-- Declaring the index category
declare_syntax_cat index
syntax ident : index
syntax ident ":" term : index 
syntax ident "∈" term : index

-- Notation for sets
syntax "{" index "|" term "}" : term

macro_rules 
| `({ $x:ident : $t | $p }) => `(setOf (λ ($x:ident : $t) => $p))
| `({ $x:ident | $p }) => `(setOf (λ ($x:ident) => $p))
| `({ $x:ident ∈ $s | $p }) => `(setOf (λ $x => $x ∈ $s → $p))

def union (s t : Set α) : Set α := { x : α | x ∈ s ∨ x ∈ t } 

def inter (s t : Set α) : Set α := { x : α | x ∈ s ∧ x ∈ t }

theorem unionDef (s t : Set α) : union s t = λ x => s x ∨ t x := rfl

theorem interDef (s t : Set α) : inter s t = λ x => s x ∧ t x := rfl

infix:60 "∪" => Set.union
infix:60 "∩" => Set.inter

def Union (s : Set (Set α)) : Set α := { x : α | ∃ t : Set α, t ∈ s → t x }

def Inter (s : Set (Set α)) : Set α := { x : α | ∀ t : Set α, t ∈ s → t x }

def UnionDef (s : Set (Set α)) : Union s = λ x => ∃ t : Set α, t ∈ s → t x := rfl

def InterDef (s : Set (Set α)) : Inter s = λ x => ∀ t : Set α, t ∈ s → t x := rfl

syntax "⋃" index "," term : term
syntax "⋂" index "," term : term

macro_rules
| `(⋃ $s:ident ∈ $c, $s) => `(Union $c)
| `(⋂ $s:ident ∈ $c, $s) => `(Inter $c)

-- variables {s : Set (Set α)}

-- #check ⋂ t ∈ s, t

-- Notation for ∀ x ∈ s, p and ∃ x ∈ s, p
syntax "∀" index "," term : term
syntax "∃" index "," term : term

macro_rules
| `(∀ $x:ident ∈ $s, $p) => `(∀ $x:ident, $x ∈ $s → $p)
| `(∃ $x:ident ∈ $s, $p) => `(∃ $x:ident, $x ∈ $s ∧ $p)

def Subset (s t : Set α) := ∀ x ∈ s, x ∈ t

infix:50 "⊆" => Subset

theorem Subset.def {s t : Set α} : s ⊆ t ↔ ∀ x ∈ s, x ∈ t := Iff.rfl

namespace Subset

theorem refl {s : Set α} : s ⊆ s := λ _ hx => hx

theorem trans {s t v : Set α} (hst : s ⊆ t) (htv : t ⊆ v) : s ⊆ t := 
  λ x hx => hst x hx

theorem antisymm {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ s) : s = t := 
  Set.ext λ x => ⟨ λ hx => hst x hx, λ hx => hts x hx ⟩

theorem antisymmIff {s t : Set α} : s = t ↔ s ⊆ t ∧ t ⊆ s :=
  ⟨ by { intro hst; subst hst; exact ⟨ refl, refl ⟩ }, 
    λ ⟨ hst, hts ⟩ => antisymm hst hts ⟩ 

-- ↓ Uses classical logic
theorem notSubset : ¬ s ⊆ t ↔ ∃ x ∈ s, x ∉ t := by 
  apply Iff.intro;
  { intro hst; 
    rw Classical.Exists.notAnd;
    apply Classical.notForall;
    exact λ h => hst λ x hx => h x hx }
  { intro h hst;
    let ⟨ x, ⟨ hxs, hxt ⟩ ⟩ := h;
    exact hxt <| hst x hxs }

end Subset

theorem memEmptySet {x : α} (h : x ∈ ∅) : False := h

@[simp] theorem memEmptySetIff : (∃ (x : α), x ∈ ∅) ↔ False := 
  Iff.intro (λ h => h.2) False.elim 

@[simp] theorem setOfFalse : { a : α | False } = ∅ := rfl

def univ : Set α := { x | True }

@[simp] theorem memUniv (x : α) : x ∈ univ := True.intro

theorem Subset.subsetUniv {s : Set α} : s ⊆ univ := λ x _ => memUniv x 

theorem Subset.univSubsetIff {s : Set α} : univ ⊆ s ↔ univ = s := by
  apply Iff.intro λ hs => Subset.antisymm hs Subset.subsetUniv 
  { intro h; subst h; exact Subset.refl }

theorem eqUnivIff {s : Set α} : s = univ ↔ ∀ x, x ∈ s := by 
  apply Iff.intro 
  { intro h x; subst h; exact memUniv x }
  { exact λ h => ext λ x => Iff.intro (λ _ => memUniv _) λ _ => h x }

/-! ### Unions and Intersections -/

macro "extia" x:term : tactic => `(tactic| apply ext; intro $x; apply Iff.intro)

theorem unionSelf {s : Set α} : s ∪ s = s := by 
  extia x
  { intro hx; cases hx; assumption; assumption }
  { exact Or.inl }

theorem unionEmpty {s : Set α} : s ∪ ∅ = s := by 
  extia x
  { intro hx; cases hx with 
    | inl   => assumption
    | inr h => exact False.elim <| memEmptySet h }
  { exact Or.inl }

theorem unionSymm {s t : Set α} : s ∪ t = t ∪ s := by 
  extia x 
  allGoals { intro hx; cases hx with 
             | inl hx => exact Or.inr hx
             | inr hx => exact Or.inl hx }

theorem emptyUnion {s : Set α} : ∅ ∪ s = s := by 
  rw unionSymm; exact unionEmpty

theorem unionAssoc {s t w : Set α} : s ∪ t ∪ w = s ∪ (t ∪ w) := by 
  extia x
  { intro hx; cases hx with 
    | inr hx   => exact Or.inr <| Or.inr hx
    | inl hx   => cases hx with 
      | inr hx => exact Or.inr <| Or.inl hx
      | inl hx => exact Or.inl hx }
  { intro hx; cases hx with 
    | inl hx   => exact Or.inl <| Or.inl hx
    | inr hx   => cases hx with 
      | inr hx => exact Or.inr hx
      | inl hx => exact Or.inl <| Or.inr hx }

end Set