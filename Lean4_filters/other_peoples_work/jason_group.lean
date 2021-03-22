-- Stuff that's not there yet

class One (α : Type u) where
  one : α

instance [One α] : OfNat α (natLit! 1) where
  ofNat := One.one

class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

-- where is `u` coming from?
def Function.injective {α : Sort u} {β : Sort v} (f : α → β) : Prop :=
  ∀ a₁ a₂ : α, f a₁ = f a₂ → a₁ = a₂

theorem Function.injective.eqIff {α : Sort u} {β : Sort v} {f : α → β} (I : Function.injective f) {a b : α} :
  f a = f b ↔ a = b :=
⟨I a b, λ h => congrArg _ h⟩

-- Actual File from mathlib

universe u

section Mul

variables {G : Type u} [Mul G] 

def leftMul : G → G → G := λ g : G => λ x : G => g * x 

def rightMul : G → G → G := λ g : G => λ x : G => x * g

end Mul

class Semigroup (G : Type u) extends Mul G where
  mulAssoc : ∀ a b c : G, (a * b) * c = a * (b * c)

section Semigroup

variables {G : Type u} [Semigroup G]

theorem mulAssoc : ∀ a b c : G, (a * b) * c = a * (b * c) := Semigroup.mulAssoc

end Semigroup

class CommSemigroup (G : Type u) extends Semigroup G where
  mulComm : ∀ a b : G, a * b = b * a

section CommSemigroup

variables {G : Type u} [CommSemigroup G]

theorem mulComm : ∀ a b : G, a * b = b * a := CommSemigroup.mulComm

end CommSemigroup

class LeftCancelSemigroup (G : Type u) extends Semigroup G where
  mulLeftCancel : ∀ a b c : G, a * b = a * c → b = c

section LeftCancelSemigroup

variables {G : Type u} [LeftCancelSemigroup G] {a b c : G}

theorem mulLeftCancel : a * b = a * c → b = c := LeftCancelSemigroup.mulLeftCancel a b c

theorem mulLeftCancelIff : a * b = a * c ↔ b = c :=
⟨mulLeftCancel, congrArg _⟩

-- It's \centerdot
theorem mulRightInjective (a : G) : Function.injective ((a * ·)) :=
λ b c => mulLeftCancel

theorem mulRightInj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
(mulRightInjective a).eqIff

end LeftCancelSemigroup

class RightCancelSemigroup (G : Type u) extends Semigroup G where
  mulRightCancel : ∀ a b c : G, a * b = c * b → a = c

section RightCancelSemigroup

variables {G : Type u} [RightCancelSemigroup G] {a b c : G}

theorem mulRightCancel : a * b = c * b → a = c := RightCancelSemigroup.mulRightCancel a b c

theorem mulRightCancelIff : a * b = c * b ↔ a = c :=
⟨mulRightCancel, congrArg (· * b)⟩ -- mathlib Lean 3 proof is ⟨mul_right_cancel, congr_arg _⟩

theorem mulLeftInjective (a : G) : Function.injective (· * a) :=
λ b c => mulRightCancel

theorem mulLeftInj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
(mulLeftInjective a).eqIff

end RightCancelSemigroup

class Monoid (M : Type u) extends Semigroup M, One M where
  oneMul : ∀ a : M, 1 * a = a
  mulOne : ∀ a : M, a * 1 = a

section Monoid

variables {M : Type u} [Monoid M]

theorem oneMul : ∀ a : M, 1 * a = a := Monoid.oneMul

theorem mulOne : ∀ a : M, a * 1 = a := Monoid.mulOne

theorem leftInvEqRightInv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [←oneMul c, ←hba, mulAssoc, hac, mulOne]

end Monoid

-- This no longer `extends` `CommSemigroup`
class CommMonoid (M : Type u) extends Monoid M where
  mulComm : ∀ a b : M, a * b = b * a

-- Instead, we have an instance going from `CommMonoid` to `CommSemigroup`
instance {M : Type u} [CommMonoid M] : CommSemigroup M where
  mulComm := CommMonoid.mulComm

section LeftCancelMonoid

-- Again, we only extend one `class` and we provide an instance to the other
class LeftCancelMonoid (M : Type u) extends Monoid M where
  mulLeftCancel : ∀ a b c : M, a * b = a * c → b = c

instance {M : Type u} [LeftCancelMonoid M] : LeftCancelSemigroup M where
  mulLeftCancel := LeftCancelMonoid.mulLeftCancel

class LeftCancelCommMonoid (M : Type u) extends LeftCancelMonoid M where
  mulComm : ∀ a b : M, a * b = b * a

instance {M : Type u} [LeftCancelCommMonoid M] : CommMonoid M where
  mulComm := LeftCancelCommMonoid.mulComm

end LeftCancelMonoid

section RightCancelMonoid 

class RightCancelMonoid (M : Type u) extends Monoid M where
  mulRightCancel : ∀ a b c : M, a * b = c * b → a = c

instance {M : Type u} [RightCancelMonoid M] : RightCancelSemigroup M where
  mulRightCancel := RightCancelMonoid.mulRightCancel

class RightCancelCommMonoid (M : Type u) extends RightCancelMonoid M where
  mulComm : ∀ a b : M, a * b = b * a

instance {M : Type u} [RightCancelCommMonoid M] : CommMonoid M where
  mulComm := RightCancelCommMonoid.mulComm

end RightCancelMonoid

section CancelMonoid

class CancelMonoid (M : Type u) extends LeftCancelMonoid M where
  mulRightCancel : ∀ a b c : M, a * b = c * b → a = c

instance {M : Type u} [CancelMonoid M] : RightCancelMonoid M where
  mulRightCancel := CancelMonoid.mulRightCancel

class CancelCommMonoid (M : Type u) extends LeftCancelCommMonoid M where
  mulRightCancel : ∀ a b c : M, a * b = c * b → a = c

instance {M : Type u} [CancelCommMonoid M] : RightCancelCommMonoid M where
  mulRightCancel := CancelCommMonoid.mulRightCancel
  mulComm := λ a b => mulComm a b -- why is the λ necessary?

end CancelMonoid

class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  div := λ a b => a * b⁻¹
  divEqMulInv : ∀ a b : G, a / b = a * b⁻¹

theorem divEqMulInv {G : Type u} [DivInvMonoid G] :
  ∀ a b : G, a / b = a * b⁻¹ :=
DivInvMonoid.divEqMulInv

class Group (G : Type u) extends DivInvMonoid G where
  mulLeftInv : ∀ a : G, a⁻¹ * a = 1

def Group.toMonoid (G : Type u) [Group G] : Monoid G :=
  (Group.toDivInvMonoid (G := G)).toMonoid -- no more underscores!

section Group

variables {G : Type u} [Group G] {a b c : G}

@[simp]
theorem mulLeftInv : ∀ a : G, a⁻¹ * a = 1 := Group.mulLeftInv

@[simp]
theorem invMulCancelLeft (a b : G) : a⁻¹ * (a * b) = b := by
  rw [←mulAssoc, mulLeftInv, oneMul]

@[simp]
theorem invEqOfMulEqOne (h : a * b = 1) : a⁻¹ = b :=
  leftInvEqRightInv (mulLeftInv _) h

@[simp]
theorem invInv (a : G) : a⁻¹⁻¹ = a :=
  invEqOfMulEqOne (mulLeftInv _)

@[simp]
theorem mulRightInv (a : G) : a * a⁻¹ = 1 :=
  have a⁻¹⁻¹ * a⁻¹ = 1 := mulLeftInv a⁻¹
  by rw invInv at this
     assumption

theorem mulInv (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply invEqOfMulEqOne
  rw [← mulAssoc, mulAssoc _ b, mulRightInv, mulOne, mulRightInv]

theorem invMulInvEqInvMul (a b : G) : (a⁻¹ * b)⁻¹ = b⁻¹ * a := by 
  rw [mulInv, invInv]

theorem mulInvSelf (a : G) : a * a⁻¹ = 1 := mulRightInv a

@[simp]
theorem mulInvCancelRight (a b : G) : a * b * b⁻¹ = a := by
  rw [mulAssoc, mulRightInv, mulOne]

instance : CancelMonoid G where 
  mulLeftCancel := λ a b c h => by rw [←invMulCancelLeft a b, h, invMulCancelLeft]
  mulRightCancel := λ a b c h => by rw [←mulInvCancelRight a b, h, mulInvCancelRight]

end Group

class CommGroup (G : Type u) extends Group G where
  mulComm : ∀ a b : G, a * b = b * a

instance (G : Type u) [CommGroup G] : CommMonoid G where
  mulComm := CommGroup.mulComm

def Set (α : Type u) := α → Prop

namespace Set

variables {α : Type u} {s : Set α}

def mem (a : α) (s : Set α) := s a

infix:50 " ∈ " => Set.mem

instance : CoeSort (Set α) (Type u) where 
  coe s := Subtype s

theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := 
  funext <| λ x => propext <| h x

-- instance : Coe (Set α) α := ⟨ λ a => a.1 ⟩ 

end Set

structure Subgroup (G : Type u) [Group G] :=
(carrier : Set G)
(oneMem' : 1 ∈ carrier)
(mulMem' {x y} : x ∈ carrier → y ∈ carrier → (x * y) ∈ carrier)
(invMem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

-- We try out the suggestion about membership where we do not make a membership 
-- relation for subgroups

namespace Subgroup

variables {G : Type u} [Group G] {H : Subgroup G}

theorem oneMem : 1 ∈ H.carrier := H.oneMem'

theorem mulMem {x y : G} (hx : x ∈ H.carrier) (hy : y ∈ H.carrier.mem) : 
  H.carrier.mem (x * y) := H.mulMem' hx hy

theorem invMem {x : G} (hx : x ∈ H.carrier) : x⁻¹ ∈ H.carrier := 
  H.invMem' hx

theorem mkInj (s t : Set G) (hs₁ : 1 ∈ s) (ht₁ : 1 ∈ t) 
  (hs₂ : ∀ {x y}, x ∈ s → y ∈ s → (x * y) ∈ s) 
  (ht₂ : ∀ {x y}, x ∈ t → y ∈ t → (x * y) ∈ t) 
  (hs₃ : ∀ {x}, x ∈ s → x⁻¹ ∈ s)
  (ht₃ : ∀ {x}, x ∈ t → x⁻¹ ∈ t) (hst : s = t) : 
  Subgroup.mk s hs₁ hs₂ hs₃ = Subgroup.mk t ht₁ ht₂ ht₃ := by subst hst; rfl

theorem ext' {H K : Subgroup G} (h : H.carrier = K.carrier) : H = K := by
  cases H; cases K
  apply mkInj; allGoals { assumption }

theorem invMemIff {x : G} : x⁻¹ ∈ H.carrier ↔ x ∈ H.carrier := by
  apply Iff.intro
  { intro hx; rw ← invInv x;
    exact invMem hx }
  { exact invMem }

instance : Coe (Subgroup G) (Set G) := ⟨ Subgroup.carrier ⟩

instance : CoeSort (Subgroup G) (Type u) where 
  coe s := Subtype s.carrier

instance ofSubgroup (H : Subgroup G) : Group (coeSort H) where
  mul := λ x y => ⟨ x.1 * y.1, H.mulMem x.2 y.2 ⟩ 
  one := ⟨ 1, H.oneMem ⟩  
  inv := λ x => ⟨ x.1⁻¹, H.invMem x.2 ⟩
  oneMul := λ x => by { cases x; apply Subtype.eq; exact oneMul _ }
  mulOne := λ x => by { cases x; apply Subtype.eq; exact mulOne _ }
  mulAssoc := λ x y z => by 
    { cases x; cases y; cases z; apply Subtype.eq;
      exact mulAssoc _ _ _ }
  divEqMulInv := λ x y => rfl
  mulLeftInv := λ x => by { cases x; apply Subtype.eq; exact mulLeftInv _ }

@[simp] theorem coeMul (a b : G) (ha : a ∈ H.carrier) (hb : b ∈ H.carrier) :
  (⟨a, ha⟩ * ⟨b, hb⟩ : H).1 = a * b := rfl

def LCoset (g : G) (H : Subgroup G) : Set G := 
  (λ s => ∃ k, ∃ (h : k ∈ H.carrier), s = g * k)

infix:70 " ⋆ " => LCoset

theorem selfMemLCoset (x : G) (H : Subgroup G): x ∈ x ⋆ H := 
  ⟨ 1, ⟨ H.oneMem, (mulOne x).symm ⟩ ⟩ 

theorem LCosetEq {x y : G} : x ⋆ H = y ⋆ H ↔ x⁻¹ * y ∈ H := by 
  apply Iff.intro
  { intro h;
    have h' : x ∈ y ⋆ H := by 
    { rw ← h;
      exact selfMemLCoset _ _ };
    cases h' with | intro k hk => 
    cases hk with | intro hk hk' => 
    { rw [hk', mulInv, mulAssoc, mulLeftInv, mulOne];
      exact invMem hk  } }
  { intro h;
    apply Set.ext;
    intro t;
    apply Iff.intro;
    { intro ht;
      cases ht with | intro g hg => 
      cases hg with | intro hg₀ hg₁ => 
      { rw hg₁;
        apply Exists.intro (y⁻¹ * x * g);
        apply Exists.intro <| H.mulMem _ hg₀;
        rw [← mulAssoc, ← mulAssoc, mulRightInv, oneMul];
        rw [← invMulInvEqInvMul];
        exact H.invMem h } }
    { intro ht;
      cases ht with | intro g hg => 
      cases hg with | intro hg₀ hg₁ => 
      { rw hg₁;
        apply Exists.intro (x⁻¹ * y * g);
        apply Exists.intro <| H.mulMem h hg₀;
        rw [← mulAssoc, ← mulAssoc, mulRightInv, oneMul] } } }

theorem oneLCosetEqSelf : 1 ⋆ H = H := by
  apply Set.ext;
  intro x; 
  apply Iff.intro;
  { intro hx;
    cases hx with | intro h hh => 
    cases hh with | intro hh₀ hh₁ => 
    { rw [hh₁, oneMul]; assumption } }
  { intro hx;
    apply Exists.intro x;
    apply Exists.intro hx;
    rw oneMul }

theorem memSubgroupIff (x : G) : x ∈ H.carrier ↔ x ∈ H := Iff.rfl

theorem lcoset_of_mem {a : G} :
  a ⋆ H = H ↔ a ∈ H := by 
  rw [← oneLCosetEqSelf, LCosetEq, mulOne, oneLCosetEqSelf, 
      ← memSubgroupIff, invMemIff]; exact Iff.rfl
  
theorem lcoset_digj {a b c : G} (ha : c ∈ a ⋆ H) (hb : c ∈ b ⋆ H) : 
  a ⋆ H = b ⋆ H := by
  { let ⟨g₀, ⟨hg₀, hca⟩⟩ := ha; let ⟨g₁, ⟨hg₁, hcb⟩⟩ := hb;
    rw [LCosetEq, show b = c * g₁⁻¹ by simp [hcb]];
    rw (show a⁻¹ = g₀ * c⁻¹ by rw [(show a = c * g₀⁻¹ by 
      rw [hca, mulAssoc, mulRightInv, mulOne]), mulInv, invInv]);
    rw [← mulAssoc, mulAssoc _ _ c, mulLeftInv, mulOne];
    exact H.mulMem hg₀ (H.invMem hg₁) }

end Subgroup

