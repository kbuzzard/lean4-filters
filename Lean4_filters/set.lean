def Set {α : Type} := α → Prop

class HasMem (α : outParam $ Type u) (β : Type v) where
    mem : α → β → Prop

infix:50 " ∈ " => HasMem.mem

class HasLe (α : Type u) where
    le : α → α → Prop

infix:50 " ≤ " => HasLe.le



  



