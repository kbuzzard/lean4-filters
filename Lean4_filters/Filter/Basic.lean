import Lean4_filters.Set.Basic

structure Filter (α : Type u) where
  sets : Set (Set α)
