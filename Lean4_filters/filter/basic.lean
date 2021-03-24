import Lean4_filters.set.completeLattice

open Lattice

structure Filter (α) where
  (sets : Set (Set α))
  (univ_sets : Set.univ ∈ sets)
  (sets_of_superset {x y} : x ∈ sets → x ≤ y → y ∈ sets)
  (inter_sets {x y} : x ∈ sets → y ∈ sets → x ⊓ y ∈ sets)

instance : HasMem (Set α) (Filter α) := ⟨λ s f => s ∈ f.sets⟩

namespace Filter

@[simp] theorem univ_mem (f : Filter α) : Set.univ ∈ f := f.univ_sets

variable {f : Filter α}

theorem mem_sets_of_superset : x ∈ f → x ≤ y → y ∈ f := f.sets_of_superset

theorem mem_mono : x ≤ y → x ∈ f → y ∈ f := flip mem_sets_of_superset

theorem inter_mem_sets : x ∈ f → y ∈ f → x ⊓ y ∈ f := f.inter_sets

@[simp] theorem inter_mem_sets_iff : x ⊓ y ∈ f ↔ x ∈ f ∧ y ∈ f := by
  refine ⟨λ h => ⟨mem_mono ?hx h, mem_mono ?hy h⟩, λ ⟨hx, hy⟩ => inter_mem_sets hx hy⟩
  { rw Set.mem_inf_iff; -- element name is selected to be `x` even though there is another `x` in the context
    intro hx; -- intro ⟨hx, hy⟩ doesn't work here, despite what Zulip says
    exact hx.left }
  { rw Set.mem_inf_iff;
    intro hx;
    exact hx.right }

instance : HasInf (Filter α) := ⟨λ f g => {
  sets := λ s => ∃ t u, t ∈ f → u ∈ g → t ⊓ u ≤ s
  univ_sets := ⟨Set.univ, Set.univ, by simp⟩
  sets_of_superset := λ ⟨x, y, h⟩ hl => ⟨x, y, by -- doing it in term mode unfolds the ≤ defn instead

    -- intro hx hy
    -- refine LessEq.trans ?_ hl -- this does not work
    -- admit

    intro hx hy
    apply LessEq.trans
    { exact h hx hy }
    { exact hl }

    -- intro hx hy a ha -- expanding out the set membership
    -- apply hl
    -- exact h hx hy ha
  ⟩
  inter_sets := λ ⟨s, t, h⟩ ⟨x, y, h'⟩ => ⟨s ⊓ x, t ⊓ y, by
    intros hst hxy
    admit -- Johannes used ac_refl -- should we port it?
  ⟩
}⟩

end Filter
