/-

## `left` and `right`

-/
syntax "left" : tactic

macro_rules
  | `(tactic| left) => `(tactic| apply Or.inl)

syntax "right" : tactic

macro_rules
  | `(tactic| right) => `(tactic| apply Or.inr)

syntax "split" : tactic

/-

## `split`

-/

macro_rules
  | `(tactic| split) => `(tactic| apply And.intro)

-- todo : cases (h : p ∧ q) with hp hq