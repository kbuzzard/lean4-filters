example (p : Prop) : ¬ ¬ p → p := by
  intro h;
  cases (Classical.em p);
  { assumption };
  { apply False.elim;
    apply h;
    assumption }

-- compiles
example (p : Prop) : ¬ ¬ p → p := by
  intro h;
  cases (Classical.em p);
    assumption;
  admit
  
-- copied from the manual
open Lean in
macro "begin " ts:tactic,*,? "end"%i : term => do
  -- preserve position of the last token, which is used
  -- as the error position in case of an unfinished proof
  `(by { $[$ts:tactic]* }%$i)

-- fails
example (p : Prop) : ¬ ¬ p → p :=
begin
  intro h,
  cases (Classical.em p),
    assumption,-- error "unknown identifier 'assumption'"
  admit
end