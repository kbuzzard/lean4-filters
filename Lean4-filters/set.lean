open Lean in
macro "begin " ts:tactic,*,? "end"%i : term => do
  -- preserve position of the last token, which is used
  -- as the error position in case of an unfinished proof
  `(by { $[$ts:tactic]* }%$i)
  
def Set {α : Type} := α → Prop

#check Classical.em

example (p : Prop) : ¬ ¬ p → p := by
  intro h
  cases (Classical.em p)
  focus
    assumption
  focus
    admit

  



