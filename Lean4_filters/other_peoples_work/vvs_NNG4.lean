theorem add_zero : x + 0 = x := by
  rfl

theorem add_succ : x + Nat.succ y = Nat.succ (x + y) := by
  rfl

theorem one_Eq_succ_zero : 1 = Nat.succ 0 := by
  rfl

--set_option hygienicIntro false in
theorem zero_add : 0 + x = x := by
  induction x with | succ _ ih => _ | _ => _
  rfl
  rewrite add_succ
  apply congrArg -- or just `rw ih`/`rw v_0`
  assumption

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with | succ _ ih => _ | _ => _
  rewrite add_zero
  rewrite add_zero
  rfl
  rewrite add_succ
  rewrite add_succ
  rewrite add_succ
  rewrite ih
  rfl

theorem succ_add (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with | succ _ ih => _ | _ => _
  rfl
  rewrite add_succ
  rewrite add_succ
  rewrite ih
  rfl

theorem add_comm (a b : Nat) : a + b = b + a := by
  induction b with | succ _ ih => _ | _ => _
  rewrite zero_add
  rfl
  rewrite add_succ
  rewrite succ_add
  rewrite ih
  rfl

theorem succ_Eq_add_one (n : Nat) : Nat.succ n = n + 1 := by
  rewrite one_Eq_succ_zero
  rewrite add_succ
  rfl

theorem add_rightComm (a b c : Nat) : a + b + c = a + c + b := by
  rewrite add_assoc
  rewrite add_comm b
  rewrite add_assoc
  rfl
