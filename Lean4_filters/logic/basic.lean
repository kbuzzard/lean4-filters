@[simp] theorem True_imp (p : Prop) : True → p ↔ p := ⟨λ h => h trivial, λ hp _ => hp⟩
