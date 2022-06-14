namespace Bool

instance : Xor Bool := ⟨bne⟩

@[simp] theorem false_xor (a : Bool) : false ^^^ a = a := by cases a <;> rfl
@[simp] theorem xor_false (a : Bool) : a ^^^ false = a := by cases a <;> rfl
@[simp] theorem true_xor (a : Bool) : true ^^^ a = !a := by cases a <;> rfl
@[simp] theorem xor_true (a : Bool) : a ^^^ true = !a := by cases a <;> rfl

theorem xor_comm (a b : Bool) : a ^^^ b = b ^^^ a :=
  by cases a <;> simp

theorem xor_assoc (a b c : Bool) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) :=
  by cases a <;> cases b <;> simp

-- TODO(WN): Should these be in the Lean namespace? And probably Mathlib classes
-- should imply them.
instance : Lean.IsCommutative (α := Bool) HXor.hXor := ⟨xor_comm⟩

instance : Lean.IsAssociative (α := Bool) HXor.hXor := ⟨xor_assoc⟩

end Bool