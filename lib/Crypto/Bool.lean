import Mathlib.Data.Bool.Basic

namespace Bool

instance : Xor Bool := ⟨xor⟩

-- TODO(WN): Should these be in the Lean namespace? And probably Mathlib classes
-- should imply them.
instance : Lean.IsCommutative (α := Bool) HXor.hXor := ⟨xor_comm⟩

instance : Lean.IsAssociative (α := Bool) HXor.hXor := ⟨xor_assoc⟩

end Bool