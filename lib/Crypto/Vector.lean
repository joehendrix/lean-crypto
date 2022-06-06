import Crypto.Array

/--
This module introduces arrays with an explicit type parameter for storing length.
-/

-- An array with explicit parameter for length.
structure Vector (n:Nat) (α:Type) where
  data : Array α
  size_proof : data.size = n

namespace Vector

-- Construct a vector whose contents are generated from function.
def generate (n:Nat) (f : Fin n → α) : Vector n α :=
  { data := Array.generate n f,
    size_proof := Array.size_generate n f
  }

def get {n:Nat} {α:Type _} (v:Vector n α) (i: Fin n) : α :=
  let p : i.val < v.data.size := by
        simp only [v.size_proof]
        exact i.isLt
  v.data.get ⟨i.val, p⟩

end Vector