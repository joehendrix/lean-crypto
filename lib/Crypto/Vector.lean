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
protected def generate (n:Nat) (f : Fin n → α) : Vector n α :=
  { data := Array.generate n f,
    size_proof := Array.size_generate n f
  }

def get! {n:Nat} {α:Type _} [Inhabited α] (v:Vector n α) (i: Nat) : α := v.data.get! i

def get {n:Nat} {α:Type _} (v:Vector n α) (i: Fin n) : α :=
  let p : i.val < v.data.size := by
        simp only [v.size_proof]
        exact i.isLt
  v.data.get ⟨i.val, p⟩


protected
def replicate {α : Type _} (n:Nat) (d:α): Vector n α  := Vector.generate n (λi => d)

instance (n:Nat) (α: Type _) [Inhabited α] : Inhabited (Vector n α) := ⟨Vector.replicate n default⟩

protected
def zero {α : Type _} [OfNat α 0] (n:Nat) : Vector n α := Vector.replicate n 0

end Vector