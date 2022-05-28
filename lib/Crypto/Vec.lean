structure Vec (n:Nat) (α:Type u) where
  data : Array α
  size_proof : data.size = n

namespace Vec

def groupBy {n:Nat} : Vec n α → ∀(parts each:Nat), Vec parts (Vec each α) := sorry

protected def map {n:Nat} {α β : Type u} (f : α → β) (a: Vec n α) : Vec n β := sorry

instance : Functor (Vec n) where
  map := Vec.map

end Vec