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

def set! {n:Nat} {α:Type _} (v:Vector n α) (i: Nat) (e:α) : Vector n α :=
  { data := v.data.set! i e, size_proof := sorry }

def add! {n:Nat} {α:Type _} [Add α] (v:Vector n α) (i: Nat) (e:α) : Vector n α :=
  let h : Inhabited α := ⟨e⟩
  { data := v.data.set! i (v.data.get! i + e), size_proof := sorry }

def sub! {n:Nat} {α:Type _} [Sub α] (v:Vector n α) (i: Nat) (e:α) : Vector n α :=
  let h : Inhabited α := ⟨e⟩
  { data := v.data.set! i (v.data.get! i - e), size_proof := sorry }

protected
def replicate {α : Type _} (n:Nat) (d:α): Vector n α  := Vector.generate n (λi => d)

instance (n:Nat) (α: Type _) [Inhabited α] : Inhabited (Vector n α) := ⟨Vector.replicate n default⟩

protected
def zero {α : Type _} [OfNat α 0] (n:Nat) : Vector n α := Vector.replicate n 0

protected def map {n:Nat} {α β : Type _} (f : α → β) (v : Vector n α) : Vector n β :=
  Vector.generate n (λi => f (v.get i))

instance : Functor (Vector n) where
  map := Vector.map

protected
def qsort {n : Nat} {α : Type _} [Inhabited α] (v:Vector n α) (lt : α → α → Bool) : Vector n α :=
  { data := Array.qsort v.data lt,
    size_proof := Eq.trans (Array.size_qsort v.data lt) v.size_proof
  }

theorem eq_of_val_eq {n:Nat} {α : Type _} : ∀ {x y : Vector n α}, Eq x.data y.data → Eq x y
  | ⟨x,_⟩, _, rfl => rfl

theorem ne_of_val_ne {n:Nat} {α : Type _} {i j : Vector n α} (h : Not (Eq i.data j.data)) : Not (Eq i j) :=
  λh' => absurd (h' ▸ rfl) h

protected def decideEq {n:Nat} {α : Type _} [DecidableEq α] : (a b : Vector n α) → Decidable (Eq a b) :=
  fun ⟨i, _⟩ ⟨j, _⟩ =>
    match decEq i j with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

instance (n:Nat) {α : Type _} [DecidableEq α] : DecidableEq (Vector n α) := Vector.decideEq

def push (v:Vector n α) (x : α) : Vector (n+1) α :=
  let pr : (v.data.push x).size = n + 1 := by
        simp only [Array.size_push, v.size_proof]
  ⟨v.data.push x, pr⟩

end Vector