-- This module introduces arrays with an explicit type parameter for storing length.
import Crypto.Array
import Crypto.Nat
import Crypto.Range
import Crypto.Hadamard


/--
An array with explicit parameter for length.
-/
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
  { data := v.data.set! i e, size_proof := Eq.trans (Array.size_set! _) v.size_proof }

def add! {n:Nat} {α:Type _} [Add α] (v:Vector n α) (i: Nat) (e:α) : Vector n α :=
  let _h : Inhabited α := ⟨e⟩
  v.set! i (v.get! i + e)

def sub! {n:Nat} {α:Type _} [Sub α] (v:Vector n α) (i: Nat) (e:α) : Vector n α :=
  let _h : Inhabited α := ⟨e⟩
  v.set! i (v.get! i - e)

def xor! {n:Nat} {α:Type _} [Xor α] (v:Vector n α) (i: Nat) (e:α) : Vector n α :=
  let _h : Inhabited α := ⟨e⟩
  v.set! i (v.get! i ^^^ e)

protected
def replicate {α : Type _} (n:Nat) (d:α): Vector n α  := Vector.generate n (λ_ => d)

instance (n:Nat) (α: Type _) [Inhabited α] : Inhabited (Vector n α) := ⟨Vector.replicate n default⟩

protected
def zero {α : Type _} [OfNat α 0] (n:Nat) : Vector n α := Vector.replicate n 0

protected def map {n:Nat} {α β : Type _} (f : α → β) (v : Vector n α) : Vector n β :=
  Vector.generate n (λi => f (v.get i))

instance : Functor (Vector n) where
  map := Vector.map

-- `iterate n f b` returns a vector v where `v.get i` is equal to `f^i b`.
def iterate (n:Nat) (f : α → α) (b:α) : Vector n α := Id.run do
  let mut a := (Array.mkEmpty n).push b
  let mut b := b
  for i in range 1 n do
    b := f b
    a := a.push b
  let p : a.size = n := by admit
  ⟨a, p⟩

protected
def qsort {n : Nat} {α : Type _} [Inhabited α] (v:Vector n α) (lt : α → α → Bool) : Vector n α :=
  { data := Array.qsort v.data lt,
    size_proof := Eq.trans (Array.size_qsort v.data lt) v.size_proof
  }

theorem eq_of_val_eq {n:Nat} {α : Type _} : ∀ {x y : Vector n α}, Eq x.data y.data → Eq x y
  | ⟨_,_⟩, _, rfl => rfl

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

protected
def append (x : Vector m α) (y : Vector n α) : Vector (m+n) α :=
  let p : (x.data ++ y.data).size = (m+n) := by
        simp only [Array.size_append, x.size_proof, y.size_proof]
  ⟨x.data ++ y.data, p⟩

instance : HAppend (Vector m α) (Vector n α) (Vector (m+n) α) where
  hAppend := Vector.append

def extractN! [Inhabited α] (a : Vector n α) (s m:Nat) : Vector m α :=
  let b := a.data.extract s (s+m)
  let e := Array.generate (m - b.size) (λ_ => default)
  let pr : (b ++ e).size = m := by
        simp [Array.size_append, Array.size_generate]
        have p : min (s + m) (Array.size a.data) - s ≤ m := by
              apply Nat.sub_le_of_le_add
              simp only [Nat.add_comm s m, min]
              cases Decidable.em (m + s ≤ a.data.size) with
              | inl h =>
                simp [h]
              | inr h =>
                simp [h]
                exact Nat.le_of_lt (Nat.gt_of_not_le h)
        simp [Nat.add_sub_of_le p]
  ⟨b ++ e, pr⟩

def smul [h:HMul α β γ] (a:α) (v:Vector n β) : Vector n γ := (HMul.hMul a) <$> v

instance [HMul α β γ]: HMul α (Vector n β) (Vector n γ) := ⟨Vector.smul⟩

protected
def zip (f: α → β → γ) (u:Vector n α) (v:Vector n β) : Vector n γ :=
  Vector.generate n (λi => f (u.get i) (v.get i))

def add [h:HAdd α β γ] (u:Vector n α) (v:Vector n β) : Vector n γ :=
  Vector.zip HAdd.hAdd u v

instance [HAdd α β γ] : HAdd (Vector n α) (Vector n β) (Vector n γ) where
  hAdd := Vector.add

def hadProd [h:HMul α β γ] (u:Vector n α) (v:Vector n β) : Vector n γ :=
  Vector.zip HMul.hMul u v

instance [HMul α β γ] : HadamardProduct (Vector n α) (Vector n β) (Vector n γ) where
  hadProd := Vector.hadProd

def flatten (v : Vector m (Vector n α)) : Vector (m*n) α :=
  Vector.generate (m*n) λi =>
    have n_pos : 0 < n := by
            have p := i.isLt
            cases n with
            | zero =>
              contradiction
            | succ x =>
              exact (Nat.zero_lt_succ _)
    (v.get ⟨i.val/n, Nat.mul_div_lt i.isLt⟩).get ⟨i.val%n, Nat.mod_lt _ n_pos⟩

end Vector