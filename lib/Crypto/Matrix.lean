import Crypto.Array
import Crypto.Vector

structure Range where
  base : Nat
  count : Nat

def range (l n:Nat) : Range := ⟨l, n⟩

namespace Range

protected
def forIn {β} {m} [Monad m] (x : Range) (b : β) (f : Nat → β → m (ForInStep β)) : m β :=
  let e := x.base + x.count
  let rec loop : Nat → β → m β
      | 0, b => pure b
      | Nat.succ n, b => do
        let r ← f (e - Nat.succ n) b
        match r with
        | ForInStep.done r => pure r
        | ForInStep.yield r => loop n r
  loop x.count b

instance {m: Type _ → Type _} [Monad m] : ForIn m Range Nat where
  forIn := Range.forIn

end Range

structure Matrix (r c : Nat) (α :Type _) where
  data : Array α
  size_proof : data.size = r*c

namespace Matrix

protected
def generate {α : Type _} (m n:Nat) (f:Fin m → Fin n → α): Matrix m n α  :=
  { data := Array.generate (m*n) (λi => f ⟨i.val / n, sorry⟩ ⟨i.val % n, sorry⟩),
    size_proof := Array.size_generate _ _
  }

protected
def replicate {α : Type _} (r c:Nat) (d:α): Matrix r c α  :=
  { data := Array.generate (r*c) (λi => d),
    size_proof := Array.size_generate _ _
  }

protected
def get! {α : Type _} [Inhabited α] {r c:Nat} (x:Matrix r c α) (i j : Nat) : α :=
  x.data.get! (i * c + j)

protected
def col! {m n : Nat} {α : Type _} [Inhabited α] (mat : Matrix m n α) (c:Nat) (off : Nat := 0) (len : Nat := n)  : Vector len α :=
  Vector.generate len (λi => mat.get! (off+i) c)

protected
def row! {m n : Nat} {α : Type _} [Inhabited α] (mat : Matrix m n α) (r:Nat) (off : Nat := 0) (len : Nat := n)  : Vector len α :=
  Vector.generate len (λi => mat.get! r (off+i))

instance (r c:Nat) (α: Type _) [Inhabited α] : Inhabited (Matrix r c α) := ⟨Matrix.replicate r c default⟩

protected
def ofRows {m n : Nat} {α} [Inhabited α] (v:Vector m (Vector n α)) : Matrix m n α := Id.run do
  let mut a : Array α := Array.mkEmpty (m*n)
  for i in range 0 m do
    a := a ++ (Vector.get! v i).data
  pure ⟨a, sorry⟩

protected
def ofCols {m n : Nat} {α} [Inhabited α] (v:Vector n (Vector m α)) : Matrix m n α :=
  Matrix.generate _ _ λi j => (v.get j).get i

protected
def unfoldBy {α} (f : Vector c α → Vector c α) (v0:Vector c α) : Matrix (r+1) c α := Id.run do
  let mut m : Array α := Array.mkEmpty (r*c)
  let mut v := v0
  for i in range 0 r do
    m := m ++ v.data
    v := f v
  pure ⟨m ++ v.data, sorry⟩


end Matrix

