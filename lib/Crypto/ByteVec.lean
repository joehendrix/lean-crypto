import Crypto.ByteArray
import Crypto.UInt8

structure ByteVec (n:Nat) where
  data : ByteArray
  size_proof : data.size = n

namespace ByteVec

def push {n:Nat} (b:UInt8) : ByteVec n → ByteVec (n+1)
| ⟨d, p⟩ => ⟨d.push b, by simp [p]⟩  

def zeros : ∀(n:Nat), ByteVec n
| 0 => ⟨⟨#[]⟩, rfl⟩
| Nat.succ n => (zeros n).push 0

def sequence : ∀(n:Nat), ByteVec n
| 0 => ⟨⟨#[]⟩, rfl⟩
| Nat.succ n => (sequence n).push (OfNat.ofNat n)

theorem eq_of_val_eq {n:Nat} : ∀ {x y : ByteVec n}, Eq x.data y.data → Eq x y
  | ⟨x,_⟩, _, rfl => rfl

theorem val_eq_of_eq {n:Nat} {i j : ByteVec n} (h : Eq i j) : Eq i.data j.data :=
  h ▸ rfl

theorem ne_of_val_ne {n:Nat} {i j : ByteVec n} (h : Not (Eq i.data j.data)) : Not (Eq i j) :=
  λh' => absurd (val_eq_of_eq h') h

def decideEq {n:Nat} : (a b : ByteVec n) → Decidable (Eq a b) :=
  fun i j =>
    match decEq i.data j.data with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

instance (n:Nat): DecidableEq (ByteVec n) := decideEq

protected def toString {n:Nat} (a:ByteVec n) : String := 
  a.data.foldl (λs b => s ++ b.toHex) ""

instance (n:Nat) : ToString (ByteVec n) := ⟨ByteVec.toString⟩ 

instance (n:Nat) : Inhabited (ByteVec n) := ⟨ByteVec.zeros n⟩

protected def fromList (l:List UInt8) : ByteVec (l.length) := ⟨fromList l, by simp⟩

protected def append {m n : Nat} : ByteVec m → ByteVec n → ByteVec (m+n)
| ⟨x,p⟩, ⟨y,q⟩ => ⟨x ++ y, by simp [p,q]⟩

instance (m n : Nat) : HAppend (ByteVec m) (ByteVec n) (ByteVec (m+n)) where
  hAppend := ByteVec.append
  
end ByteVec

syntax "#v[" sepBy(term, ", ") "]" : term

macro_rules
  | `(#v[ $elems,* ]) => `(ByteVec.fromList [ $elems,* ])
