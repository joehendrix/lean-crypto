import Crypto.ByteArray
import Crypto.UInt8

structure ByteVec (n:Nat) where
  data : ByteArray
  size_proof : data.size = n

namespace ByteVec

protected def get (x:ByteVec n) (i:Fin n) : UInt8 := x.data.get ⟨i.val, Eq.subst x.size_proof.symm i.isLt⟩

protected def get! (x:ByteVec n) (i:Nat) : UInt8 := x.data.get! i

def push {n:Nat} (b:UInt8) : ByteVec n → ByteVec (n+1)
| ⟨d, p⟩ => ⟨d.push b, by simp [ByteArray.size_push, p]⟩

def zeros (n:Nat) : ByteVec n := ⟨ByteArray.replicate n 0, ByteArray.size_replicate n 0⟩

-- Creates a vector [0..n)
def sequence (n:Nat) : ByteVec n := ⟨ByteArray.sequence n, ByteArray.size_sequence n⟩

theorem eq_of_val_eq {n:Nat} : ∀ {x y : ByteVec n}, Eq x.data y.data → Eq x y
  | ⟨x,_⟩, _, rfl => rfl

theorem ne_of_val_ne {n:Nat} {i j : ByteVec n} (h : Not (Eq i.data j.data)) : Not (Eq i j) :=
  λh' => absurd (h' ▸ rfl) h

protected def decideEq {n:Nat} : (a b : ByteVec n) → Decidable (Eq a b) :=
  fun ⟨i, _⟩ ⟨j, _⟩ =>
    match decEq i j with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

instance (n:Nat): DecidableEq (ByteVec n) := ByteVec.decideEq

protected def toString {n:Nat} (a:ByteVec n) : String :=
  a.data.foldl (λs b => s ++ b.toHex) ""

instance (n:Nat) : ToString (ByteVec n) := ⟨ByteVec.toString⟩

instance (n:Nat) : Inhabited (ByteVec n) := ⟨ByteVec.zeros n⟩

protected def fromList (l:List UInt8) : ByteVec (l.length) := ⟨fromList l, by simp [ByteArray.size_from_list]⟩

protected def append {m n : Nat} : ByteVec m → ByteVec n → ByteVec (m+n)
| ⟨x,p⟩, ⟨y,q⟩ => ⟨x ++ y, by simp [p,q, ByteArray.size_append]⟩

instance (m n : Nat) : HAppend (ByteVec m) (ByteVec n) (ByteVec (m+n)) where
  hAppend := ByteVec.append

def extractN {n:Nat} (a:ByteVec n) (s m:Nat) : ByteVec m :=
  ⟨a.data.extractN s m, a.data.size_extractN s m⟩

def drop {n:Nat} (a:ByteVec n) (m:Nat) : ByteVec (n-m) := a.extractN m (n-m)

def takeFromEnd {n:Nat} (a:ByteVec n) (m:Nat) : ByteVec m := a.extractN (n-m) m

def orAll {n:Nat} (v:ByteVec n) : UInt8 := Id.run $ do
  let mut c := 0
  for b in v.data do
    c := c ||| b
  pure c

def generate (n:Nat) (f:Fin n → UInt8) : ByteVec n :=
  ⟨ByteArray.generate n f, ByteArray.size_generate n f⟩

protected def map {n:Nat} (f : UInt8 → UInt8) (x : ByteVec n) : ByteVec n := generate n (λi => f (x.get i))

protected def map2 {n:Nat} (f : UInt8 → UInt8 → UInt8) (x y : ByteVec n) : ByteVec n := Id.run do
  generate n (λi => f (x.get i) (y.get i))

protected def and1 {n:Nat} (x:UInt8) (y : ByteVec n) : ByteVec n := ByteVec.map (λa => x &&& a) y


protected def or1 {n:Nat} (x:UInt8) (y : ByteVec n) : ByteVec n := ByteVec.map (λa => x ||| a) y

protected def and {n:Nat} (x y : ByteVec n) : ByteVec n := ByteVec.map2 AndOp.and x y
protected def or  {n:Nat} (x y : ByteVec n) : ByteVec n := ByteVec.map2 OrOp.or x y
protected def xor {n:Nat} (x y : ByteVec n) : ByteVec n := ByteVec.map2 Xor.xor x y

instance : HAnd UInt8 (ByteVec n) (ByteVec n) where
  hAnd := ByteVec.and1

instance : HAnd (ByteVec n) UInt8 (ByteVec n) where
  hAnd := λx y => ByteVec.and1 y x

instance : AndOp (ByteVec n) where
  and := ByteVec.and

instance : HOr UInt8 (ByteVec n) (ByteVec n) where
  hOr := ByteVec.or1

instance : HOr (ByteVec n) UInt8 (ByteVec n) where
  hOr := λx y => ByteVec.or1 y x

instance : OrOp (ByteVec n) where
  or := ByteVec.or

instance : Xor (ByteVec n) where
  xor := ByteVec.xor

def ofUInt64lsb (v:UInt64) : ByteVec 8 :=
  let byte (i:UInt64) : UInt8 := OfNat.ofNat (v >>> (8 * i)).toNat
  ByteVec.fromList [byte 0, byte 1, byte 2, byte 3, byte 4, byte 5, byte 6, byte 7]


end ByteVec


--structure UInt16Vec (n:Nat) where
--  data : Array
--  size_proof : data.size = n

--namespace ByteVec

syntax "#v[" sepBy(term, ", ") "]" : term

macro_rules
  | `(#v[ $elems,* ]) => `(ByteVec.fromList [ $elems,* ])


