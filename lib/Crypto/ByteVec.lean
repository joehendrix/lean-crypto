import Crypto.ByteArray
import Crypto.ToSubarray
import Crypto.UInt8

structure ByteVec (n:Nat) where
  data : ByteArray
  size_proof : data.size = n

namespace ByteVec

protected def get (x:ByteVec n) (i:Fin n) : UInt8 := x.data.get ⟨i.val, by sorry⟩ 

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

def extract {n:Nat} : ByteVec n → ∀(s e:Nat) , ByteVec (min e n - s)
| ⟨a,p⟩, s, e => ⟨a.extract s e, sorry⟩    

def take {n:Nat} : ∀(b:ByteVec n) (m:Nat), ByteVec (min m n)
| ⟨a,p⟩, m => ⟨a.extract 0 m, sorry⟩    

def drop {n:Nat} : ByteVec n → ∀(m:Nat), ByteVec (n-m)
| ⟨a,p⟩, m => ⟨a.extract m a.size, sorry⟩    

protected def forIn {n:Nat} {β : Type v} {m : Type v → Type w} [Monad m] (x : ByteVec n) (b : β) (f : UInt8 → β → m (ForInStep β)) : m β := 
  x.data.forIn b f

instance : ForIn m (ByteVec n) UInt8 where
  forIn := ByteVec.forIn

instance : ToStream (ByteVec n) ByteSubarray where
  toStream a := toStream a.data


def orAll {n:Nat} (v:ByteVec n) : UInt8 := Id.run $ do
  let mut c := 0
  for b in v do
    c := c ||| b
  pure c

protected def map {n:Nat} (f : UInt8 → UInt8) (x : ByteVec n) : ByteVec n := Id.run do
  let mut r : ByteArray := ByteArray.mkEmpty n
  for a in x do
    r := r.push (f a)
  pure ⟨r, sorry⟩ 

protected def map2 {n:Nat} (f : UInt8 → UInt8 → UInt8) (x y : ByteVec n) : ByteVec n := Id.run do
  let mut r : ByteArray := ByteArray.mkEmpty n
  for a in x, b in y.data do
    r := r.push (f a b)
  pure ⟨r, sorry⟩ 

protected def and1 {n:Nat} (x:UInt8) (y : ByteVec n) : ByteVec n := ByteVec.map (λa => x &&& a) y
protected def and {n:Nat} (x y : ByteVec n) : ByteVec n := ByteVec.map2 AndOp.and x y
protected def or1 {n:Nat} (x:UInt8) (y : ByteVec n) : ByteVec n := ByteVec.map (λa => x ||| a) y
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

end ByteVec

syntax "#v[" sepBy(term, ", ") "]" : term

macro_rules
  | `(#v[ $elems,* ]) => `(ByteVec.fromList [ $elems,* ])

instance : ToSubarray (ByteVec n) ByteSubarray where
  size := λ_ => n
  toSubarray := λv => @ByteArray.toSubarray (v.data)