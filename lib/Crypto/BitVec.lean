import Crypto.Range
import Crypto.UInt8
import Crypto.ToMathlib

import Smt.Data.BitVec

namespace BitVec

def get_lsb (x : BitVec m) (i : Fin m) : Bool :=
  (x.val &&& (1 <<< i.val)) ≠ 0

def lsb_getAux (x : BitVec m) (i : Nat) : Bool :=
  (x.val &&& (1 <<< i)) ≠ 0

@[implementedBy lsb_getAux]
def lsb_get! (x : BitVec m) (i : Nat) : Bool :=
  BitVec.lsbGet x i

def lsb_set! (x : BitVec m) (i : Nat) (c : Bool) : BitVec m :=
  if c then
    x ||| ⟨1 <<< i, sorry⟩
  else
    x &&& ⟨((1 <<< m) - 1 - (1 <<< i)), sorry⟩

def get_msb (x : BitVec m) (i : Fin m) : Bool :=
  (x.val &&& (1 <<< (m-1-i.val))) ≠ 0

def msb_get! (x : BitVec m) (i : Nat) : Bool :=
  (x.val &&& (1 <<< (m-1-i))) ≠ 0

def msb_set! (x : BitVec m) (i : Nat) (c : Bool) : BitVec m :=
  let i  := m-1-i
  if c then
    x ||| ⟨1 <<< i, sorry⟩
  else
    x &&& ⟨((1 <<< m) - 1 - (1 <<< i)), sorry⟩

/--
Update index to use most-significant bytes, but least-significant bit
ordering within bytes.

This may be removed once compatibility with C is not needed.
-/
def msbb_fix (m : Nat) (i : Nat) : Nat :=
  let j := (m-1)-i
  -- Reverse bit order within bytes (see if we can fix this)
  ((j >>> 3) <<< 3) ||| (0x7 - (j &&& 0x7))

def msbb_get! (x : BitVec m) (i : Nat) : Bool := x.lsb_get! (msbb_fix m i)

protected def toBinary (x : BitVec n) : String :=
  let l := Nat.toDigits 2 x.val
  "0b" ++ String.mk (List.replicate (n - l.length) '0' ++ l)

protected def toHex (x : BitVec n) : String :=
  let l := Nat.toDigits 16 x.val
  "0x" ++ String.mk (List.replicate (n/4 - l.length) '0' ++ l)

def reverse (x : BitVec n) : BitVec n := Id.run do
  let mut r : Nat := 0
  for i in range 0 n do
    r := r <<< 1
    if x.lsb_get! i then
      r := r + 1
  pure ⟨r, sorry⟩

-- Fold that visits least-significant bit first.
protected def fold_lsb (f : α → Bool → α) (x : BitVec n) (a : α) : α := Id.run do
  let mut r := a
  let mut v := x.val
  for _i in range 0 n do
    r := f r ((v &&& 1) = 1)
    v := v >>> 1
  pure r

protected def take_lsb (x : BitVec m) (n : Nat) : BitVec n :=
  ⟨x.val &&& 1 <<< n - 1, sorry⟩

protected def take_msb (x : BitVec m) (n : Nat) : BitVec n :=
  ⟨x.val >>> (m-n), sorry⟩

def extractN! (a:BitVec n) (s m:Nat) : BitVec m :=
  let e := s + m
  let b := (a.val >>> (n - e)) &&& (1 <<< (min m (n - s)) - 1)
  ⟨b, sorry⟩

theorem eq_of_val_eq {n:Nat} : ∀{x y : BitVec n}, x.val = y.val → x = y
  | ⟨_,_⟩, _, rfl => rfl

theorem ne_of_val_ne {x y : BitVec n} (h : x.val ≠ y.val) : x ≠ y :=
  λ h' => absurd (h' ▸ rfl) h

protected def decideEq : (x y : BitVec n) → Decidable (x = y) :=
  fun ⟨i, _⟩ ⟨j, _⟩ =>
    match decEq i j with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

instance : DecidableEq (BitVec n) := BitVec.decideEq

protected def generate_lsb (n : Nat) (f : Fin n → Bool) : BitVec n := Id.run do
  let mut r : Nat := 0

  for i in range 0 n do
    let b := f ⟨i, sorry⟩
    r := (if b then 1 <<< i else 0) ||| r

  ⟨r, sorry⟩

protected def generate_msb (n : Nat) (f : Fin n → Bool) : BitVec n := Id.run do
  let mut r : Nat := 0

  for i in range 0 n do
    let b := f ⟨i, sorry⟩
    r := r <<< 1 ||| (if b then 1 else 0)

  ⟨r, sorry⟩

  def toUInt8  (x:BitVec  8) : UInt8  := OfNat.ofNat x.val
  def toUInt16 (x:BitVec 16) : UInt16 := OfNat.ofNat x.val
  def toUInt32 (x:BitVec 32) : UInt32 := OfNat.ofNat x.val
  def toUInt64 (x:BitVec 64) : UInt64 := OfNat.ofNat x.val

  protected def toString {n:Nat} (x:BitVec n) : String :=
    if n % 16 = 0 then
      let s := (Nat.toDigits 16 x.val).asString
      let t := (List.repeat' '0' (n / 16 - s.length)).asString
      "0x" ++ t ++ s
    else
      let s := (Nat.toDigits 2 x.val).asString
      let t := (List.repeat' '0' (n - s.length)).asString
      "0b" ++ t ++ s

  instance : ToString (BitVec n) := ⟨BitVec.toString⟩

end BitVec

namespace UInt8
  def toBitVec (x:UInt8) : BitVec 8 := ⟨x.toNat, x.val.isLt⟩
end UInt8

namespace UInt16
  def toBitVec (x:UInt16) : BitVec 16 := ⟨x.toNat, x.val.isLt⟩
end UInt16

namespace UInt32
  def toBitVec (x:UInt32) : BitVec 32 := ⟨x.toNat, x.val.isLt⟩
end UInt32

namespace UInt64
  def toBitVec (x:UInt64) : BitVec 64 := ⟨x.toNat, x.val.isLt⟩
end UInt64