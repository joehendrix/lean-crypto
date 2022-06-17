import Crypto.Range
import Crypto.UInt8
import Crypto.ToMathlib

/-!
We define bitvectors in two variants - indexed and packed. The indexed variant is helpful
for stating strongly-typed interfaces, whereas the packed one is better for stating some
properties without the dependent index getting in the way.
-/

def BitVec (w : Nat) := Fin (2^w)

@[ext]
structure BitVec.Packed where
  width : Nat
  data  : Fin (2^width)

namespace BitVec
namespace Packed

@[ext]
theorem ext' {a b : Packed} (hWidth : a.width = b.width)
    (hData : a.data.val = b.data.val) : a = b := by
  let ⟨aw, ad, _⟩ := a
  let ⟨bw, bd, _⟩ := b
  cases hWidth
  cases hData
  rfl

end Packed

protected def zero (w : Nat) : BitVec w :=
  ⟨0, Nat.pos_pow_of_pos _ <| by decide⟩

instance : Inhabited (BitVec w) := ⟨BitVec.zero w⟩

protected def append (x : BitVec w) (y : BitVec v) : BitVec (w+v) :=
  ⟨x.val <<< v ||| y.val, sorry⟩

instance : HAppend (BitVec w) (BitVec v) (BitVec (w+v)) where
  hAppend := BitVec.append

protected def and (x y : BitVec w) : BitVec w :=
  ⟨x.val &&& y.val, sorry⟩
protected def or (x y : BitVec w) : BitVec w :=
  ⟨x.val ||| y.val, sorry⟩
protected def xor (x y : BitVec w) : BitVec w :=
  ⟨x.val ^^^ y.val, sorry⟩
protected def shiftLeft (x : BitVec w) (n : Nat) : BitVec w :=
  Fin.ofNat' (x.val <<< n) (Nat.pos_pow_of_pos _ (by decide))
protected def shiftRight (x : BitVec w) (n : Nat) : BitVec w :=
  ⟨x.val >>> n, sorry⟩

instance : AndOp (BitVec w) := ⟨BitVec.and⟩
instance : OrOp (BitVec w) := ⟨BitVec.or⟩
instance : Xor (BitVec w) := ⟨BitVec.xor⟩
instance : HShiftLeft (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftLeft⟩
instance : HShiftRight (BitVec w) Nat (BitVec w) := ⟨BitVec.shiftRight⟩

def lsb_get! (x : BitVec m) (i : Nat) : Bool :=
  (x.val &&& (1 <<< i)) ≠ 0

def lsb_set! (x : BitVec m) (i : Nat) (c : Bool) : BitVec m :=
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

def msbb_set! (x : BitVec m) (i : Nat) (c : Bool) : BitVec m :=
  x.lsb_set! (msbb_fix m i) c

protected def toBinary (x : BitVec n) : String :=
  let l := Nat.toDigits 2 x.val
  "0b" ++ String.mk (List.replicate (n - l.length) '0' ++ l)

protected def toHex (x : BitVec n) : String :=
  let l := Nat.toDigits 16 x.val
  "0x" ++ String.mk (List.replicate (n/4 - l.length) '0' ++ l)

protected def toHex2 (x : BitVec n) : String := Id.run do
  let mut s : String := "0x"
  for i in range 0 (n/8) do
    let b := UInt8.ofNat (x.val >>> (8*i))
    s := s ++ b.toHex
  pure s

instance : ToString (BitVec n) := ⟨BitVec.toHex2⟩

def reverse (x : BitVec n) : BitVec n := Id.run do
  let mut r : Nat := 0
  for i in range 0 n do
    r := r <<< 1
    if x.lsb_get! i then
      r := r + 1
  pure ⟨r, sorry⟩

protected def foldl (f : α → Bool → α) (x : BitVec n) (a : α) : α := Id.run do
  let mut r := a
  for i in range 0 n do
    r := f r (x.msbb_get! i)
  pure r

protected def take_lsb (x : BitVec m) (n : Nat) : BitVec n :=
  ⟨x.val &&& 1 <<< n - 1, sorry⟩

protected def take_msb (x : BitVec m) (n : Nat) : BitVec n :=
  ⟨x.val >>> (m-n), sorry⟩

theorem eq_of_val_eq : ∀ {x y : BitVec n}, x.val = y.val → x = y
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

  for i in range 0 (n/8) do
    let mut w : Nat := 0
    for j in range 0 8 do
      let b := f ⟨8*i+j, sorry⟩
      w := if b then 1 <<< j ||| w else w
    r := w <<< (8*i) ||| r

  let m := n % 8
  if m ≠ 0 then
    let mut w : Nat := 0
    for j in range 0 m do
      let b := f ⟨8*(n/8) + j, sorry⟩
      w := if b then 1 <<< j ||| w else w
    r := w <<< (8*(n/8)) ||| r
  ⟨r, sorry⟩

protected def generate_msbb (n : Nat) (f : Fin n → Bool) : BitVec n := Id.run do
  let mut r : Nat := 0

  let m := n % 8
  if m ≠ 0 then
    let mut w : Nat := 0
    for j in range 0 m do
      let b := f ⟨j, sorry⟩
      w := if b then 1 <<< j ||| w else w
    r := w

  for i in range 0 (n/8) do
    let mut w : Nat := 0
    for j in range 0 8 do
      let b := f ⟨m+8*i+j, sorry⟩
      w := if b then 1 <<< j ||| w else w
    r := r <<< 8 ||| w

  ⟨r, sorry⟩

end BitVec