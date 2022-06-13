import Crypto.Range
import Crypto.UInt8

def BitVec (n:Nat) := Fin (2^n)

namespace BitVec

protected def zero (n:Nat) : BitVec n := ⟨0, sorry⟩

instance : Inhabited (BitVec n) := ⟨BitVec.zero n⟩

protected def append {m n:Nat} (x:BitVec m) (y:BitVec n) : BitVec (m+n) :=
  ⟨x.val <<< n ||| y.val, sorry⟩

instance : HAppend (BitVec m) (BitVec n) (BitVec (m+n)) where
  hAppend := BitVec.append

protected def and (x y : BitVec n) : BitVec n := ⟨x.val &&& y.val, sorry⟩
protected def or  (x y : BitVec n) : BitVec n := ⟨x.val ||| y.val, sorry⟩
protected def xor (x y : BitVec n) : BitVec n := ⟨x.val ^^^ y.val, sorry⟩

instance : AndOp (BitVec n) := ⟨BitVec.and⟩
instance : OrOp (BitVec n) := ⟨BitVec.or⟩
instance : Xor (BitVec n) := ⟨BitVec.xor⟩

def lsb_get! {m:Nat} (x:BitVec m) (i:Nat) : Bool :=
  (x.val &&& (1 <<< i)) ≠ 0

def lsb_set! {m:Nat} (x:BitVec m) (i:Nat) (c:Bool) : BitVec m :=
  if c then
    x ||| ⟨1 <<< i, sorry⟩
  else
    x &&& ⟨((1 <<< m) - 1 - (1 <<< i)), sorry⟩

/--
Update index to use most-significant bytes, but least-significant bit
ordering within bytes.

This may be removed once compatibility with C is not needed.
-/
def msbb_fix (m:Nat) (i:Nat) : Nat :=
  let j := (m-1)-i
  -- Reverse bit order within bytes (see if we can fix this)
  ((j >>> 3) <<< 3) ||| (0x7 - (j &&& 0x7))

def msbb_get! {m:Nat} (x:BitVec m) (i:Nat) : Bool := x.lsb_get! (msbb_fix m i)

def msbb_set! {m:Nat} (x:BitVec m) (i:Nat) (c:Bool) : BitVec m :=
  x.lsb_set! (msbb_fix m i) c

protected def toBinary (x:BitVec n) : String :=
  let l := Nat.toDigits 2 x.val
  String.mk (List.replicate (n - l.length) '0' ++ l)

protected def toHex (x:BitVec n) : String :=
  let l := Nat.toDigits 16 x.val
  String.mk (List.replicate (n/4 - l.length) '0' ++ l)

protected def toHex2 (x:BitVec n) : String := Id.run do
  let mut s : String := ""
  for i in range 0 (n/8) do
    let b := UInt8.ofNat (x.val >>> (8*i))
    s := s ++ b.toHex
  pure s
instance : ToString (BitVec n) := ⟨BitVec.toHex2⟩

def reverse (x:BitVec n) : BitVec n := Id.run do
  let mut r : Nat := 0
  for i in range 0 n do
    r := r <<< 1
    if x.lsb_get! i then
      r := r + 1
  pure ⟨r, sorry⟩

protected def foldl (f: α → Bool → α) (x: BitVec n) (a : α) : α := Id.run do
  let mut r := a
  for i in range 0 n do
    r := f r (x.msbb_get! i)
  pure r

protected def take_lsb (x:BitVec m) (n:Nat) : BitVec n :=
  ⟨x.val &&& 1 <<< n - 1, sorry⟩

protected def take_msb (x:BitVec m) (n:Nat) : BitVec n :=
  ⟨x.val >>> (m-n), sorry⟩

theorem eq_of_val_eq {n:Nat} : ∀ {x y : BitVec n}, Eq x.val y.val → Eq x y
  | ⟨x,_⟩, _, rfl => rfl

theorem ne_of_val_ne {n:Nat}  {i j : BitVec n} (h : Not (Eq i.val j.val)) : Not (Eq i j) :=
  λh' => absurd (h' ▸ rfl) h

protected def decideEq {n:Nat} : (a b : BitVec n) → Decidable (Eq a b) :=
  fun ⟨i, _⟩ ⟨j, _⟩ =>
    match decEq i j with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

instance (n:Nat) : DecidableEq (BitVec n) := BitVec.decideEq

protected def generate_lsb (n:Nat) (f : Fin n → Bool) : BitVec n := Id.run do
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

protected def generate_msbb {n:Nat} (f : Fin n → Bool) : BitVec n := Id.run do
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