-- This is an old BitVec implementation using byte arrays
-- It should be completely replaced with Crypto.BitVec2
import Crypto.ByteArray
import Crypto.UInt8

def BitVec.msbMask (n:Nat) : UInt8 :=
  if n % 8 == 0 then
    0xFF
  else
    (1 <<< OfNat.ofNat (n % 8)) - 1

structure BitVec (n:Nat) where
  data : ByteArray
  size_proof : data.size = (n+7)/8
  -- Most significant bit should satisfy mask.
  msb_proof  : data.get! 0 &&& BitVec.msbMask n = data.get! 0

namespace List

theorem replicate_get (n:Nat) (c:α) : ∀(i:Fin (length (replicate n c))), (replicate n c).get i = c := by
  induction n with
  | zero =>
    intro ⟨i, p⟩
    simp [length, replicate] at p
    contradiction
  | succ n nh =>
    intro ⟨i, p⟩
    simp [replicate]
    cases i with
    | zero =>
      simp [get]
    | succ i =>
      simp [get, nh]

end List


namespace ByteArray

theorem get!_replicate (i n: Nat) (c:UInt8)
    : (replicate n c).get! i = if i < n then c else default := by
  simp [ByteArray.replicate, fromList, ByteArray.fromList]
  simp [get!, Array.get!, Array.getD, Array.get, Array.size]
  simp [List.replicate_get]
  trivial

end ByteArray

namespace UInt8

theorem default_is_zero : (default : UInt8) = 0 := rfl

theorem zero_and (x:UInt8) : 0 &&& x = 0 := by admit

end UInt8


namespace BitVec

protected def zeros (n:Nat) : BitVec n :=
  { data := ByteArray.replicate ((n+7)/8) 0,
    size_proof := by simp [ByteArray.size_replicate],
    msb_proof := by
      simp [ByteArray.get!_replicate]
      simp [UInt8.default_is_zero, UInt8.zero_and]
  }

instance (n:Nat) : Inhabited (BitVec n) := ⟨BitVec.zeros n⟩

-- Get with most-significant bit first.
protected def get! (x:BitVec n) (i:Nat) : Bool :=
  let off := i / 8
  let byte := x.data.get! off
  let mod := UInt8.ofNat (i % 8)
  let mask := 1 <<< (7 - mod)
  (byte &&& mask) == mask

protected def toHex {n:Nat} (a:BitVec n) : String := a.data.foldl (λs b => s ++ b.toHex) ""

protected def toBits {n:Nat} (a:BitVec n) : String :=
  let firstByte := a.data.get! 0
  let startStr := firstByte.toBits (n % 8)
  a.data.foldl (λs b => s ++ b.toBits) startStr 1


protected def toString {n:Nat} (a:BitVec n) : String :=
  if n % 4 == 0 then
    "Ox" ++ a.toHex
  else
    "0b" ++ a.toBits

instance (n:Nat) : ToString (BitVec n) := ⟨BitVec.toString⟩

def firstByteFilter (n i :Nat) (v:UInt8) : UInt8 :=
  if i = 0 then
    v &&& msbMask n
  else
    v

def extractN {n:Nat} (a:BitVec n) (s m:Nat) : BitVec m :=
  let so := s / 8
  let sm := UInt8.ofNat (s % 8)
  let byteCount := (m + 7) / 8 + 1
  let f := if sm = 0 then
             λ(i : Fin byteCount) => a.data.get! (so + i.val)
           else
             λ(i : Fin byteCount) =>
               (a.data.get! (so + i.val) <<< sm)
               ||| (a.data.get! (so + i.val + 1) >>> (8-sm))
  let g := if m % 8 = 0 then
             f
            else
              λ(i : Fin byteCount) => firstByteFilter m i.val (f i)
  { data := ByteArray.generate byteCount f,
    size_proof := sorry,
    msb_proof := sorry
  }

def generateN (m:Nat) {n:Nat} (f:Fin m → BitVec n) : BitVec (m*n) :=
  let byteCount := (m*n + 7) / 8 + 1
  if n % 8 = 0 then
    let a : ByteArray := ByteArray.mkEmpty byteCount
    let loop (i:Fin m) (a:ByteArray) : ByteArray := a ++ (f i).data
    let a := foreachFin m loop a
    { data := a, size_proof := sorry, msb_proof := sorry }
  else
    panic! "BitVec.generateN does not yet support non-multiples of 8."

def map2Bytes {n:Nat} (f : UInt8 → UInt8 → UInt8) (x y: BitVec n) : BitVec n :=
  { data := ByteArray.generate ((n+7)/8) (λi => f (x.data.get! i) (y.data.get! i)), size_proof := sorry, msb_proof := sorry }


protected def and {n:Nat} (x y: BitVec n) : BitVec n := map2Bytes AndOp.and x y
protected def or  {n:Nat} (x y: BitVec n) : BitVec n := map2Bytes OrOp.or   x y
protected def xor {n:Nat} (x y: BitVec n) : BitVec n := map2Bytes Xor.xor   x y

instance {n:Nat} : AndOp (BitVec n) := ⟨BitVec.and⟩
instance {n:Nat} : OrOp (BitVec n) := ⟨BitVec.or⟩
instance {n:Nat} : Xor (BitVec n) := ⟨BitVec.xor⟩

protected def append {m n : Nat} (x : BitVec m) (y : BitVec n) : BitVec (m+n) :=
  if n % 8 = 0 then
    { data := x.data ++ y.data, size_proof := sorry, msb_proof := sorry }
  else
    panic! "BitVec.append not yet fully implemented."

instance : HAppend (BitVec m) (BitVec n) (BitVec (m+n)) := ⟨BitVec.append⟩

end BitVec