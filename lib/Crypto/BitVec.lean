import Crypto.ByteArray
import Crypto.UInt8

structure BitVec (n:Nat) where
  data : ByteArray
  size_proof : data.size = (n+7)/8

namespace BitVec

protected def zeros (n:Nat) : BitVec n := ⟨ByteArray.replicate ((n+7)/8) 0, by simp [ByteArray.size_replicate]⟩

instance (n:Nat) : Inhabited (BitVec n) := ⟨BitVec.zeros n⟩

-- Get with most-significant bit first.
protected def get! (x:BitVec n) (i:Nat) : Bool :=
  let off := i / 8
  let byte := x.data.get! off
  let mod := UInt8.ofNat (i % 8)
  let mask := 1 <<< (7 - mod)
  (byte &&& mask) == mask


protected def toHex {n:Nat} (a:BitVec n) : String := a.data.foldl (λs b => s ++ b.toHex) ""

protected def toString {n:Nat} (a:BitVec n) : String :=
  if n % 4 == 0 then
    "Ox" ++ a.toHex
  else
    let firstByte := a.data.get! 0
    let startStr := "0b" ++ firstByte.toBits (n % 8)
    a.data.foldl (λs b => s ++ b.toBits) startStr 1

instance (n:Nat) : ToString (BitVec n) := ⟨BitVec.toString⟩

end BitVec