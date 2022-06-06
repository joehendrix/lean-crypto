import Crypto.BitVec

inductive Kind
| bit : Kind
| vec : Nat → Kind → Kind

export Kind(bit)
export Kind(vec)

namespace Kind

def width : Kind → Nat
| bit => 1
| vec n k => n * k.width

structure Value (k:Kind) : Type where
  bits : BitVec k.width

instance : CoeSort Kind Type where
   coe := Kind.Value

namespace Value

protected def and {K:Kind} (x y : K) : K := ⟨x.bits &&& y.bits⟩

instance {K:Kind}: AndOp K where
  and := Value.and

protected def append {m n : Nat} {K:Kind} (x : vec m K) (y : vec n K) : vec (m+n) K :=
  let r := x.bits ++ y.bits
  let p : (m+n)*K.width = m*K.width + n*K.width := Nat.add_mul _ _ _
  ⟨cast (congrArg BitVec p.symm) r⟩

instance (m n:Nat) (K:Kind) : HAppend (vec m K) (vec n K) (vec (m+n) K) := ⟨Value.append⟩

def toHex {k:Kind} (v:k) := v.bits.toHex

end Value


instance (K:Kind) : Inhabited K.Value := ⟨⟨default⟩⟩

def generateV (n:Nat) {K:Kind} (f : Fin n → K) : vec n K :=
  ⟨BitVec.generateN n (λi => (f i).bits)⟩

protected
def toString : ∀{k:Kind}, Value k → String
| bit, ⟨v⟩ => if v.get! 0 then "1" else "0"
| vec n k, ⟨v⟩ => v.toString

instance (k:Kind) : ToString (Value k) := ⟨Kind.toString⟩


def ofUInt8 (v:UInt8) : vec 8 bit :=
  ⟨⟨ByteArray.fromList [UInt8.ofNat v.toNat], sorry, sorry⟩⟩

def ofUInt16_lbf (v:UInt16) : vec 16 bit :=
  ⟨⟨ByteArray.fromList [UInt8.ofNat v.toNat, UInt8.ofNat (v.toNat >>> 8)], sorry, sorry⟩⟩

def get! {n:Nat} {k:Kind} (v:vec n k) (i:Nat) : k := ⟨v.bits.extractN (i*k.width) k.width⟩

end Kind

-- Creates a vector [0..n)
def byteSequence (n:Nat) : Kind.vec n (Kind.vec 8 bit) :=
  ⟨ByteArray.sequence n, by admit, by admit⟩


