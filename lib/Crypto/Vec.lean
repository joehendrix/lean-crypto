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

def Value (k:Kind) : Type := BitVec k.width

instance : CoeSort Kind Type where
   coe := Kind.Value

protected
def toString : ∀{k:Kind}, Value k → String
| bit, v => if v.get! 0 then "1" else "0"
| vec n k, v => v.toString

instance (k:Kind) : ToString (Value k) := ⟨Kind.toString⟩

--protected
--def get! {n:Nat} {k:Kind} (a:vec n k) (i:Nat) : k := a.slice (i * k.width) k.width

end Kind

-- Creates a vector [0..n)
def byteSequence (n:Nat) : Kind.vec n (Kind.vec 8 bit) :=
  ⟨ByteArray.sequence n, by admit⟩