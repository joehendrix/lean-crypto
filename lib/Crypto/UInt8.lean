namespace UInt8

def testBit (w:UInt8) (i:Nat) : Bool :=
  let mask := 1 <<< i
  w.toNat &&& mask = mask

def toBitsAux (c : UInt8) : String → Nat → String
| s, Nat.zero => s
| s, Nat.succ i =>
  let w := if c.testBit i then "1" else "0"
  toBitsAux c (s ++ w) i

def toHex (x : UInt8) : String :=
  let l := (Nat.toDigits 16 x.toNat).map Char.toUpper
  String.mk (List.replicate (2 - l.length) '0' ++ l)

end UInt8

def UInt64.toHex (x:UInt64) : String :=
  let l := Nat.toDigits 16 x.toNat
  String.mk (List.replicate (16 - l.length) '0' ++ l)
