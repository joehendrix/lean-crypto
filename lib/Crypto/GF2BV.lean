import Crypto.ToMathlib
import Crypto.BitVec2
import Crypto.GF2Poly

import Smt.Tactic.WHNFSmt

/-! Concrete implementations of GF(2)[X] and GF(2^k) operations as bitvector circuits. -/

namespace GF2BVPoly

/-- Semantic interpretation of a bitvector as a polynomial. -/
def interp (x : BitVec w) : GF2Poly :=
  GF2Poly.mk x.val

-- TODO(WN): might have to define in terms of BV operations
def polyDegree (x : BitVec w) : Nat :=
  (interp x).degree

def polyAdd (a b : BitVec w) : BitVec w := a ^^^ b

/-- Long multiplication in GF(2)[x] translated from Cryptol reference.

```cryptol
pmult : {u, v} (fin u, fin v) => [1 + u] -> [1 + v] -> [1 + u + v]
pmult x y = last zs
  where
    zs = [0] # [ (z << 1) ^ (if yi then 0 # x else 0) | yi <- y | z <- zs ]
``` -/
def polyMul (a : BitVec w) (b : BitVec v) : BitVec (w+v) := Id.run do
  let wOut := w + v
  let_opaque a := a.zeroExtend wOut (Nat.le_add_right _ _)
  let mut ret : BitVec wOut := 0
  -- fold over the bits of b starting at MSB
  for i in List.range v |>.reverse do
    let_opaque tmp := ret <<< 1
    opaque ret := if b.lsbGet i then polyAdd tmp a else tmp
  return ret

def reduce (a : BitVec v) (y : BitVec v) : BitVec v :=
  if a.lsbGet v then polyAdd a y else a

/-- Modulo operation in GF(2)[x] translated from Cryptol reference.

For non-zero b(x), when a(x) = t(x)*b(x) + r(x), mod a b = r.
For zero b(x), we return zero.

```cryptol
pmod : {u, v} (fin u, fin v) => [u] -> [1 + v] -> [v]
pmod x y = if y == 0 then 0/0 else last zs
  where
    degree : [width v]
    degree = last (ds : [2 + v]_)
      where ds = [0/0] # [if yi then i else d | yi <- reverse y | i <- [0..v] | d <- ds ]

    reduce : [1 + v] -> [1 + v]
    reduce u = if u ! degree then u ^ y else u

    powers : [inf][1 + v]
    powers = [reduce 1] # [ reduce (p << 1) | p <- powers ]

    zs = [0] # [ z ^ (if xi then tail p else 0) | xi <- reverse x | p <- powers | z <- zs ]
```
-/
def polyMod (x : BitVec w) (y : BitVec (v+1)) : BitVec v :=
  if y = 0 then 0
  else
    let reduce (a : BitVec (v+1)) : BitVec (v+1) :=
      if a.lsbGet v then polyAdd a y else a
    let_opaque ret : BitVec v := 0
    let_opaque pow : BitVec (v+1) := reduce (BitVec.ofNat (v+1) 1)
    let (ret, _) := List.range w |>.foldl (init := (ret, pow)) fun (ret, pow) i =>
      let_opaque ret := if x.lsbGet i then polyAdd ret (pow.shrink v) else ret
      let_opaque pow := reduce (pow <<< 1)
      (ret, pow)
    ret

section test

-- TODO(WN): We may eventually want to prove these. But to do so, it might make sense
-- to express GF2Poly operations in more abstract terms than the same shifting circuits
-- as given here.
@[reducible]
def is_polyMul_correct (x y : BitVec w) := interp (polyMul x y) = interp x * interp y
@[reducible]
def is_polyMod_correct (x : BitVec w) (y : BitVec (v+1)) := interp (polyMod x y) = interp x % interp y

-- x²+x+1
def a : BitVec 8 := ⟨0b0111, by decide⟩
-- x³+x
def b : BitVec 8 := ⟨0b1010, by decide⟩
-- x⁴+1
def c : BitVec 8 := ⟨0b10001, by decide⟩
-- x³+1
def d : BitVec 8 := ⟨0b01001, by decide⟩
-- x⁷+x+1
def e : BitVec 8 := ⟨0b10000011, by decide⟩

#eval is_polyMul_correct a b
#eval is_polyMul_correct c d
#eval is_polyMod_correct (polyMul a b) e
#eval is_polyMod_correct (polyMul c d) e

end test

end GF2BVPoly

/-! Finite field GF(2^8) -/

/-- An element of the finite field GF(2^8) -/
abbrev GF256 := BitVec 8

namespace GF256

open GF2BVPoly

-- x⁸ + x⁴ + x³ + x + 1
def irreducible : BitVec 9 := BitVec.ofNat 9 0b100011011

def add (a b : GF256) : GF256 := polyAdd a b

def addMany (as : Array GF256) : GF256 :=
  as.foldl (init := BitVec.ofNat 8 0) add

def mul (a b : GF256) : GF256 := polyMod (polyMul a b) irreducible

def pow (k : Nat) (x : GF256) : GF256 :=
  if hEq : k = 0 then BitVec.ofNat 8 1
  else
    have : k / 2 < k := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hEq) (by decide)
    if k % 2 = 0 then sq (pow (k / 2) x)
    else mul x (sq (pow (k / 2) x))
where
  sq (x : GF256) := mul x x

-- NOTE(WN): We have to define this because WHNFSmt reduction of `pow` is buggy
-- and introduces WF encoding internals
/-- `pow2 k = pow (2^k)` -/
def pow2 (k : Nat) (x : GF256) : GF256 :=
  if k = 0 then x
  else
    let_opaque v := pow2 (k-1) x
    mul v v
  
def inverse (x : GF256) : GF256 :=
  -- pow2 254 x
  let v := pow2 7 x
  let v := mul v (pow2 6 x)
  let v := mul v (pow2 5 x)
  let v := mul v (pow2 4 x)
  let v := mul v (pow2 3 x)
  let v := mul v (pow2 2 x)
  let v := mul v (pow2 1 x)
  v

end GF256
