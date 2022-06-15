import Crypto.ToMathlib
import Crypto.BitVec2
import Crypto.GF2Poly

/-! Concrete implementations of GF(2)[X] and GF(2^k) operations as Boolean circuits. -/

namespace BitVec

instance : OfNat (BitVec w) (nat_lit 0) :=
  ⟨BitVec.zero w⟩

/-- Shrink or extend with zeros. -/
def zeroShrinxtend (x : BitVec w) (v : Nat) : BitVec v :=
  if h : w < v then ⟨x.val, Nat.lt_trans x.isLt sorry⟩
  else ⟨x.val % (2^v), Nat.mod_lt _ sorry⟩

end BitVec

namespace GF2Poly

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
def polyMul (a : BitVec w) (b : BitVec v) : BitVec (w+v) :=
  let wOut := w + v
  let a := a.zeroShrinxtend wOut
  -- fold over the bits of b starting at MSB
  let ret : BitVec wOut := List.range v |>.foldr (init := 0) fun i acc =>
    let acc' := acc <<< 1
    if b.lsb_get! i then acc' ^^^ a else acc'
  ret

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
  else Id.run do
    let mut ret : BitVec v := 0
    let reduce (a : BitVec (v+1)) : BitVec (v+1) := if a.lsb_get! 7 /- HACK -/ then polyAdd a y else a
    let mut pow : BitVec (v+1) := reduce ⟨1, by
      show 1 * 2 ≤ 2^v * 2
      exact Nat.mul_le_mul_right 2 <| Nat.succ_le_of_lt <| Nat.pos_pow_of_pos _ <| by decide⟩
    for i in List.range w do
      if x.lsb_get! i then ret := polyAdd ret (pow.zeroShrinxtend v)
      pow := reduce (pow <<< 1)
    return ret

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

end GF2Poly
