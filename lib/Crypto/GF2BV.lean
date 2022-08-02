import Crypto.ToMathlib
import Crypto.BitVec
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

/-- Data of a finite field of the form GF(2^k).

Inspired by the [implementation](https://github.com/project-everest/hacl-star/blob/0a58b6343c2dac2cd87a17f1ecb8233c3947f856/specs/Spec.GaloisField.fst)
in HACL*. -/
structure GaloisField2k where
  k : Nat
  /-- An irreducible polynomial with degree `k`. Representing it explicitly would require `k+1`
  bits, but we know that the highest one is set, and so need only only store the lower `k` bits.
  So the "real" polynomial is `x^k + GF2BVPoly.interp irred`. -/
  irred : BitVec k

/-- Select the smallest integer type able to contain elements of GF(2^k),
or `BitVec` if no integer type can contain them. -/
-- TODO: Specialize the field operations for these.
def GaloisField2k.uint : Nat → Type
  | 0   => UInt8
  | 9   => UInt16
  | 17  => UInt32
  | 33  => UInt64
  | k+1 =>
    if k < 64 then uint k
    else BitVec (k+1)

instance : CoeSort GaloisField2k Type :=
  ⟨fun F => BitVec F.k⟩

namespace GaloisField2k
open GF2BVPoly

variable {F : GaloisField2k}

instance : OfNat F (nat_lit 0) := ⟨BitVec.ofNat F.k 0⟩
instance : OfNat F (nat_lit 1) := ⟨BitVec.ofNat F.k 1⟩

def add (a b : F) : F := polyAdd a b

instance : Add F := ⟨add⟩

def addMany (as : Array F) : F :=
  as.foldl (init := BitVec.ofNat F.k 0) add

-- TODO: use specialized polyMod instead
def irredFull (F : GaloisField2k) :=
  BitVec.ofNat (F.k+1) (1 <<< F.k) ||| F.irred.zeroExtend (F.k+1) (Nat.le_succ _)

def mul (a b : F) : F := polyMod (polyMul a b) (irredFull F)

instance : Mul F := ⟨mul⟩

def pow (k : Nat) (x : F) : F :=
  if hEq : k = 0 then 1
  else
    have : k / 2 < k := Nat.div_lt_self (Nat.zero_lt_of_ne_zero hEq) (by decide)
    if k % 2 = 0 then sq (pow (k / 2) x)
    else mul x (sq (pow (k / 2) x))
where
  sq (x : F) := mul x x

instance : Pow F Nat := ⟨fun x k => pow k x⟩

def inv (x : F) : F :=
  pow (2^F.k - 1) x

end GaloisField2k

open GaloisField2k

def GF256 : GaloisField2k where
  k := 8
  -- x⁸ + x⁴ + x³ + x + 1
  irred := BitVec.ofNat 8 0b11011

-- NOTE(WN): We would like to unroll the loop in `pow` during specialization in order to create
-- an easier SMT problem, but currently WHNFSmt reduction results in some WF internals. It should
-- apply unfolding theorems instead. Z3 can deal with this variant even without unrolling.
/-- `pow2 k = pow (2^k)` -/
def GF256.pow2 (k : Nat) (x : GF256) : GF256 :=
  if k = 0 then x
  else
    let_opaque v : GF256 := pow2 (k-1) x
    mul v v

def GF256.inv' (x : GF256) : GF256 :=
  -- pow 254 x
  let v := pow2 7 x
  let v := mul v (pow2 6 x)
  let v := mul v (pow2 5 x)
  let v := mul v (pow2 4 x)
  let v := mul v (pow2 3 x)
  let v := mul v (pow2 2 x)
  let v := mul v (pow2 1 x)
  v