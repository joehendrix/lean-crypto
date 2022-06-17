import Crypto.Bool
import Crypto.ToMathlib
import Mathlib.Algebra.Ring.Basic

/-! A concrete (computable) implementation of GF(2) (aka ℤ/2ℤ) as Booleans
and the polynomial ring GF(2)[X] as binary numbers. -/

/-- The two-element finite field. -/
structure GF2 where
  val : Bool
  deriving DecidableEq

namespace GF2

instance : Coe Bool GF2 :=
  ⟨GF2.mk⟩

instance : Add GF2 where
  add a b := ⟨a.val ^^^ b.val⟩
instance : Mul GF2 where
  mul a b := ⟨a.val && b.val⟩
instance : OfNat GF2 (nat_lit 0) :=
  ⟨⟨Bool.false⟩⟩
instance : OfNat GF2 (nat_lit 1) :=
  ⟨⟨Bool.true⟩⟩

instance : Repr GF2 where
  reprPrec x _ := toString x.val

end GF2

/-- The univariate polynomial ring in X over GF(2).

We represent each polynomial as its coefficients encoded in binary with LSB endianness.
This is a unique normal form. For example, 1x³ + 0x² + 1x¹ + 1 is `0b1011`. -/
-- NOTE(WN): I think this is mathematically the best representation because of uniqueness.
-- Representations such as `BitVec n` or `List Bool` have to be quotiented by the width first,
-- since e.g. `0b00001111` and `0b1111` represent the same polynomial.
@[ext]
structure GF2Poly where
  bits : Nat
  deriving DecidableEq

namespace GF2Poly

def ofBits : Nat → GF2Poly :=
  GF2Poly.mk

instance : OfNat GF2Poly (nat_lit 0) :=
  ⟨ofBits 0⟩
instance : OfNat GF2Poly (nat_lit 1) :=
  ⟨ofBits 1⟩

/-- The indeterminate. -/
def X : GF2Poly :=
  ofBits 0b10

def coeffs (p : GF2Poly) : List GF2 :=
  go p.bits
where go (p : Nat) : List GF2 :=
  if h : p = 0 then []
  else
    have : p >>> 1 < p := by
      rw [← Nat.div_two_pow_eq_shiftRight]
      exact Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (Nat.lt_succ_self _)
    (p &&& 1 == 1) :: go (p >>> 1)

def coeff (p : GF2Poly) (i : Nat) : GF2 :=
  (p.bits >>> i) &&& 1 == 1

theorem coeff_eq_coeffs_get (p : GF2Poly) (i : Nat) : p.coeff i = p.coeffs.getD i 0 :=
  sorry

instance : Repr GF2Poly where
  reprPrec p _ :=
    let cs := p.coeffs
    if cs = [] then "0"
    else go <| List.range cs.length |>.zip cs
where
  go : List (Nat × GF2) → String
    | [] => ""
    | (_, 0) :: cs => go cs
    | (i, 1) :: cs =>
      let t := if i = 0 then "1" else s!"X^{i}"
      let ts := go cs
      s!"{t}{if !ts.isEmpty then " + " else ""}{ts}"

/-- The polynomial degree. A total function, but only meaningful when `p ≠ 0`. -/
def degree (p : GF2Poly) : Nat :=
  p.coeffs.length - 1

@[simp]
def add (p q : GF2Poly) : GF2Poly :=
  ⟨p.bits ^^^ q.bits⟩

instance : Add GF2Poly := ⟨add⟩
instance : Neg GF2Poly := ⟨id⟩

lemma add_degree (p q : GF2Poly) : (p + q).degree ≤ max p.degree q.degree := sorry

def mul (p q : GF2Poly) : GF2Poly :=
  q.coeffs.foldr (init := 0) fun qc acc =>
    let acc' : GF2Poly := ofBits (acc.bits <<< 1)
    if qc = (1 : GF2) then acc' + p else acc'

instance : Mul GF2Poly := ⟨mul⟩

theorem mul_degree (p q : GF2Poly) : (p * q).degree ≤ p.degree + q.degree := sorry

def pow (p : GF2Poly) (n : Nat) : GF2Poly :=
  if h : n = 0 then 1
  else if n % 2 == 0 then
    have : n / 2 < n := Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (Nat.lt_succ_self _)
    let v := pow p (n / 2)
    v * v
  else
    p * pow p (n - 1)

instance : Pow GF2Poly Nat := ⟨pow⟩

def mod (p q : GF2Poly) : GF2Poly :=
  if q = 0 then 0
  else Id.run do
    let mut ret := 0
    let reduce (x : GF2Poly) := if x.coeff q.degree = 1 then x + q else x
    let mut pow := reduce 1
    for pc in p.coeffs do
      if pc = (1 : GF2) then ret := ret + pow
      pow := reduce <| ofBits (pow.bits <<< 1)
    return ret

instance : Mod GF2Poly := ⟨mod⟩

-- NOTE(WN): If implemented correctly, this should be ring-isomorphic to mathlib's `polynomial GF2`
instance : CommRing GF2Poly where
  add_zero           := sorry
  zero_add           := sorry
  add_comm           := sorry
  add_assoc          := sorry
  add_left_neg       := sorry
  mul_zero           := sorry
  zero_mul           := sorry
  mul_one            := sorry
  one_mul            := sorry
  mul_comm           := sorry
  mul_assoc          := sorry
  left_distrib       := sorry
  right_distrib      := sorry
  npow_zero' n       := sorry
  npow_succ' n x     := sorry
  nsmul n p          := sorry
  nsmul_zero'        := sorry
  nsmul_succ' n x    := sorry
  sub_eq_add_neg a b := sorry
  gsmul n p          := sorry
  gsmul_zero'        := sorry
  gsmul_succ' n x    := sorry
  gsmul_neg' n x     := sorry
  natCast            := sorry
  natCast_zero       := sorry
  natCast_succ _     := sorry
  intCast            := sorry
  intCast_ofNat _    := sorry
  intCast_negSucc _  := sorry

-- NOTE(WN): should also have EuclideanDomain GF2Poly
 
namespace test

def a : GF2Poly := X^3 + X^2 + X
def b : GF2Poly := X^3 + X^2

#eval a * b == X^6 + X^3

def c : GF2Poly := X^2 + X + 1
def d : GF2Poly := X^3 + X
def e : GF2Poly := X^4 + 1
def f : GF2Poly := X^3 + 1
def g : GF2Poly := X^7 + X +1

#eval (c * d) % e == X^2 + 1
#eval (f * e) % g == X^4 + X^3 + X^1

end test

end GF2Poly