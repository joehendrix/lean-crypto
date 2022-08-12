import Crypto
import Smt

/-! Optimized Galois field operations in McEliece are the same as generic reference algorithm. -/

namespace Mceliece.Ref348864

def GF4096 : GaloisField2k where
  k := 12
  -- x^12 + x^3 + 1
  irred := BitVec.ofNat 12 0b1001

def GF4096.ofGF (x : GF) : GF4096 :=
  BitVec.shrink (w := 16) 12 x.val.val

open Smt Term Translator in
/-- Translate `{x : α // _}` as `α`. -/
@[smtTranslator]
def translateSubtype : Translator
  | .app (.app (.const ``Subtype _) e) _ =>
    applyTranslators! e
  | .app (.app (.app (.const ``Subtype.val _) _) _) e => do
    applyTranslators! e
  | .app (.app (.app (.app (.const ``Subtype.mk _) _) _) e) _ => do
    applyTranslators! e
  | _ => return none

open Lean Smt Term Translator in
/-- Translate `UIntXY` as `BitVec XY`.
It may be better to use an isomorphism-transfer tactic first, and then just the standard `BitVec`
translation. -/
@[smtTranslator]
def translateUInt : Translator
  | .const ``UInt16 _ =>
    return mkApp2 (symbolT "_") (symbolT "BitVec") (literalT "16")
  | .app (.const ``UInt16.val _) e =>
    applyTranslators! e
  | e@(.app (.const ``UInt16.ofNat _) n) => do
    let n ← reduceLit n e
    return Smt.BitVec.mkLit 16 n
  | .const ``UInt16.add _        => return symbolT "bvadd"
  | .const ``UInt16.sub _        => return symbolT "bvsub" -- QF_BV
  | .const ``UInt16.mul _        => return symbolT "bvmul"
  | .const ``UInt16.div _        => return symbolT "bvudiv"
  | .const ``UInt16.mod _        => return symbolT "bvurem"
  | .const ``UInt16.modn _       => throwError "unknown"
  | .const ``UInt16.land _       => return symbolT "bvand"
  | .const ``UInt16.lor _        => return symbolT "bvor"
  | .const ``UInt16.xor _        => return symbolT "bvxor"
  | .const ``UInt16.shiftLeft _  => return symbolT "bvshl"
  | .const ``UInt16.shiftRight _ => return symbolT "bvlshr"
  | .app (.const ``UInt16.toUInt32 _) e =>
    return mkApp2 (symbolT "concat") (BitVec.mkLit 16 0) (← applyTranslators! e)
  | .const ``UInt32 _ =>
    return mkApp2 (symbolT "_") (symbolT "BitVec") (literalT "32")
  | .app (.const ``UInt32.val _) e =>
    applyTranslators! e
  | e@(.app (.const ``UInt32.ofNat _) n) => do
    let n ← reduceLit n e
    return BitVec.mkLit 32 n
  | .const ``UInt32.add _        => return symbolT "bvadd"
  | .const ``UInt32.sub _        => return symbolT "bvsub" -- QF_BV!
  | .const ``UInt32.mul _        => return symbolT "bvmul"
  | .const ``UInt32.div _        => return symbolT "bvudiv"
  | .const ``UInt32.mod _        => return symbolT "bvurem"
  | .const ``UInt32.modn _       => throwError "unknown"
  | .const ``UInt32.land _       => return symbolT "bvand"
  | .const ``UInt32.lor _        => return symbolT "bvor"
  | .const ``UInt32.xor _        => return symbolT "bvxor"
  | .const ``UInt32.shiftLeft _  => return symbolT "bvshl"
  | .const ``UInt32.shiftRight _ => return symbolT "bvlshr"
  | .app (.const ``UInt32.toUInt16 _) e =>
    return appT
      (mkApp3 (symbolT "_") (symbolT "extract") (literalT "15") (literalT "0"))
      (← applyTranslators! e)
  | _ => return none
where
  reduceLit (n : Expr) (e : Expr) : TranslationM Nat := do
    let some n ← Meta.evalNat (← Meta.whnf n) |>.run
      | throwError "literal{indentD n}\nis not constant in{indentD e}"
    return n

open GF2BVPoly

set_option maxHeartbeats 400000 in
example (x y : GF) : GF4096.ofGF (x * y) = (GF4096.ofGF x) * (GF4096.ofGF y) := by
  show (GF4096.ofGF (GF.mul x y)) = GaloisField2k.mul (GF4096.ofGF x) (GF4096.ofGF y)

  extract_def GF4096.ofGF
    specialize_def GF4096.ofGF [] blocking [@Subtype.val, UInt16.val]
    rw [GF4096.ofGF.specialization]
    rw [GF4096.ofGF.specialization]
    rw [GF4096.ofGF.specialization]
    save

  extract_def GF.mul
    specialize_def Mceliece348864Ref.GF.mul [] blocking [
      @Subtype.val,
      UInt16.toUInt32,
      GF.red
    ]
    save

  extract_def GaloisField2k.mul
    specialize_def GaloisField2k.mul [GF4096] blocking [@polyMod, @polyMul]
      rw [GaloisField2k.mul.GF4096.specialization]
      save

  smt_show [
    GF4096.ofGF,
    GF,
    GF.mul,
    GF.red,
    gfMask
  ]

  sorry

#exit -- times out below

  extract_def polyMod
  specialize_def GF2BVPoly.polyMod [24, 12]
  save

  extract_def polyMul
  specialize_def GF2BVPoly.polyMul [12, 12]
  save
#exit
  conv at GaloisField2k.mul.GF4096.def =>
    intro a b
    rw [ GF2BVPoly.polyMul.«12».«12».specialization,
      GF2BVPoly.polyMod.«24».«12».specialization ]
  save

  smt_show [
    GF4096.ofGF,
    GF,
    GF.mul,
    GF.red,
    gfMask,

    GaloisField2k.mul.GF4096,
    GF2BVPoly.polyMul.«12».«12»,
    GF2BVPoly.polyMod.«24».«12»
  ]

  sorry
