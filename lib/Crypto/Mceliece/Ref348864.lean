import Crypto.Bool
import Crypto.BitVec
import Crypto.GF2BV
import Crypto.GF2Poly
import Crypto.ByteVec
import Crypto.Exp
import Crypto.Matrix
import Crypto.Nat
import Crypto.Prim.Shake
import Crypto.Random.PRNG
import Crypto.Range
import Crypto.UInt8
import Crypto.Vector

def select (c:BitVec n) (t f : Vector n α) : Vector n α :=
  Vector.generate n (λi => if c.msb_get! i then t.get i else f.get i)

def tryN {α:Type _ } (f:DRBG → Option α × DRBG) : DRBG → Nat → Option α × DRBG
  | drbg, 0 =>
    (none, drbg)
  | drbg, Nat.succ attempts =>
    match f drbg with
    | (some ind, drbg) => (some ind, drbg)
    | (none, drbg) => tryN f drbg attempts

-- `iterN f n a` return `f^n a`.
def iterN (f : α → α) : Nat → α → α
| 0, a => a
| i+1, a => iterN f i (f a)

def concatVec (v : Vector m (Vector n α)) : Vector (m*n) α :=
  let q {i} (p : i < m*n) : i / n < m := sorry
  let r {i} (p : i < m*n) : 0 < n := sorry
  Vector.generate (m*n) (λi => (v.get ⟨i.val / n, q i.isLt⟩).get (Fin.ofNat' i.val (r i.isLt)))

def bitvecToByteVec_msb {r : Nat} (w : Nat) (v : BitVec r) : ByteVec w :=
  ByteVec.generate w λi => Id.run do
    let mut z : UInt8 := 0
    for j in range 0 8 do
      z := z ||| (if v.msb_get! (8*i+j) then (1:UInt8) <<< OfNat.ofNat j else 0)
    pure z

namespace UInt16

theorem and_right_lt {x y n : UInt16} : y < n →  (x &&& y) < n := by admit

def xor_lt_both {x y n: UInt16} : x < (1 <<< n) → y < (1 <<< n) →  (x ^^^ y) < (1 <<< n) := by
  admit

end UInt16

namespace Mceliece
namespace Ref348864

def name : String := "mceliece348864"

def N := 3488

@[reducible]
def gfbits : Nat := 12

@[reducible]
def sys_t : Nat := 64

@[reducible]
def cond_bytes : Nat := (1 <<< (gfbits-4))*(2*gfbits - 1)

@[reducible]
def pk_nrows : Nat := sys_t * gfbits

@[reducible]
def pk_ncols : Nat := N - pk_nrows

def publicKeyBytes : Nat := pk_nrows * (pk_ncols / 8)

def PublicKey := Vector pk_nrows (BitVec pk_ncols)

namespace PublicKey

-- Create public key from row matrix
def init (m : Vector pk_nrows (BitVec N)) : PublicKey :=
  Vector.generate pk_nrows λr =>
    (m.get! r).take_lsb pk_ncols

def pk_row_bytes : Nat := pk_ncols / 8

protected
def toBytes (pk:PublicKey) : ByteVec publicKeyBytes :=
  let v := bitvecToByteVec_msb (pk_ncols / 8) <$> pk
  ByteVec.generate publicKeyBytes λi =>
    let r := i.val / pk_row_bytes
    let c := i.val % pk_row_bytes
    (v.get! r).get! c

protected def toString (pk:PublicKey) : String := pk.toBytes.toString

instance : ToString PublicKey := ⟨PublicKey.toString⟩

end PublicKey

@[reducible]
def GF := { x:UInt16 // x < (1:UInt16) <<< 12 }

def gfMask : UInt16 := OfNat.ofNat ((1 <<< 12) - 1)

namespace GF

instance (n:Nat) : OfNat GF n where
  ofNat := ⟨UInt16.ofNat n &&& gfMask, UInt16.and_right_lt (by decide)⟩

instance : Inhabited GF := ⟨OfNat.ofNat 0⟩

protected def xor (x y:GF) : GF := ⟨x.val ^^^ y.val, UInt16.xor_lt_both x.property y.property⟩

-- This should compute x * y mod x^12 + x^3 + 1
protected def red (tmp : UInt32) : GF :=
  let t := tmp &&& 0x7fc000
  let tmp := tmp ^^^ (t >>> 9) ^^^ (t >>> 12)
  let t := tmp &&& 0x3000
  let tmp := tmp ^^^ (t >>> 9) ^^^ (t >>> 12)
 ⟨tmp.toUInt16 &&& gfMask, sorry⟩

-- This computes (x * y) mod x^12 + x^3 + 1
protected def mul (x y : GF) : GF := Id.run do
  let x : UInt32 := x.val.toUInt32
  let y : UInt32 := y.val.toUInt32
  let mut tmp : UInt32 := 0
  for i in [0:12] do
    let mask : UInt32 := 1 <<< (UInt32.ofNat i)
    opaque tmp := tmp ^^^ (x * (y &&& mask))
  return GF.red tmp

instance : Xor GF := ⟨GF.xor⟩
instance : Add GF := ⟨GF.xor⟩
instance : Sub GF := ⟨GF.xor⟩
instance : Mul GF := ⟨GF.mul⟩

-- This computes (x * x) mod x^12 + x^3 + 1
def sq (x:GF) : GF :=
  let x := x.val.toUInt32
  let x := (x ||| (x <<< 8)) &&& 0x00FF00FF
  let x := (x ||| (x <<< 4)) &&& 0x0F0F0F0F
  let x := (x ||| (x <<< 2)) &&& 0x33333333
  let x := (x ||| (x <<< 1)) &&& 0x55555555
  GF.red x

-- This computes x^-1 (mod x^12 + x^3 + 1)
def inv (i:GF) : GF :=
  let tmp11 := i.sq * i                  -- 11
  let tmp1111 := tmp11.sq.sq * tmp11     -- 1111
  let o := tmp1111.sq.sq.sq.sq * tmp1111 -- 11111111
  let o := o.sq.sq * tmp11               -- 1111111111
  let o := o.sq * i                      -- 11111111111
  o.sq                                   -- 111111111110

protected def div (n d : GF) := n * d.inv

instance : Div GF := ⟨GF.div⟩

instance : CommMulMonoid GF where
  mul_assoc := sorry
  mul_comm  := sorry
  mul_one := sorry

protected def bit (x:GF) (idx:Nat) : Bool :=
  if idx < 12 then
    (x.val >>> UInt16.ofNat idx) &&& 1 = 1
  else
    false

def bitrev (x:GF) : GF :=
  let a : UInt16 := x.val
  let a := ((a &&& 0x00FF) <<< 8) ||| ((a &&& 0xFF00) >>> 8)
  let a := ((a &&& 0x0F0F) <<< 4) ||| ((a &&& 0xF0F0) >>> 4)
  let a := ((a &&& 0x3333) <<< 2) ||| ((a &&& 0xCCCC) >>> 2)
  let a := ((a &&& 0x5555) <<< 1) ||| ((a &&& 0xAAAA) >>> 1)
  ⟨a >>> 4, sorry⟩

end GF

def loadGf {n} (r: ByteVec n) (i:Nat) : GF :=
  let f (x:UInt8) : UInt16 := UInt16.ofNat x.toNat
  let w : UInt16 := f (r.get! (i+1)) <<< 8 ||| f (r.get! i)
  ⟨w &&& gfMask, sorry⟩

def loadGfArray {n:Nat} (r: ByteVec (2*n)) : Vector n GF :=
  Vector.generate n (λi => loadGf r (2*i.val))

def store_gf (irr : Vector sys_t GF) : ByteVec (2*sys_t) :=
  ByteVec.generate (2*sys_t) λi =>
    let idx := i.val >>> 1
    let p : idx < sys_t := by admit
    let gf := irr.get ⟨idx, p⟩
    if i.val &&& 1 = 1 then
      UInt8.ofNat ((gf.val >>> 8).toNat)
    else
      UInt8.ofNat (gf.val.toNat)

def secretKeyBytes : Nat := 40 + 2*sys_t + cond_bytes + N/8

@[reducible]
def row_size := 1 <<< (gfbits - 1)

@[reducible]
def cb_size : Nat := row_size*(2*gfbits - 1)

def cbf_le (w:@&Nat)
      (e : @&Vector (1 <<< (w+1)) GF)
      (e_min : @&Vector (1 <<< (w+1)) GF)
  : Vector (1 <<< w) Bool := Id.run do
  let n := 1 <<< (w+1)

  let mut b00 := e_min.map λv => v.val.toNat
  let mut b10 := Vector.generate n λx => (e.get! (e.get! x).val.toNat).val.toNat
  for _i in range 1 (w-1) do
    b00 := Vector.generate n λx =>
      if b00.get! (b10.get! x) < b00.get! x then
        b00.get! (b10.get! x)
      else
        b00.get! x
    b10 := Vector.generate n λx => b10.get! (b10.get! x)
  pure <| Vector.generate (1 <<< w) λx => decide ((b00.get! (2*x)) &&& 1 = 1)

def cbf_gt (w:@&Nat)
      (e : @&Vector (1 <<< (w+1)) GF)
      (e_min : @&Vector (1 <<< (w+1)) GF)
  : Vector (1 <<< w) Bool := Id.run do
  let n := 1 <<< (w+1)

  let mut b00 := e_min.map λv => v.val.toNat
  let mut b16 := Vector.generate n λx => (e.get! (e.get! x).val.toNat).val.toNat

  for i in range 1 (w-1) do
    let a := Vector.generate n λx => b00.get! (b16.get! x)
    if i < w-1 then
      b16 := Vector.generate n λx => b16.get! (b16.get! x)
    b00 := Vector.generate n λx => min (b00.get! x) (a.get! x)

  pure <| Vector.generate (1 <<< w) λx => decide ((b00.get! (2*x)) &&& 1 = 1)

def controlBitsFromPermutation4 (a : Vector cb_size Bool) (off:Nat) : ∀(w:Nat) (_pi : Vector (1 <<< (w+1)) GF), Vector cb_size Bool
| 0, pi =>
  a.set! (row_size * (gfbits-1) + off) (decide ((pi.get! 0).val &&& 1 = 1))
| Nat.succ w, pi => Id.run do
  let n := 1 <<< (w+2)

  let mut pi_inv : Vector n GF := Vector.replicate n ⟨0, sorry⟩
  for i in range 0 n do
    pi_inv := pi_inv.set! (pi.get! i).val.toNat ⟨UInt16.ofNat i, sorry⟩

  let e                   := Vector.generate n λx => pi.get! ((pi_inv.get! (x ^^^ 1)).val.toNat ^^^ 1)
  let e_min : Vector n GF := Vector.generate n λx => ⟨min (UInt16.ofNat x) (e.get! x).val, sorry⟩

  let bits :=
    if w+2 ≤ 10 then
      cbf_le (w+1) e e_min
    else
      cbf_gt (w+1) e e_min

  let c : Vector _ GF := Vector.generate n (λk =>
    let idx := pi.get! k
    if bits.get! (idx.val.toNat / 2) then ⟨idx.val ^^^ 1, sorry⟩  else idx)
  let wk := gfbits - (w+2)
  let step := 1 <<< wk

  let mut a := a
  let m := 1 <<< (w+1)

  for j in range 0 m do
    let idx := step * j + off
    let p := bits.get! j
    a := a.set! (row_size * (gfbits - (w+2)) + idx) p

  for j in range 0 m do
    let idx := step * j + off
    let p :=  decide ((c.get! (2*j)).val &&& 1 = 1)
    a := a.set! (row_size * (gfbits + w) + idx) p

  let q0 : Vector m GF := Vector.generate m λj =>
    let idx : Nat := 2*j.val+ ((c.get! (2*j.val)).val &&& 1).toNat
    ⟨(c.get! idx).val >>> 1, sorry⟩
  let q1 : Vector m GF := Vector.generate m λj =>
    let idx : Nat := 2*j.val+ (1-((c.get! (2*j.val)).val &&& 1).toNat)
    ⟨(c.get! idx).val >>> 1, sorry⟩

  a := controlBitsFromPermutation4 a off w q0
  let step := 1 <<< (gfbits - (w+2))
  controlBitsFromPermutation4 a (off+step) w q1

theorem shl_plus_shl (n : Nat) : (1 <<< n + 1 <<< n) = 1 <<< (n+1) := sorry

theorem shl_times_shl (m n : Nat) : (1 <<< m * 1 <<< n) = 1 <<< (m+n) := sorry

def layer (pi : Vector (1 <<< gfbits) GF) (cb : BitVec (1 <<< gfbits)) (s : Fin gfbits) : Vector (1 <<< gfbits) GF :=
  let si := s.val
  let stride := 1 <<< si
  let h : Vector (1 <<< (gfbits - (si+1)) * (1 <<< si + 1 <<< si)) GF = Vector (1 <<< gfbits) GF := by
        apply congrFun
        apply congrArg
        simp only [shl_plus_shl, shl_times_shl, Nat.sub_add_cancel s.isLt]
  cast h $
    concatVec $ Vector.generate (1 <<< (gfbits - (s+1))) λk =>
      let i := stride*k.val
      let c  : BitVec (1 <<< si)    := cb.extractN! i stride
      let p1 : Vector (1 <<< si) GF := pi.extractN! (2*i) stride
      let p2 : Vector (1 <<< si) GF := pi.extractN! (2*i+stride) stride
      select c p2 p1 ++ select c p1 p2

def testPerm (out : ByteVec cond_bytes) :  Vector (1 <<< gfbits) GF := Id.run do
  let w  := gfbits
  let n  := 1 <<< gfbits
  let n4 := n >>> 4
  let out : Vector (2*gfbits-1) (BitVec (1 <<< gfbits))  :=
        Vector.generate (2*w-1) λi =>
          let cb := out.extractN (n4 * i) n4
          BitVec.generate_msb (1 <<< gfbits) λi => (cb.get! (i.val/8)).testBit (i.val%8)
  let mut pi := Vector.generate n (λi => (OfNat.ofNat i.val : GF))
  for i in range 0 w do
    have p : i < 2*w-1 := by admit
    have q : i < gfbits := by admit
    let cb := out.get ⟨i, p⟩
    pi := layer pi cb ⟨i, q⟩
  for j in range 0 (w-1) do
    have p : gfbits+j < 2*gfbits-1 := by admit
    let cb := out.get ⟨gfbits+j, p⟩
    let i := (w - 2) - j
    have q : i < gfbits := by admit
    pi := layer pi cb ⟨i, q⟩
  pure pi

def controlBitsFromPermutation (pi : Vector (1 <<< gfbits) GF) : Option (ByteVec cond_bytes) :=
  let out := controlBitsFromPermutation4 (Vector.replicate cb_size false) 0 (gfbits-1) pi
  let out :=
        ByteVec.generate cond_bytes λi =>
          let v := BitVec.generate_lsb 8 (λj => out.get! (8*i + j))
          v.toUInt8
  if pi ≠ testPerm out then
    none
  else
    some out

structure SecretKey where
  seed : ByteVec 32
  goppa : Vector sys_t GF
  permutation : Vector (1 <<< gfbits) GF
  controlbits : ByteVec cond_bytes
  rest : ByteVec (N/8)

namespace SecretKey

def byteVec (sk:SecretKey) : ByteVec secretKeyBytes :=
  sk.seed
    ++ ByteVec.ofUInt64lsb 0xffffffff
    ++ store_gf sk.goppa
    ++ sk.controlbits
    ++ sk.rest

protected def toString (sk:SecretKey) : String := sk.byteVec.toString

instance : ToString SecretKey := ⟨SecretKey.toString⟩

end SecretKey

structure KeyPair where
  pk : PublicKey
  sk : SecretKey

@[reducible]
def rw : Nat :=  N/8 + 4*(1 <<< gfbits) + sys_t * 2 + 32

def byteToUInt32 (v:UInt8) : UInt32 := UInt32.ofNat (v.toNat)

def load4 {n} (r: ByteVec n) (i:Nat) : UInt32 :=
  let b (j:Nat) (s:UInt32) : UInt32 := byteToUInt32 (r.get! (i+j)) <<< s
  b 0 0 ||| b 1 8 ||| b 2 16 ||| b 3 24

def load4Array {n:Nat} (r: ByteVec (4*n)) : Vector n UInt32 :=
  Vector.generate n (λi => load4 r (4*i.val))

def poly_full_mul {m n:Nat} {α:Type _} [Add α] [Mul α] [OfNat α 0] (x : Vector m α) (y : Vector n α) : Vector (m+n-1) α := Id.run do
  let mut prod : Vector (m+n-1) α := Vector.replicate (m+n-1) 0
  let _h : Inhabited α := ⟨0⟩
  for i in range 0 m do
    for j in range 0 n do
      prod := prod.add! (i+j) (x.get! i * y.get! j)
  pure prod

def GF_red (z : Vector (2*sys_t-1) GF) : Vector sys_t GF := Id.run do
  let mut z := z
  for j in range 0 (sys_t-1) do
    let i := sys_t-2 - j
    let p := z.get! (sys_t+i)
    z := z.sub! (i+3) p
    z := z.sub! (i+1) p
    z := z.sub! (i+0) (2*p)
  pure (Vector.generate sys_t λi => z.get! i)

def GF_mul (x y : Vector sys_t GF) : Vector sys_t GF :=
  GF_red (@poly_full_mul sys_t sys_t GF _ _ _ x y)

def genPolyGen_mask (mat : Matrix (sys_t+1) sys_t GF) (j:Nat) : GF := Id.run do
  let mut r := mat.get! j j
  for i in rangeH j (sys_t+1) do
    for k in rangeH (j+1) sys_t do
      r := r ^^^ mat.get! i k
  pure r

def genPolyGenUpdate (mat : Matrix (sys_t+1) sys_t GF) (j : Nat) (inv : GF)
    : Matrix (sys_t+1) sys_t GF :=
  Matrix.generate _ _ λr c =>
    if r ≤ j then
      0
    else
      if c = j then
        inv * mat.get! r j
      else
        mat.get! r c ^^^ (inv * mat.get! r j * mat.get! j c)

def genPolyGen (f : Vector sys_t GF) : Option (Vector sys_t GF) := Id.run do
  let v0 : Vector sys_t GF := Vector.generate sys_t λi => if i = 0 then 1 else 0
  let mut mat := Matrix.unfoldBy (GF_mul f) v0
  for j in range 0 sys_t do
    let mut r := mat.get! j j
    if r = 0 then
      r := genPolyGen_mask mat j
    if r = 0 then
      return none
    else
      mat := genPolyGenUpdate mat j r.inv
  some (mat.row! sys_t)

-- Map used by init_pi
structure Perm where
  value : UInt32
  idx : GF

namespace Perm

instance : Inhabited Perm := ⟨{ value := 0, idx := 0}⟩

end Perm

-- Generate random permutation from random uint32 array
def randomPermutation (perm : Vector (1 <<< gfbits) UInt32)
  : Option (Vector (1 <<< gfbits) GF) := Id.run do
  -- Build vector associated input number to index
  let v : Vector (1 <<< gfbits) Perm :=
        Vector.generate _
          (λi => { value := perm.get i, idx := OfNat.ofNat i.val })

  -- Sort vector based on value to get random permutation
  let lt (x y : Perm) : Bool := x.value < y.value
  let v : Vector (1 <<< gfbits) Perm := Vector.qsort v lt

  -- Check to see if we have duplicated values in sorted array
  -- Failing to check can bias result
  for i in range 0 (1 <<< gfbits - 1) do
    if (v.get! i).value = (v.get! (i+1)).value then
      return none

  pure (some (Perm.idx <$> v))

def eval (f : Vector (sys_t+1) GF) (a : GF) : GF := Id.run do
  let mut r := f.get! sys_t
  for j in range 0 sys_t do
    r := r * a
    r := r + f.get! (sys_t - 1 - j)
  pure r

def init_mat_row (inv : Vector N GF) (k : Nat) : BitVec N :=
  BitVec.generate_msb N λi => (inv.get i).bit k

def init_mat (g : Vector sys_t GF) (L : Vector N GF) : Vector pk_nrows (BitVec N) := Id.run do
  let g' := g.push 1
  let inv0 := (λx => (eval g' x).inv) <$> L
  Vector.flatten $
    Vector.generate sys_t λi =>
      let inv := Vector.generate N λj =>
            inv0.get! j * exp (L.get! j) i
      Vector.generate gfbits λk => init_mat_row inv k

def gaussian_elim_row (m : Vector pk_nrows (BitVec N)) (row: Nat)
  : Option (Vector pk_nrows (BitVec N)) := Id.run do
  let mut mat_row : BitVec N := m.get! row
  for k in rangeH (row+1) pk_nrows do
    let mat_k := m.get! k
    let mask1 := mat_row.msb_get! row
    let mask2 := mat_k.msb_get! row
    if mask1 ≠ mask2 then
      mat_row := mat_row ^^^ mat_k
  if not (mat_row.msb_get! row) then
    return none
  let mut m := m
  for k in range 0 pk_nrows do
    if k = row then
      m := m.set! k mat_row
    else
      let mat_k := m.get! k
      if mat_k.msb_get! row then
        m := m.set! k (mat_k ^^^ mat_row)
  pure (some m)

def gaussian_elim (m : Vector pk_nrows (BitVec N))
  : Option (Vector pk_nrows (BitVec N)) := Id.run do
  let mut m := m
  for i in range 0 pk_nrows do
    match gaussian_elim_row m i with
    | some m1 =>
      m := m1
    | none => return none
  pure (some m)

def mkPublicKey (g : Vector sys_t GF) (pi: Vector (1 <<< gfbits) GF) : Option PublicKey := do
  let L   := Vector.generate N λi => (pi.get! i).bitrev
  PublicKey.init <$> gaussian_elim (init_mat g L)

def tryCryptoKemKeypair (seed: ByteVec 32) (r: ByteVec rw) : Option KeyPair := do
  let g ← genPolyGen $ loadGfArray $        r.extractN (N/8 + 4*(1 <<< gfbits)) (2*sys_t)
  let pi ← randomPermutation $ load4Array $ r.extractN (N/8) (4*(1 <<< gfbits))
  let cb ← controlBitsFromPermutation pi
  let pk ← mkPublicKey g pi
  let sk := { seed := seed,
              goppa := g,
              permutation := pi,
              controlbits := cb,
              rest := r.extractN 0 (N/8)
            }
  some { pk := pk, sk := sk }

def mkCryptoKemKeypair [PRNG α] (prng:α) (attempts: optParam Nat 10) : Option (KeyPair × α) := do
  let rec loop : ByteVec 32 → Nat → Option KeyPair
      | _, 0 => none
      | seed, Nat.succ n => do
        let r := shake rw (#v[64] ++ seed).data
        match tryCryptoKemKeypair seed r with
        | some kp => some kp
        | none =>
          loop (r.takeFromEnd 32) n
  let (bytes, prng) := PRNG.randombytes prng 32
  match loop bytes attempts with
  | none => none
  | some p => some (p, prng)

def tryGenerateRandomErrors (v : Vector (2*sys_t) GF) (n:Nat) : Option (Vector n (Fin N)) := Id.run do
  let mut ind : Array (Fin N) := Array.mkEmpty sys_t
  for num in v.data do
    let num := num.val.toNat
    if lt : num < N then
      ind := ind.push ⟨num, lt⟩
      if eq:ind.size = n then
        return (some ⟨ind, eq⟩)
  pure none

def has_duplicate {n:Nat} {α:Type} [DecidableEq α] (v: Vector n α) : Bool := Id.run do
  for i in rangeH 1 n do
    for j in range 0 i do
      if lt_i : i < n then
        if lt_j : j < n then
          if v.get ⟨i, lt_i⟩ = v.get ⟨j, lt_j⟩ then
            return true
  pure false

def generateErrorBitmask (a: Vector sys_t (Fin N)) : BitVec N := Id.run do
  let mut e : BitVec N := BitVec.zero N
  for v in a.data do
    e := e.msb_set! v.val true
  pure e

def tryGenerateErrors [PRNG α] (prng:α) : Option (BitVec N) × α := Id.run do
  let (bytes, prng) := PRNG.randombytes prng (4*sys_t)
  let input : Vector (2*sys_t) GF := loadGfArray bytes

  let mut a : Array (Fin N) := Array.mkEmpty sys_t
  for (num : GF) in input.data do
    let num : Nat := num.val.toNat
    if lt : num < N then
      a := a.push ⟨num, lt⟩
      -- Check to see if done
      if eq:a.size = sys_t then
        let v : Vector sys_t (Fin N) := ⟨a, eq⟩
        if has_duplicate v then
          return (none, prng)
        return (some (generateErrorBitmask v), prng)
  pure ⟨none, prng⟩

def cSyndrome (pk : PublicKey) (e: BitVec N) : BitVec pk_nrows := Id.run do
  BitVec.generate_msb pk_nrows λi =>
    let off := (BitVec.zero pk_nrows).msb_set! i True
    let row : BitVec N := off ++ pk.get! i
    (row &&& e).fold_lsb (· ^^^ ·) false

@[reducible]
structure Ciphertext where
  syndrome : BitVec pk_nrows
  hash : ByteVec 32

namespace Ciphertext

protected def bytes (c:Ciphertext) : ByteVec 128 :=
  bitvecToByteVec_msb (pk_nrows/8) c.syndrome ++ c.hash

protected def toString (c:Ciphertext) : String := c.bytes.toString

instance : ToString Ciphertext := ⟨Ciphertext.toString⟩

def mkHash (e:BitVec N) : ByteVec 32 :=
  shake 32 (ByteArray.fromList [2] ++ (bitvecToByteVec_msb (N/8) e).data)

end Ciphertext

structure Plaintext where
  e : BitVec N
  c : Ciphertext

namespace Plaintext

protected def bytes (p:Plaintext) :  ByteVec 32 :=
  shake 32 (ByteArray.fromList [1] ++ (bitvecToByteVec_msb (N/8) p.e).data ++ p.c.bytes.data)

protected def toString (p:Plaintext) : String := p.bytes.toString

instance : ToString Plaintext := ⟨Plaintext.toString⟩

end Plaintext

structure EncryptionResult where
  e : BitVec N
  ct : Ciphertext

def EncryptionResult.ss (r:EncryptionResult) : Plaintext := { e := r.e, c := r.ct }

def mkCryptoKemEnc [PRNG α] (drbg:α) (attempts:Nat) (pk:PublicKey) : Option (EncryptionResult × α) := do
  match tryN tryGenerateErrors drbg attempts with
  | (some e, drbg) =>
    let c   := { syndrome := cSyndrome pk e,
                 hash := Ciphertext.mkHash e
                }
    some ({ e := e, ct := c }, drbg)
  | (none, _) => panic! "mkCryptoKemEnc def failure"

def concatBitvec (v: Vector m (BitVec n)) : BitVec (m*n) := Id.run do
  let mut r : Nat := 0
  for i in range 0 m do
    r := r <<< n + (v.get! i).val
  ⟨r, sorry⟩


def unconcatBitvec! (m n : Nat) (v: BitVec r) : Vector m (BitVec n) :=
  Vector.generate m (λi => v.extractN! (i.val*n) n)

def transpose64 (a : BitVec (64*64)) : BitVec (64*64) :=
  BitVec.generate_msb (64*64) (λi =>
    let j := i.val / 64
    let k := i.val % 64
    a.msb_get! (64 * (63-k) + (63-j)))

def benes_layer
  (data : BitVec (64*64))
  (bits : BitVec (32*64))
  (lgs : Nat)
    : BitVec (64*64) :=
  let s : Nat := 1 <<< lgs

  let data_l : Vector (32 >>> lgs) (BitVec (s*64)) :=
        Vector.generate (32 >>> lgs) (λh2 => data.extractN! ((s*64)*2*h2.val)     (s*64))
  let data_h : Vector (32 >>> lgs) (BitVec (s*64)) :=
        Vector.generate (32 >>> lgs) (λh2 => data.extractN! ((s*64)*(2*h2.val+1)) (s*64))

  let b3 : Vector (32 >>> lgs) (BitVec (s*64)) :=
        Vector.generate (32 >>> lgs) (λh2 => bits.extractN! ((s*64)*h2.val) (s*64))

  let res_v : Vector (32 >>> lgs) (BitVec (s*64+s*64)) :=
        Vector.generate (32 >>> lgs) (λh2 =>
          let d3 := data_l.get h2
          let d4 := data_h.get h2
          let p2 : BitVec (s*64) := (d3 ^^^ d4) &&& (b3.get h2)
          let d1 : BitVec (s*64) := d3 ^^^ p2
          let d2 : BitVec (s*64) := d4 ^^^ p2
          BitVec.append d1 d2)
  let r := concatBitvec res_v
  ⟨r.val, sorry⟩

def load4_64
  (c : ByteVec 256)
  : BitVec 2048 :=
  let b := transpose64 (concatBitvec (Vector.generate 64 $ λi => Id.run do
    let mut r := 0
    for j in range 0 4 do
      r := (r <<< 8) ||| (c.get! (4*i+3-j)).toNat
    pure $ (UInt64.ofNat r).toBitVec))
  b.extractN! 0 2048

def load8_32 (c: ByteVec 256) : BitVec 2048 :=
  @concatBitvec 32 64 (Vector.generate 32 $ λi => Id.run do
    let mut r := 0
    for j in range 0 8 do
      r := (r <<< 8) ||| (c.get! (8*i+(7-j))).toNat
    pure $ (UInt64.ofNat r).toBitVec)

def apply_benes0 (a0 : BitVec (64*64))
                 (d : Vector 23 (ByteVec 256))
    : BitVec (64*64) := Id.run do
  let mut a := a0
  a := transpose64 a
  for l in range 0 6 do
    a := benes_layer a (load4_64 (d.get! l)) l
  a := transpose64 a
  for l in range 0 6 do
    let c := d.get! (6+l)
    a := benes_layer a (load8_32 c) l
  for l in range 0 5 do
    let l := 4 - l
    let c := d.get! (16-l)
    a := benes_layer a (load8_32 c) l
  a := transpose64 a
  for l in range 0 6 do
    let l := 5 - l
    a := benes_layer a (load4_64 (d.get! (22-l))) l
  pure <| transpose64 a

def support_gen (d : Vector 23 (ByteVec 256)) : Vector N GF := Id.run do
  let L : Vector gfbits (Vector 64 (BitVec 64)) :=
        Vector.generate gfbits λj =>
          let r :=
            BitVec.generate_lsb (1 <<< gfbits) λ(i : Fin (1 <<< gfbits)) =>
              let i : GF := OfNat.ofNat i.val
              i.bit (11-j)
          let a0 :=
            concatBitvec (Vector.generate 64 (λ(i : Fin 64) =>
              (UInt64.ofNat ((r.val >>> (64*i.val)) &&& (2^64 - 1))).toBitVec))
          unconcatBitvec! 64 64 (apply_benes0 a0 d)
  Vector.generate N λi0 => Id.run do
    let i  := i0.val / 64
    let m2 := i0.val % 64
    let mut si : Nat := 0
    for k in range 0 gfbits do
      let r := L.get! (gfbits-1-k)
      let e := ((r.get! i).toUInt64.toNat >>> m2) &&& 1
      si := si <<< 1 ||| e
    pure (OfNat.ofNat si)

def synd
    (g: Vector sys_t GF)
    (l : Vector N GF)
    (error_bitmask : BitVec N)
   : Vector (2*sys_t) GF := Id.run do
  let mut out := Vector.replicate (2*sys_t) 0
  let f := g.push 1
  for i in range 0 N do
    if error_bitmask.msb_get! i then
      let e := eval f (l.get! i)
      let mut e_inv := (e * e).inv
      for j in range 0 (2*sys_t) do
        out := out.set! j (out.get! j + e_inv)
        e_inv := e_inv * l.get! i
  pure out

-- the Berlekamp-Massey algorithm
-- input: s, sequence of field elements
-- output: out, minimal polynomial of s
def bm
    (s: Vector (2*sys_t) GF)
   : Vector (sys_t+1) GF := Id.run do
  let mut B := Vector.generate (sys_t+1) λi => if i = 1 then 1 else 0
  let mut C := Vector.generate (sys_t+1) λi => if i = 0 then 1 else 0
  let mut L : Nat := 0
  let mut b : GF := 1
  for N in range 0 (2*sys_t) do
    let mut d : GF := 0
    for i in range 0 (min N sys_t + 1) do
      d := d + (C.get! i * s.get! (N-i))

    if d ≠ 0 then
      let T := C
      C := C + (d/b) * B
      if N ≥ 2*L then
        L := N+1-L
        B := T
        b := d
    B := Vector.generate (sys_t+1) λi =>
           if i = 0 then 0 else B.get! (i-1)
  pure $ Vector.generate (sys_t+1) λi => C.get ⟨sys_t-i, sorry⟩

-- Decrypt the N-bit vector created by mkCryptoKemEnc
def cryptoKemDec1 (c : Ciphertext) (sk : SecretKey) : Option (BitVec N) := do
  let g := sk.goppa
  let d : Vector 23 (ByteVec 256) := Vector.generate _ λ(i: Fin 23) =>
        sk.controlbits.extractN! (256*i.val) 256
  let l : Vector N GF := support_gen d
  let r : BitVec N := c.syndrome ++ BitVec.zero (N-pk_nrows)
  let s := synd g l r
  let locator := bm s
  let images := (λi => (eval locator i).inv) <$> l

  let mut w : Nat := 0
  for i in range 0 N do
    if images.get! i = 0 then
      w := w + 1
  let e : BitVec N := BitVec.generate_msb N λi => images.get i = 0
  -- Generate preimage
  if w = sys_t ∧ Ciphertext.mkHash e = c.hash ∧ s = synd g l e then
    some e
  else
    none

-- This is the basic correctness theorem that if we
-- make a public key from Goppa polynomial and permutation
-- and use that to generate an encryption key result, then
-- we can decrypt it.
theorem decryptEncrypt [PRNG α] (drbg drbg' : α)
               (attempts : Nat)
               (sk: SecretKey)
               (pk : PublicKey)
               (r:EncryptionResult) :
    controlBitsFromPermutation sk.permutation = some sk.controlbits
    → mkPublicKey sk.goppa sk.permutation = some pk
    → mkCryptoKemEnc drbg attempts pk = some (r, drbg')
    → cryptoKemDec1 r.ct sk = some r.e := by
  admit

def cryptoKemDec (c : Ciphertext) (sk : SecretKey) : Option Plaintext := do
  let e ← cryptoKemDec1 c sk
  some $ { e := e, c := c }

end Ref348864
end Mceliece
