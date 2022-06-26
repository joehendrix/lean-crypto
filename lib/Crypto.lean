import Crypto.Bool
import Crypto.BitVec2
import Crypto.ByteBuffer
import Crypto.ByteVec2
import Crypto.Exp
import Crypto.Matrix
import Crypto.Nat
import Crypto.Range
import Crypto.UInt8
import Crypto.Vector

namespace BitVec

protected def generate (n : Nat) (f : Fin n → Bool) : BitVec n := Id.run do
  let mut r : Nat := 0

  for i in range 0 n do
    let b := f ⟨i, sorry⟩
    r := r <<< 1 ||| (if b then 1 else 0)
  ⟨r, sorry⟩

def extractN! (a:BitVec n) (s m:Nat) : BitVec m :=
  let e := s + m
  let b := (a.val >>> (n - e)) &&& (1 <<< (min m (n - s)) - 1)
  ⟨b, sorry⟩

def get (a: BitVec n) (i:Nat) : Bool :=
  if i < n then
    (a.val >>> (n-1-i)) &&& 1 = 1
  else
    false

end BitVec

def select (c:BitVec n) (t f :Vector n α) : Vector n α :=
  Vector.generate n (λi => if c.get i then t.get i else f.get i)

def iterN (f : α → α) : Nat → α → α
| 0, a => a
| i+1, a => iterN f i (f a)

def iterV (n:Nat) (f : β → α × β) (b:β) : Vector n α × β :=
  let g := λ((a, b) : Array α × β) =>
        let (v, b) := f b
        (a.push v, b)
  let (a, b) := iterN g n (Array.mkEmpty n, b)
  let p : a.size = n := by admit
  (⟨a, p⟩, b)

def concatByteVec (v : Vector m (ByteVec n)) : ByteVec (m*n) :=
  let q {i} (p : i < m*n) : i / n < m := sorry
  let r {i} (p : i < m*n) : 0 < n := sorry
  ByteVec.generate (m*n) (λi => (v.get ⟨i.val / n, q i.isLt⟩).get (Fin.ofNat' i.val (r i.isLt)))

def concatVec (v : Vector m (Vector n α)) : Vector (m*n) α :=
  let q {i} (p : i < m*n) : i / n < m := sorry
  let r {i} (p : i < m*n) : 0 < n := sorry
  Vector.generate (m*n) (λi => (v.get ⟨i.val / n, q i.isLt⟩).get (Fin.ofNat' i.val (r i.isLt)))

def concatIterV (m:Nat) (f : β → ByteVec n × β) (b:β) : ByteVec (m*n) × β :=
  (λ(v,b) => (concatByteVec v, b)) (iterV m f b)

/-
def concatIterV (m:Nat) (f : β → ByteVec n × β) (b:β) : ByteVec (m*n) × β :=
  let g := λ((a, b) : ByteArray × β) =>
        let (v, b) := f b
        (a ++ v.data, b)
  let (a, b) := iterN g m (ByteArray.mkEmpty (m*n), b)
  let p : a.size = m*n := by admit
  (⟨a, p⟩, b)
-/

@[extern "lean_elt_from_bytevec"]
opaque eltFromByteVec {w : @&Nat} (r : @&Nat) (v : @&(ByteVec w)) : BitVec r

@[extern "lean_elt_to_bytevec"]
opaque bitvecToByteVec_msbb { r : @&Nat} (w : @&Nat) (v : @&(BitVec r)) : ByteVec w

@[extern "lean_nat_to_bytevec_lsb"]
opaque bitvecToByteVec_lsb {r : @&Nat} (w : @&Nat) (v : @&(BitVec r)) : ByteVec w


def lsbToMsbb {r:Nat} (v:BitVec r) : BitVec r :=
  BitVec.generate_msbb r (λi => v.lsb_get! i.val)

def ByteVec.toBuffer {n:Nat} : ByteVec n → ByteBuffer
| ⟨a,_⟩ => ⟨a⟩

instance : Coe (ByteVec n) ByteBuffer where
  coe := ByteVec.toBuffer

structure DRBG where
  key : ByteVec (256 / 8)
  v : ByteVec (128 / 8)

instance : Inhabited DRBG := ⟨Inhabited.default, Inhabited.default⟩

def tryN {α:Type _ } (f:DRBG → Option α × DRBG) : DRBG → Nat → Option α × DRBG
  | drbg, 0 =>
    (none, drbg)
  | drbg, Nat.succ attempts =>
    match f drbg with
    | (some ind, drbg) => (some ind, drbg)
    | (none, drbg) => tryN f drbg attempts

@[reducible]
def Seed := ByteVec 48

opaque incrementV (v : ByteVec 16) : ByteVec 16 := Id.run do
  let mut v := v
  for i in range 0 15 do
    let j := 15 - i
    let vj := v.get! j
    if vj = 0xff then
      v := v.set! j 0x00
    else
      v := v.add! j 1
      break
  pure v

@[extern "lean_AES256_ECB"]
opaque aes256Ecb (key: @&ByteVec 32) (v: @&ByteVec 16) : ByteVec 16

opaque aes256CtrDrbgUpdate (key : ByteVec 32) (v0 : ByteVec 16) : ByteVec 48 × ByteVec 16 :=
  let f := λv => let v := incrementV v; (aes256Ecb key v, v)
  concatIterV 3 f v0

opaque randombytesInit (s : Seed) : DRBG :=
  let key := ByteVec.generate 32 (λ_ => 0)
  let v   := ByteVec.generate 16 (λ_ => 0)
  let (b, _) := aes256CtrDrbgUpdate key v
  let b := ByteVec.generate _ (λi => b.get i ^^^ s.get i)
  { key := b.extractN 0 32, v := b.extractN 32 16 }

private theorem randomBytesTerminates : ∀n, n ≥ 16 → n - 16 < n := sorry

def randombytes3 (key : ByteVec 32) (v : ByteVec 16) (a : ByteArray) (n : Nat)
   : ByteArray × ByteVec 16 :=
  if n == 0 then
    (a, v)
  else
    let v := incrementV v
    let b := aes256Ecb key v
    if n ≥ 16 then
      randombytes3 key v (a ++ b.data) (n - 16)
    else
      (a ++ b.data.extractN 0 n, v)
  decreasing_by exact randomBytesTerminates _ ‹_›

theorem randomBytes3_size (key) (v) (a) (n:Nat)
    : (randombytes3 key v a n).1.size = n := by
  admit

opaque randombytes (rbg : DRBG) (n : Nat) : ByteVec n × DRBG :=
  let key := rbg.key
  let v := rbg.v
  let p := randombytes3 key v (ByteArray.mkEmpty n) n
  let pr : p.1.size = n := randomBytes3_size key v (ByteArray.mkEmpty n) n
  let (b, _) := aes256CtrDrbgUpdate key p.2
  let rbg := { key := b.extractN 0 32, v := b.extractN 32 16 }
  (⟨p.1, pr⟩, rbg)

def initKeypairSeedPrefix : ByteVec 1 := #v[64]

def initKeypairSeed (v:ByteVec 32) : ByteVec 33 := initKeypairSeedPrefix ++ v

@[extern "lean_shake256"]
opaque shake (w:Nat) (input: ByteArray) : ByteVec w

def cryptoHash32b (b:ByteArray) : ByteVec 32 := shake 32 b

namespace Mceliece348864Ref

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
    (lsbToMsbb (m.get! r)).take_lsb pk_ncols

def pk_row_bytes : Nat := pk_ncols / 8

protected
def toBytes (pk:PublicKey) : ByteVec Mceliece348864Ref.publicKeyBytes :=
  let v := (λbv => bitvecToByteVec_msbb (pk_ncols / 8) bv) <$> pk
  ByteVec.generate publicKeyBytes λi =>
    let r := i.val / pk_row_bytes
    let c := i.val % pk_row_bytes
    (v.get! r).get! c

protected def toString (pk:PublicKey) : String := pk.toBytes.toString

instance : ToString PublicKey := ⟨PublicKey.toString⟩

end PublicKey

@[reducible]
def GF := { x:UInt16 // x < (1<<<12) }

def gfMask : UInt16 := (1 <<< 12) - 1

namespace GF

instance : Inhabited GF := ⟨⟨0, sorry⟩⟩

protected def xor  (x y:GF) : GF := ⟨x.val ^^^ y.val, sorry⟩

@[extern "lean_gf_mul"]
protected opaque mul (x y : GF) : GF

@[extern "lean_gf_frac"]
protected opaque frac (x y : GF) : GF

instance : Xor GF := ⟨GF.xor⟩
instance : Add GF := ⟨GF.xor⟩
instance : Sub GF := ⟨GF.xor⟩
instance : Mul GF := ⟨GF.mul⟩

instance (n:Nat) : OfNat GF n where
  ofNat := ⟨UInt16.ofNat n &&& gfMask, sorry⟩

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

@[extern "lean_gf_inv"]
opaque gf_inv : GF -> GF


def loadGf {n} (r: ByteVec n) (i:Nat) : GF :=
  let f (x:UInt8) : UInt16 := UInt16.ofNat x.toNat
  let w : UInt16 := f (r.get! (i+1)) <<< 8 ||| f (r.get! i)
  ⟨w &&& gfMask, sorry⟩

def loadGfArray {n:Nat} (r: ByteVec (2*n)) : Vector n GF :=
  Vector.generate n (λi => loadGf r (2*i.val))

@[extern "lean_store_gf"]
opaque store_gf (irr : Vector sys_t GF) : ByteVec (2*sys_t)

def secretKeyBytes : Nat := 40 + 2*sys_t + cond_bytes + N/8

@[extern "lean_controlbitsfrompermutation2"]
opaque controlBitsFromPermutation2 (pi : Vector (1 <<< gfbits) GF) : ByteVec cond_bytes

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
      let c  : BitVec (1 <<< si) := cb.extractN! i stride
      let p1 : Vector (1 <<< si) GF := pi.extractN! (2*i) stride
      let p2 : Vector (1 <<< si) GF := pi.extractN! (2*i+stride) stride
      select c p2 p1 ++ select c p1 p2

def testPerm (out : ByteVec cond_bytes) :  Vector (1 <<< gfbits) GF := Id.run do
  let w  := gfbits
  let n  := 1 <<< gfbits
  let n4 := n >>> 4
  let out :=
        Vector.generate (2*w-1) λi =>
          let cb := out.extractN (n4 * i) n4
          BitVec.generate (1 <<< gfbits) λi => (cb.get! (i.val/8)).testBit (i.val%8)
  let mut pi := Vector.generate n (λi => (OfNat.ofNat i.val : GF))
  for i in range 0 w do
    let cb := out.get! i
    pi := layer pi cb ⟨i, sorry⟩
  for j in range 0 (w-1) do
    let cb := out.get! (w+j)
    let i := (w - 2) - j
    pi := layer pi cb ⟨i, sorry⟩
  pure pi

def controlBitsFromPermutation (pi : Vector (1 <<< gfbits) GF) : Option (ByteVec cond_bytes) :=
  let out := controlBitsFromPermutation2 pi
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

def byteVec (sk:SecretKey) : ByteVec Mceliece348864Ref.secretKeyBytes :=
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
      prod := prod.set! (i+j) (prod.get! (i+j) + x.get! i * y.get! j)
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
      mat := genPolyGenUpdate mat j (gf_inv r)
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
  BitVec.generate_lsb N λi =>
    let gf := inv.get i
    gf.bit k

def flatten [Inhabited α] (v : Vector m (Vector n α)) : Vector (m*n) α :=
  Vector.generate (m*n) λi => (v.get! (i.val/n)).get! (i.val%n)

def init_mat (g : Vector sys_t GF) (L : Vector N GF) : Vector pk_nrows (BitVec N) := Id.run do
  let g' := g.push 1
  let inv0 := (λx => gf_inv (eval g' x)) <$> L
  flatten $
    Vector.generate sys_t λi =>
      let inv := Vector.generate N λj =>
            inv0.get! j * exp (L.get! j) i
      Vector.generate gfbits λk => init_mat_row inv k

def gaussian_elim_row (m : @&(Vector pk_nrows (BitVec N))) (row: Nat)
  : Option (Vector pk_nrows (BitVec N)) := Id.run do
  let mut mat_row := m.get! row
  for k in rangeH (row+1) pk_nrows do
    let mat_k := m.get! k
    let mask1 := mat_row.lsb_get! row
    let mask2 := mat_k.lsb_get! row
    if mask1 ≠ mask2 then
      mat_row := mat_row ^^^ mat_k
  if not (mat_row.lsb_get! row) then
    return none
  let mut m := m
  for k in range 0 pk_nrows do
    if k = row then
      m := m.set! k mat_row
    else
      let mat_k := m.get! k
      if mat_k.lsb_get! row then
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
  let g ← genPolyGen $ loadGfArray $ r.extractN (N/8 + 4*(1 <<< gfbits)) (2*sys_t)
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

def mkCryptoKemKeypair (iseed : Seed) (attempts: optParam Nat 10) : Option (KeyPair × DRBG) := do
  let rec loop : ByteVec 32 → Nat → Option KeyPair
      | _, 0 => none
      | seed, Nat.succ n => do
        let r := shake rw (#v[64] ++ seed).data
        match tryCryptoKemKeypair seed r with
        | some kp => some kp
        | none =>
          loop (r.takeFromEnd 32) n
  let drbg := randombytesInit iseed
  let (bytes, drbg) := randombytes drbg 32
  match loop bytes attempts with
  | none => none
  | some p => some (p, drbg)

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
    e := e.msbb_set! v.val true
  pure e

def tryGenerateErrors (drbg:DRBG) : Option (BitVec N) × DRBG := Id.run do
  let (bytes, drbg) := randombytes drbg (4*sys_t)
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
          return (none, drbg)
        return (some (generateErrorBitmask v), drbg)
  pure ⟨none, drbg⟩

def cSyndrome (pk : PublicKey) (e: BitVec N) : BitVec pk_nrows := Id.run do
  let mut s : BitVec pk_nrows := BitVec.zero _
  for i in range 0 pk_nrows do
    let off := (BitVec.zero pk_nrows).msbb_set! i True
    let row : BitVec N := off ++ pk.get! i
    if (row &&& e).foldl (· ^^^ ·) false then
      s := s.msbb_set! i True
  pure s

@[reducible]
structure Ciphertext where
  syndrome : BitVec pk_nrows
  hash : ByteVec 32

namespace Ciphertext

protected def bytes (c:Ciphertext) : ByteVec 128 :=
  bitvecToByteVec_msbb (pk_nrows/8) c.syndrome ++ c.hash

protected def toString (c:Ciphertext) : String := c.bytes.toString

instance : ToString Ciphertext := ⟨Ciphertext.toString⟩

def mkHash (e:BitVec N) : ByteVec 32 :=
  cryptoHash32b (#b[2].data ++ (bitvecToByteVec_msbb (N/8) e).data)

end Ciphertext

structure Plaintext where
  e : BitVec N
  c : Ciphertext

namespace Plaintext

protected def bytes (p:Plaintext) :  ByteVec 32 :=
  cryptoHash32b (#b[1].data ++ (bitvecToByteVec_msbb (N/8) p.e).data ++ p.c.bytes.data)

protected def toString (p:Plaintext) : String := p.bytes.toString

instance : ToString Plaintext := ⟨Plaintext.toString⟩

end Plaintext

structure EncryptionResult where
  e : BitVec N
  ct : Ciphertext

def EncryptionResult.ss (r:EncryptionResult) : Plaintext := { e := r.e, c := r.ct }

def mkCryptoKemEnc (drbg:DRBG) (attempts:Nat) (pk:PublicKey) : Option (EncryptionResult × DRBG) := do
  match tryN tryGenerateErrors drbg attempts with
  | (some e, drbg) =>
    let c   := { syndrome := cSyndrome pk e,
                 hash := Ciphertext.mkHash e
                }
    some ({ e := e, ct := c }, drbg)
  | (none, _) => panic! "mkCryptoKemEnc def failure"

@[extern "lean_transpose64"]
opaque tranpose64 (a : @&(Vector 64 UInt64)) : Vector 64 UInt64

def load4_64
  (c : ByteVec 256)
  : Vector 64 UInt64 :=
  Vector.generate 64 $ λi => Id.run do
    let mut r := 0
    for j in range 0 4 do
      r := (r <<< 8) ||| (c.get! (4*i+3-j)).toNat
    pure $ UInt64.ofNat r

def benes_layer
  (data : @&(Vector 64 UInt64))
  (bits : @&(Vector 32 UInt64))
  (lgs : @&Nat)
    : Vector 64 UInt64 := Id.run do
  let s : Nat := 1 <<< lgs
  let mut data := data
  for h2 in range 0 (32 >>> lgs) do
    let h := h2 <<< lgs
    for k in range 0 s do
      let j := 2 * h + k
      let d := (data.get! j ^^^ data.get! (j+s)) &&& bits.get! (h+k)
      data := data.xor! j d
      data := data.xor! (j+s) d
  pure data

def slice {m:Nat} (v:ByteVec m) (l n : Nat) : ByteVec n :=
  ByteVec.generate n (λi => v.get! (l+i))

def load8 (n:Nat) : UInt64 := Id.run do
  let mut r := 0
  for j in range 0 8 do
    r := (r <<< 8) ||| ((n >>> (8*j)) &&& 0xff)
  pure $ UInt64.ofNat r

def load8_32 (c: ByteVec 256) : Vector 32 UInt64 :=
  Vector.generate 32 $ λi => Id.run do
    let mut r := 0
    for j in range 0 8 do
      r := (r <<< 8) ||| (c.get! (8*i+(7-j))).toNat
    pure $ UInt64.ofNat r

def bitvecFromUInt64Vec (r:Vector 64 UInt64) : BitVec (1 <<< gfbits) :=
  BitVec.generate_lsb (1 <<< gfbits) $ λi =>
    let e := r.get! (63 - i/64)
    let m := i.val % 64
    let m2 := 8 * (7 - m/8) + m % 8
    (e &&& UInt64.ofNat (1 <<< m2)) ≠ 0

def apply_benes0 (r : BitVec (1 <<< gfbits))
                 (c : ByteVec cond_bytes)
    : BitVec (1 <<< gfbits) := Id.run do
  let inc := 256

  let mut a :=
      Vector.generate 64 $ λi =>
        load8 ((r.val >>> (64*(63-i.val))) &&& (2^64 - 1))
  a := tranpose64 a
  for l in range 0 6 do
    let c := slice c (inc*l) inc
    let c := load4_64 c
    let c := tranpose64 c
    let c := Vector.generate 32 (λi => c.get! i)
    a := benes_layer a c l
  a := tranpose64 a
  for i in range 0 6 do
    let c := slice c (inc*(6+i)) inc
    a := benes_layer a (load8_32 c) i
  for j in range 0 5 do
    let i := 4 - j
    let c := slice c (inc*(16-i)) inc
    a := benes_layer a (load8_32 c) i
  a := tranpose64 a
  for j in range 0 6 do
    let l := 5 - j
    let c := slice c (inc*(22-l)) inc
    let c := load4_64 c
    let c := tranpose64 c
    let c := Vector.generate 32 (λi => c.get! i)
    a := benes_layer a c l
  a := tranpose64 a

  pure (bitvecFromUInt64Vec a)

def support_gen (c : ByteVec cond_bytes) : Vector N GF := Id.run do
  let L : Vector gfbits (BitVec (1 <<< gfbits)) :=
        Vector.generate gfbits λj =>
          let v :=
            BitVec.generate_msbb _ λ(i : Fin (1 <<< gfbits)) =>
              let i : GF := OfNat.ofNat i.val
              i.bitrev.bit j
          apply_benes0 v c
  Vector.generate N λ i => Id.run do
    let mut si : Nat := 0
    for k in range 0 gfbits do
      let j := gfbits-1-k
      si := si <<< 1 ||| (if (L.get! j).msbb_get! i.val then 1 else 0)
    pure (OfNat.ofNat si)

def synd
    (g: Vector sys_t GF)
    (l : Vector N GF)
    (error_bitmask : BitVec N)
   : Vector (2*sys_t) GF := Id.run do
  let mut out := Vector.replicate (2*sys_t) 0
  let f := g.push 1
  for i in range 0 N do
    if error_bitmask.msbb_get! i then
      let e := eval f (l.get! i)
      let mut e_inv := gf_inv (e * e)
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
      d := d ^^^ (C.get! i * s.get! (N-i))

    if d ≠ 0 then
      let f := GF.frac b d
      let T := C
      C := Vector.generate (sys_t+1) λi => C.get! i ^^^ (f * B.get! i)
      if N ≥ 2*L then
        L := N+1-L
        B := T
        b := d
    B := Vector.generate (sys_t+1) λi =>
           if i = 0 then 0 else B.get! (i-1)
  pure $ Vector.generate (sys_t+1) λi => C.get! (sys_t-i)

def cryptoKemDec1 (c : Ciphertext) (sk : SecretKey) : Option (BitVec N) := do
  let g := sk.goppa
  let l := support_gen sk.controlbits
  let r : BitVec N := c.syndrome ++ BitVec.zero (N-pk_nrows)
  let s := synd g l r
  let locator := bm s
  let images := (λi => gf_inv (eval locator i)) <$> l

  let mut w : Nat := 0
  let mut e : BitVec N := BitVec.zero _
  for i in range 0 N do
    if images.get! i = 0 then
      e := e.msbb_set! i True
      w := w + 1
  -- Generate preimage
  if w = sys_t ∧ Ciphertext.mkHash e = c.hash ∧ s = synd g l e then
    some e
  else
    none

-- This is the basic correctness theorem that if we
-- make a public key from Goppa polynomial and permutation
-- and use that to generate an encryption key result, then
-- we can decrypt it.
theorem decryptEncrypt (drbg drbg' : DRBG)
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

end Mceliece348864Ref