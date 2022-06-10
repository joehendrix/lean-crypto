import Crypto.ByteBuffer
import Crypto.ByteVec2
import Crypto.Matrix
import Crypto.UInt8
import Crypto.Vector

def ByteVec.toBuffer {n:Nat} : ByteVec n → ByteBuffer
| ⟨a,_⟩ => ⟨a⟩

instance : Coe (ByteVec n) ByteBuffer where
  coe := ByteVec.toBuffer

structure DRBG where
  key : ByteVec (256 / 8)
  v : ByteVec (128 / 8)

instance : Inhabited DRBG := ⟨Inhabited.default, Inhabited.default⟩

def tryN {α:Type _ } (f:DRBG → Option α × DRBG)
     : ∀(drbg:DRBG) (attempts:Nat), Option α × DRBG
  | drbg, 0 =>
    (none, drbg)
  | drbg, Nat.succ attempts =>
    match f drbg with
    | (some ind, drbg) => (some ind, drbg)
    | (none, drbg) => tryN f drbg attempts

--open Kind

@[reducible]
def Seed := ByteVec 48

@[extern "lean_random_init"]
constant randombytesInit : @&Seed → DRBG

@[extern "lean_random_bytes"]
constant randombytes (rbg:DRBG) (n:@&Nat) : ByteVec n × DRBG

def initKeypairSeedPrefix : ByteVec 1 := #v[64]

def initKeypairSeed (v:ByteVec 32) : ByteVec 33 := initKeypairSeedPrefix ++ v

@[extern "lean_crypto_hash_32b"]
constant cryptoHash32b : ByteBuffer → ByteVec 32

namespace Mceliece348864Ref

def name : String := "mceliece348864"


def plaintextBytes : Nat := 32

@[reducible]
def ciphertextBytes : Nat := 128

def N := 3488

@[reducible]
def gfbits : Nat := 12

@[reducible]
def sys_t : Nat := 64

@[reducible]
def cond_bytes : Nat := (1 <<< (gfbits-4))*(2*gfbits - 1)

def secretKeyBytes : Nat := 40 + 2*sys_t + cond_bytes + N/8

@[reducible]
def pk_nrows : Nat := sys_t * gfbits

@[reducible]
def pk_ncols : Nat := N - pk_nrows

def publicKeyBytes : Nat := pk_nrows * (pk_ncols / 8)

@[reducible]
def synd_bytes : Nat := ((pk_nrows + 7)/8)

def PublicKey := ByteVec Mceliece348864Ref.publicKeyBytes
  deriving ToString

@[reducible]
def SecretKey := ByteVec Mceliece348864Ref.secretKeyBytes
  deriving ToString

def Plaintext := ByteVec Mceliece348864Ref.plaintextBytes
  deriving DecidableEq, Inhabited, ToString

@[reducible]
def Ciphertext := ByteVec Mceliece348864Ref.ciphertextBytes
  deriving ToString

structure KeyPair where
  pk : PublicKey
  sk : SecretKey

@[extern "lean_shake256"]
constant shake (w:Nat) (input: ByteArray) : ByteVec w

@[reducible]
def rw : Nat :=  N/8 + 4*(1 <<< gfbits) + sys_t * 2 + 32

def gfMask : UInt16 := (1 <<< 12) - 1

@[reducible]
def GF := { x:UInt16 // x < (1<<<12) }

namespace GF

instance : Inhabited GF := ⟨⟨0, sorry⟩⟩

protected def complement (x:GF) : GF := ⟨~~~x.val, sorry⟩
protected def and (x y:GF) : GF := ⟨x.val &&& y.val, sorry⟩
protected def or  (x y:GF) : GF := ⟨x.val ||| y.val, sorry⟩
protected def xor  (x y:GF) : GF := ⟨x.val ^^^ y.val, sorry⟩

@[extern "lean_gf_mul"]
protected constant mul (x y : GF) : GF

-- FIXME: Define classes
instance : Complement GF := ⟨GF.complement⟩
instance : AndOp GF := ⟨GF.and⟩
instance : OrOp GF := ⟨GF.or⟩
instance : Xor GF := ⟨GF.xor⟩
instance : Mul GF := ⟨GF.mul⟩

instance (n:Nat) : OfNat GF n := { ofNat := ⟨UInt16.ofNat n &&& gfMask, sorry⟩ }

end GF

def loadGf {n} (r: ByteVec n) (i:Nat) : GF :=
  let f (x:UInt8) : UInt16 := UInt16.ofNat x.toNat
  let w : UInt16 := f (r.get! (i+1)) <<< 8 ||| f (r.get! i)
  ⟨w &&& gfMask, sorry⟩

def loadGfArray {n:Nat} (r: ByteVec (2*n)) : Vector n GF :=
  Vector.generate n (λi => loadGf r (2*i.val))

def byteToUInt32 (v:UInt8) : UInt32 := UInt32.ofNat (v.toNat)

def load4 {n} (r: ByteVec n) (i:Nat) : UInt32 :=
  let b (j:Nat) (s:UInt32) : UInt32 := byteToUInt32 (r.get! (i+j)) <<< s
  b 0 0 ||| b 1 8 ||| b 2 16 ||| b 3 24

def load4Array {n:Nat} (r: ByteVec (4*n)) : Vector n UInt32 :=
  Vector.generate n (λi => load4 r (4*i.val))


@[extern "lean_GF_mul"]
constant GF_mul (x y : Vector sys_t GF) : Vector sys_t GF

@[extern "lean_gf_iszero"]
constant gf_iszero : GF -> GF

@[extern "lean_gf_inv"]
constant gf_inv : GF -> GF

@[extern "lean_bitrev"]
constant gf_bitrev : GF -> GF

def genPolyGen_mask (mat : Matrix (sys_t+1) sys_t GF) (j:Nat) : GF := Id.run do
  let mut r := mat.get! j j
  for i in range j (sys_t + 1 - j) do
    for k in range (j+1) (sys_t - (j+i)) do
      r := r ^^^ mat.get! i k
  pure r

def genPolyGenUpdate (mat : Matrix (sys_t+1) sys_t GF)
                         (j : Nat)
                         (inv : GF)
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
    let r0 := mat.get! j j
    let r := genPolyGen_mask mat j
    let mask := gf_iszero r0
    let r := r0 &&& ~~~mask ||| r &&& mask
    if r = 0 then
      return none
    else
      mat := genPolyGenUpdate mat j (gf_inv r)
  some (mat.row! sys_t)

def irr_bytes : Nat := sys_t * 2


@[extern "lean_store_gf"]
constant store_gf (irr : Vector sys_t GF) : ByteVec (2*sys_t)

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

@[extern "lean_eval"]
constant eval (sk : Vector sys_t GF) (x : GF) : GF

def pk_row_bytes : Nat := pk_ncols / 8

@[extern "lean_init_mat"]
constant init_mat (inv : @&(Vector N GF)) (L : @&(Vector N GF))
  : Matrix pk_nrows (N/8) UInt8

@[extern "lean_gaussian_elim_row"]
constant gaussian_elim_row (m : @&(Matrix pk_nrows (N/8) UInt8)) (r: Nat)
  : Option (Matrix pk_nrows (N/8) UInt8)

def gaussian_elim (m : @&(Matrix pk_nrows (N/8) UInt8))
  : Option (Matrix pk_nrows (N/8) UInt8) := Id.run do
  let mut m := m
  for i in range 0 pk_nrows do
    match gaussian_elim_row m i with
    | some m' => m := m'
    | none => return none
  pure (some m)

-- Create public key from row matrix
def init_pk (m : Matrix pk_nrows (N/8) UInt8) : PublicKey :=
  ByteVec.generate publicKeyBytes λi =>
    let r := i.val / pk_row_bytes
    let c := i.val % pk_row_bytes
    m.get! r (pk_nrows/8 + c)

@[extern "lean_controlbitsfrompermutation"]
constant controlBitsFromPermutation (pi : Vector (1 <<< gfbits) GF) : ByteVec cond_bytes

def tryCryptoKemKeypair (seed: ByteVec 32) (r: ByteVec rw) : Option KeyPair := do
  let sk_input :=                      r.extractN 0 (N/8)
  let irr ← genPolyGen $ loadGfArray $ r.extractN (N/8 + 4*(1 <<< gfbits)) (2*sys_t)
  let pi  ← randomPermutation $ load4Array $ r.extractN (N/8) (4*(1 <<< gfbits))
  let L   := Vector.generate N λi => gf_bitrev (pi.get! i)
  let inv := Vector.generate N λi => gf_inv (eval irr (L.get! i))
  let m ← gaussian_elim (init_mat inv L)
  let pk := init_pk m
  let sk := seed ++ ByteVec.ofUInt64lsb 0xffffffff
                 ++ store_gf irr
                 ++ controlBitsFromPermutation pi
                 ++ sk_input
  some ⟨pk, sk⟩

def mkCryptoKemKeypair (iseed : Seed) (attempts: optParam Nat 10) : Option (KeyPair × DRBG) := do
  let rec loop : ∀(seed: ByteVec 32) (attempts:Nat), Option KeyPair
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

structure EncryptionResult where
  ss : Plaintext
  ct : Ciphertext

def gen_e_step0 (v : Vector (2*sys_t) GF) (n:Nat) : Option (Vector n (Fin N)) := Id.run do
  let mut ind : Array (Fin N) := Array.mkEmpty sys_t
  for num in v.data do
    let num := num.val.toNat
    if lt : num < N then
      ind := ind.push ⟨num, lt⟩
      if eq:ind.size = n then
        return (some ⟨ind, eq⟩)
  pure none

def has_duplicate {n:Nat} {α:Type} [DecidableEq α] (v: Vector n α) : Bool := Id.run do
  for i in range 1 (n-1) do
    for j in range 0 i do
      if lt_i : i < n then
        if lt_j : j < n then
          if v.get ⟨i, lt_i⟩ = v.get ⟨j, lt_j⟩ then
            return true
  pure false

def gen_e_step1b (v : Vector (2*sys_t) GF) : Option (Vector sys_t (Fin N)) := do
  let ind ← gen_e_step0 v sys_t
  if has_duplicate ind then
    none
  else
    some ind

def gen_e_step1 (drbg:DRBG) : Option (Vector sys_t (Fin N)) × DRBG :=
  let (bytes, drbg) := randombytes drbg _
  let a := loadGfArray bytes
  match gen_e_step0 a sys_t with
  | none => (none, drbg)
  | some ind =>
    if has_duplicate ind then
      (none, drbg)
    else
      (some ind, drbg)

@[extern "lean_crypto_gen_e_step3"]
constant gen_e_step3b (v: @&(Vector sys_t (Fin N))) : ByteVec (N / 8)

@[extern "lean_crypto_syndrome"]
constant cSyndrome : @&PublicKey
                   → @&(ByteVec (N / 8))
                   → ByteVec synd_bytes

def mkCryptoKemEnc (drbg:DRBG) (attempts:Nat) (pk:PublicKey) : Option (EncryptionResult × DRBG) := do
  match tryN gen_e_step1 drbg attempts with
  | (some ind, drbg) =>
    let e   := gen_e_step3b ind
    let c   := cSyndrome pk e ++ cryptoHash32b (#b[2] ++ e)
    let key := cryptoHash32b $ #b[1] ++ e ++ c
    some (⟨key, c⟩, drbg)
  | (none, _) => panic! "mkCryptoKemEnc def failure"

@[extern "lean_decrypt"]
constant decrypt (ct : @&(ByteVec synd_bytes)) (sk : @&(ByteVec (secretKeyBytes - 40))) : ByteVec (N / 8) × UInt8


def cryptoKemDec (c : @&Ciphertext) (sk : @&SecretKey) : Plaintext := Id.run $ do
  let c_cipher := c.extractN 0 synd_bytes
  let c_hash   := c.extractN synd_bytes 32
  let (e, ret_decrypt) := decrypt c_cipher (sk.drop 40)
  let conf := cryptoHash32b (#b[2] ++ e)
  let ret_confirm := ByteVec.orAll (conf ^^^ c_hash)
  let m : UInt16 := (ret_decrypt ||| ret_confirm).toUInt16
  let m := m - 1
  let m := (m >>> 8 : UInt16).toUInt8
  -- Generate preimage
  let s := sk.extractN (40 + irr_bytes + cond_bytes) (N/8)
  let preimageX : ByteVec (N/8) := ~~~m &&& s
  let preimageY : ByteVec (N/8) := m &&& (e.extractN 0 (N/8))
  let preimage := preimageX ||| preimageY
  pure $ cryptoHash32b $ #b[m &&& 1] ++ preimage ++ c

end Mceliece348864Ref