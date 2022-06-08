import Crypto.BitVec
import Crypto.ByteBuffer
import Crypto.ByteVec2
import Crypto.Matrix
import Crypto.UInt8
import Crypto.Vec
import Crypto.Vector

def ByteVec.toBuffer {n:Nat} : ByteVec n → ByteBuffer
| ⟨a,_⟩ => ⟨a⟩

instance : Coe (ByteVec n) ByteBuffer where
  coe := ByteVec.toBuffer

structure DRBG where
  key : BitVec 256
  v : BitVec 128

instance : Inhabited DRBG := ⟨Inhabited.default, Inhabited.default⟩

open Kind

@[reducible]
def Seed := vec 48 (vec 8 bit)

@[extern "lean_random_init"]
constant randombytesInit : @&Seed → DRBG

@[extern "lean_random_bytes"]
constant randombytes (rbg:DRBG) (n:@&Nat) : ByteVec n × DRBG

@[extern "lean_random_bits"]
constant randombits (rbg:DRBG) (n:@&Nat) : BitVec n × DRBG

def mkRandom (drbg:DRBG) (K:Kind) : K × DRBG :=
  let ⟨b,d⟩ := randombits drbg K.width
  ⟨⟨b⟩,d⟩

def initKeypairSeedPrefix : ByteVec 1 := #v[64]

def initKeypairSeed (v:ByteVec 32) : ByteVec 33 := initKeypairSeedPrefix ++ v

@[extern "lean_crypto_hash_32b"]
constant cryptoHash32b : ByteBuffer → ByteVec 32

namespace Mceliece348864Ref
def name : String := "mceliece348864"
def publicKeyBytes : Nat := 261120
def secretKeyBytes : Nat := 6492

def plaintextBytes : Nat := 32

@[reducible]
def ciphertextBytes : Nat := 128

def N := 3488

@[reducible]
def gfbits : Nat := 12

@[reducible]
def sys_t : Nat := 64

@[reducible]
def sys_n : Nat := 3488

@[reducible]
def pk_nrows : Nat := sys_t * gfbits

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

def cond_bytes : Nat := (1 <<< (gfbits-4))*(2*gfbits - 1)

@[extern "lean_store_gf"]
constant store_gf (irr : Vector sys_t GF) : ByteVec (2*sys_t)

@[extern "lean_init_pi"]
constant init_pi (perm : Vector (1 <<< gfbits) UInt32)
  : Option (Vector (1 <<< gfbits) GF)

@[extern "lean_eval"]
constant eval (sk : Vector sys_t GF) (x : GF) : GF

@[extern "lean_pk_gen2"]
constant pk_gen2 (inv : Vector sys_n GF) (L : Vector sys_n GF)
  : Option PublicKey

@[extern "lean_controlbitsfrompermutation"]
constant controlBitsFromPermutation (pi : Vector (1 <<< gfbits) GF) : ByteVec cond_bytes

def tryCryptoKemKeypair (seed: ByteVec 32) (r: ByteVec rw) : Option KeyPair := do
  let sk_input :=                      r.extractN 0 (N/8)
  let irr ← genPolyGen $ loadGfArray $ r.extractN (N/8 + 4*(1 <<< gfbits)) (2*sys_t)

  let pi  ← init_pi    $ load4Array  $ r.extractN (N/8) (4*(1 <<< gfbits))
  let L := Vector.generate sys_n λi => gf_bitrev (pi.get! i)
  let inv := Vector.generate sys_n (λi => gf_inv (eval irr (L.get! i)))

  let pk ← pk_gen2 inv L
  some ⟨pk, seed ++ ByteVec.ofUInt64lsb 0xffffffff ++ store_gf irr ++ controlBitsFromPermutation pi ++ sk_input⟩

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

def gfmask : UInt16 := UInt16.ofNat $ (1 <<< gfbits) - 1

def load_gf (src : ByteVec 2) : UInt16 :=
  ((src.get ⟨0, Nat.le.step Nat.le.refl⟩).toUInt16 <<< 8 ||| (src.get ⟨1, Nat.le.refl⟩).toUInt16) &&& gfmask

@[extern "lean_crypto_gen_e_step1"]
constant gen_e_step1 : @&(Vector (2*sys_t) GF) → Option (vec sys_t (vec 16 bit))

@[extern "lean_crypto_gen_e_step2"]
constant gen_e_step2 : @&(vec sys_t (vec 16 bit)) → ByteVec sys_t

@[extern "lean_crypto_gen_e_step3"]
constant gen_e_step3 : @&(vec sys_t (vec 16 bit)) → @&(ByteVec sys_t) → ByteVec (N / 8)

def cGenE2 : ∀(drbg:DRBG) (attempts:Nat), Option (ByteVec (N / 8) × DRBG)
  | _, 0 =>
    none
  | drbg, Nat.succ attempts =>
    let (bytes, drbg) := randombytes drbg _
    let a := loadGfArray bytes
    match gen_e_step1 a with
    | none =>
      cGenE2 drbg attempts
    | some ind =>
      let val := gen_e_step2 ind
      some (gen_e_step3 ind (gen_e_step2 ind), drbg)

@[extern "lean_crypto_syndrome"]
constant cSyndrome : @&PublicKey
                   → @&(ByteVec (N / 8))
                   → ByteVec synd_bytes

def mkCryptoKemEnc (drbg:DRBG) (attempts:Nat) (pk:PublicKey) : Option (EncryptionResult × DRBG) := do
  match cGenE2 drbg attempts with
  | none => none
  | some (e, drbg) =>
    let c   := cSyndrome pk e ++ cryptoHash32b (#b[2] ++ e)
    let key := cryptoHash32b $ #b[1] ++ e ++ c
    some (⟨key, c⟩, drbg)

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