import Crypto.BitVec
import Crypto.ByteBuffer
import Crypto.ByteVec2
import Crypto.UInt8
import Crypto.Vec

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

def mkRandom (drbg:DRBG) (K:Kind) : K × DRBG := randombits drbg K.width

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

@[extern "lean_load_gf_array"]
constant loadGfArray (r: ByteVec (2*sys_t)) : ByteVec (2*sys_t) -- FIXME: Make Uint16vec with sys_t elements

@[extern "lean_genpoly_gen"]
constant genPolyGen (f : ByteVec (2*sys_t)) : Option (ByteVec (2*sys_t))

@[extern "lean_load4_array"]
constant load4Array (r: ByteVec (4*(1 <<< gfbits))) : ByteVec (4*(1 <<< gfbits)) -- FIXME: Make Uint32vec with (1 <<< gfbits) elements

def irr_bytes : Nat := sys_t * 2

def cond_bytes : Nat := (1 <<< (gfbits-4))*(2*gfbits - 1)

@[extern "lean_store_gf"]
constant store_gf (irr : ByteVec (2*sys_t)) : ByteVec (2*sys_t)

@[extern "lean_pk_gen"]
constant pk_gen (sk : ByteVec (2*sys_t)) (perm : ByteVec (4*(1 <<< gfbits)))
  : Option (PublicKey × ByteVec (2*(1 <<< gfbits)))

@[extern "lean_controlbitsfrompermutation"]
constant controlBitsFromPermutation (pi : ByteVec (2*(1 <<< gfbits))) : ByteVec cond_bytes

def tryCryptoKemKeypair (seed: ByteVec 32) (r: ByteVec rw) : Option KeyPair := do
  let sk_input   := r.extractN 0 (N/8)
  let perm_input := r.extractN (N/8) (4*(1 <<< gfbits))
  let irr_input  := r.extractN (N/8 + 4*(1 <<< gfbits)) (2*sys_t)
  let f := loadGfArray irr_input
  let perm := load4Array perm_input
  match genPolyGen f with
  | none => none
  | some irr =>
    let sk := store_gf irr
    match pk_gen sk perm with
    | none => none
    | some (pk, pi) =>
      some ⟨pk, seed ++ ByteVec.ofUInt64lsb 0xffffffff ++ sk ++ controlBitsFromPermutation pi ++ sk_input⟩

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
constant gen_e_step1 : @&(ByteVec (4 * sys_t)) → Option (vec sys_t (vec 16 bit))

@[extern "lean_crypto_gen_e_step2"]
constant gen_e_step2 : @&(vec sys_t (vec 16 bit)) → ByteVec sys_t

@[extern "lean_crypto_gen_e_step3"]
constant gen_e_step3 : @&(vec sys_t (vec 16 bit)) → @&(ByteVec sys_t) → ByteVec (N / 8)


def hasDuplicate (v:vec sys_t (vec 16 bit)) : Bool := Id.run do
  for i in [0:sys_t] do
    for j in [0:i] do
      if v.get! i = v.get! j then
        return true
  return false


def cGenE2 : ∀(drbg:DRBG) (attempts:Nat), Option (ByteVec (N / 8) × DRBG)
  | _, 0 =>
    none
  | drbg, Nat.succ attempts =>
    let (bytes, drbg) := randombytes drbg (4*sys_t)
    match gen_e_step1 bytes with
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