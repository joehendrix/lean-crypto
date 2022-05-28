import Crypto.ByteBuffer
import Crypto.ByteVec
import Crypto.Core
import Crypto.UInt8
import Crypto.Vec

def ByteVec.toBuffer {n:Nat} : ByteVec n → ByteBuffer
| ⟨a,_⟩ => ⟨a⟩

instance : Coe (ByteVec n) ByteBuffer where
  coe := ByteVec.toBuffer

--def UInt8.toUInt16 : UInt8 → UInt16 := UInt16.ofNat ∘ UInt8.toNat
--def UInt16.toUInt8 : UInt16 → UInt8 := UInt8.ofNat ∘ UInt16.toNat

def Bit := Bool

def Byte := Vec 8 Bit

-- Concatenates a vector together
--def Vec.flatten {α} {m n} : Vec m (Vec n α) → Vec (m * n) α := sorry

structure DRBG where
  key : ByteVec 32
  v : ByteVec 16

instance : Inhabited DRBG := ⟨Inhabited.default, Inhabited.default⟩

@[extern "lean_randombytes_init"]
constant randombytesInit : @&(ByteVec 48) → DRBG

@[extern "lean_randombytes"]
constant randombytes (rbg:DRBG) (n:@&Nat) : ByteVec n × DRBG

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

@[extern "lean_try_crypto_kem_keypair"]
constant tryCryptoKemKeypair (seed: ByteVec 33) : Option KeyPair × ByteVec 33

def mkCryptoKemKeypair (iseed : ByteVec 48) (attempts: optParam Nat 10) : Option (KeyPair × DRBG) := do
  let rec loop : ∀(seed: ByteVec 33) (attempts:Nat), Option KeyPair
      | _, 0 => none
      | seed, Nat.succ n => do
        match tryCryptoKemKeypair seed with
        | ⟨some kp, _⟩ => some kp
        | ⟨none, seed'⟩ => loop seed' n
  let drbg := randombytesInit iseed
  let (bytes, drbg) := randombytes drbg 32
  match loop (#v[64] ++ bytes) attempts with
  | none => none
  | some p => some (p, drbg)

structure EncryptionResult where
  ss : Plaintext
  ct : Ciphertext


def gfmask : UInt16 := UInt16.ofNat $ (1 <<< gfbits) - 1

def load_gf (src : ByteVec 2) : UInt16 :=
  ((src.get ⟨0, Nat.le.step Nat.le.refl⟩).toUInt16 <<< 8 ||| (src.get ⟨1, Nat.le.refl⟩).toUInt16) &&& gfmask

open Crypto

@[reducible]
def Byte := vec 8 bit

/-
def conv1 : Vec (4 * sys_t) Byte → Vec (2 * sys_t) (ByteVec 2) := sorry

def elt1 {n} {α} : Vec n α → i → α := sorry

def gen_e {m} [MonadRandom m] (attempts: optParam Nat 20) : m (ByteVec (N/8)) := do
  let rec loop : ∀(attempts:Nat), m (ByteVec sys_t)
      | 0 =>
        giveUp "Failed to generate error vector."
      | Nat.succ attempts => do
        let bytes ← mkRandom (vec (4*sys_t) Byte)
        let bytes2 := conv1 bytes
        let nums := load_gf <$> bytes2
        let nums : Array UInt16 :=
          Array.generate (2*sys_t) $ λi => load_gf (elt1 bytes2 i) -- .extract (2*i) (2*i+2))
        pure sorry
  let v ← loop attempts
  pure sorry
-/

@[extern "lean_crypto_gen_e_step1"]
constant gen_e_step1 : @&(ByteVec (4 * sys_t)) → Option (ByteVec (2 * sys_t))

@[extern "lean_crypto_gen_e_step2"]
constant gen_e_step2 : @&(ByteVec (2 * sys_t)) → ByteVec sys_t

@[extern "lean_crypto_gen_e_step3"]
constant gen_e_step3 : @&(ByteVec (2 * sys_t)) → @&(ByteVec sys_t) → ByteVec (N / 8)

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

def irr_bytes : Nat := sys_t * 2

def cond_bytes : Nat := (1 <<< (gfbits-4))*(2*gfbits - 1)

def cryptoKemDec (c : @&Ciphertext) (sk : @&SecretKey) : Plaintext := Id.run $ do
  let c_cipher := c.extract 0 synd_bytes
  let c_hash : ByteVec 32 := c.extract synd_bytes (synd_bytes+32)
  let (e, ret_decrypt) := decrypt c_cipher (sk.drop 40)
  let conf := cryptoHash32b (#b[2] ++ e)
  let ret_confirm := ByteVec.orAll (conf ^^^ c_hash)
  let m : UInt16 := (ret_decrypt ||| ret_confirm).toUInt16
  let m := m - 1
  let m := (m >>> 8 : UInt16).toUInt8

  -- Generate preimage
  let s := sk.extract (40 + irr_bytes + cond_bytes) (40 + irr_bytes + cond_bytes + N/8)
  let preimageX : ByteVec (N/8) := ~~~m &&& s
  let preimageY : ByteVec (N/8) := m &&& (e.extract 0 (N/8))
  let preimage := preimageX ||| preimageY
  pure $ cryptoHash32b $ #b[m &&& 1] ++ preimage ++ c

end Mceliece348864Ref