import Crypto.ByteBuffer
import Crypto.ByteVec
import Crypto.UInt8

def ByteVec.toBuffer {n:Nat} : ByteVec n → ByteBuffer
| ⟨a,_⟩ => ⟨a⟩ 

instance : Coe (ByteVec n) ByteBuffer where
  coe := ByteVec.toBuffer

theorem add_le_implies_le_rhs {j k : Nat} : ∀(i : Nat), (h : i + j ≤ k) → j ≤ k
| Nat.succ i, h => add_le_implies_le_rhs i (Nat.le_of_succ_le (Nat.succ_add i j ▸ h))
| 0, h => Nat.zero_add j ▸ h

@[inline] def forFinM {m} [Monad m] (n : Nat) (f : Fin n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ (i:Nat), (p : i ≤ n) → m Unit 
    | 0, p => pure ()
    | i+1, p => do
       let q : n-(i+1) < n := Nat.sub_lt (add_le_implies_le_rhs i p) (Nat.zero_lt_succ _)
       f ⟨n-(i+1), q⟩; loop i (Nat.le_of_succ_le p)
  loop n Nat.le.refl

@[extern "open_fd_write"]
constant openByFd : UInt32 → IO IO.FS.Handle

@[extern "lean_randombytes_init"]
constant randombytesInit : @&(ByteVec 48) → IO Unit

@[extern "lean_randombytes"]
constant randombytes (n:@&Nat) : IO (ByteVec n)

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

def mkCryptoKemKeypair (iseed : ByteVec 48) (attempts: optParam Nat 10) : IO KeyPair := do
  let rec loop : ∀(seed: ByteVec 33) (attempts:Nat), Option KeyPair
      | _, 0 => none        
      | seed, Nat.succ n => do
        match tryCryptoKemKeypair seed with
        | ⟨some kp, _⟩ => some kp
        | ⟨none, seed'⟩ => loop seed' n
  randombytesInit iseed
  match loop (#v[64] ++ (← randombytes 32)) attempts with
  | none => throw (IO.userError "Key generation failed")
  | some p => p

structure EncryptionResult where
  ss : Plaintext
  ct : Ciphertext

@[extern "lean_crypto_enc"]
constant mkCryptoEnc : @&PublicKey 
                     → IO (ByteVec synd_bytes × ByteVec (N / 8))

def mkCryptoKemEnc (pk:PublicKey) : IO EncryptionResult := do
  let (c, e) ← mkCryptoEnc pk
  let c   := c ++ cryptoHash32b (#b[2] ++ e)
  let key := cryptoHash32b $ #b[1] ++ e ++ c
  pure ⟨key, c⟩

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
  let m : UInt16 := UInt16.ofNat $ UInt8.toNat (ret_decrypt ||| ret_confirm)
  let m := m - 1
  let m := UInt8.ofNat $ UInt16.toNat (m >>> 8)

  -- Generate preimage
  let s := sk.extract (40 + irr_bytes + cond_bytes) (40 + irr_bytes + cond_bytes + N/8)
  let preimageX : ByteVec (N/8) := ~~~m &&& s
  let preimageY : ByteVec (N/8) := m &&& (e.extract 0 (N/8))
  let preimage := preimageX ||| preimageY
  pure $ cryptoHash32b $ #b[m &&& 1] ++ preimage ++ c

end Mceliece348864Ref