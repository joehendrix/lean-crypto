import Crypto.ByteBuffer
import Crypto.ByteVec
import Crypto.UInt8

def ByteVec.toBuffer {n:Nat} : ByteVec n → ByteBuffer
| ⟨a,_⟩ => ⟨a⟩ 

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

namespace Mceliece348864Ref
def name : String := "mceliece348864"
def publicKeyBytes : Nat := 261120
def secretKeyBytes : Nat := 6492

def plaintextBytes : Nat := 32
def ciphertextBytes : Nat := 128 

def N := 3488

def gfbits : Nat := 12
def sys_t : Nat := 64
def pk_nrows : Nat := sys_t * gfbits

def synd_bytes : Nat := ((pk_nrows + 7)/8)

def PublicKey := ByteVec Mceliece348864Ref.publicKeyBytes
  deriving ToString

def SecretKey := ByteVec Mceliece348864Ref.secretKeyBytes
  deriving ToString

def Plaintext := ByteVec Mceliece348864Ref.plaintextBytes
  deriving DecidableEq, ToString

def Ciphertext := ByteVec Mceliece348864Ref.ciphertextBytes
  deriving ToString

end Mceliece348864Ref

structure KeyPair where
  pk : Mceliece348864Ref.PublicKey
  sk : Mceliece348864Ref.SecretKey
  
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
  ss : Mceliece348864Ref.Plaintext
  ct : Mceliece348864Ref.Ciphertext

@[extern "lean_crypto_enc"]
constant mkCryptoEnc : @&Mceliece348864Ref.PublicKey 
                     → IO (ByteVec Mceliece348864Ref.synd_bytes × ByteVec (Mceliece348864Ref.N / 8))

@[extern "lean_crypto_hash_32b"]
constant cryptoHash32b : ByteBuffer → ByteVec 32

def mkCryptoKemEnc (pk:Mceliece348864Ref.PublicKey) : IO EncryptionResult := do
  let (c, e) ← mkCryptoEnc pk
  let c   := c ++ cryptoHash32b (#b[2] ++ e.toBuffer)
  let key := cryptoHash32b $ #b[1] ++ e.toBuffer ++ c.toBuffer
  pure ⟨key, c⟩
 
@[extern "lean_crypto_kem_dec"]
constant cryptoKemDec (ct : @&Mceliece348864Ref.Ciphertext) (sk : @&Mceliece348864Ref.SecretKey) : IO Mceliece348864Ref.Plaintext