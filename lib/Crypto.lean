import Crypto.ByteArray
import Crypto.ByteVec
import Crypto.UInt8

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

structure ByteBuffer where
  data : ByteArray
  deriving DecidableEq

namespace ByteBuffer

protected def toString (a:ByteBuffer) : String := 
  a.data.foldl (λs b => s ++ b.toHex) ""

instance : ToString ByteBuffer := ⟨ByteBuffer.toString⟩ 

end ByteBuffer

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


def PublicKey := ByteVec Mceliece348864Ref.publicKeyBytes
  deriving ToString

def SecretKey := ByteVec Mceliece348864Ref.secretKeyBytes
  deriving ToString

end Mceliece348864Ref

structure KeyPair where
  pk : Mceliece348864Ref.PublicKey
  sk : Mceliece348864Ref.SecretKey
  
@[extern "lean_try_crypto_kem_keypair"]
constant tryCryptoKemKeypair (seed: ByteVec 33) : Option KeyPair × ByteVec 33

def mkCryptoKemKeypairloop : ∀(seed: ByteVec 33) (attempts:Nat), IO KeyPair
| _, 0 =>
  throw (IO.userError "Key generation failed")
| seed, Nat.succ n => do
  match tryCryptoKemKeypair seed with
  | ⟨some kp, _⟩ => pure kp
  | ⟨none, seed'⟩ => mkCryptoKemKeypairloop seed' n

def mkCryptoKemKeypair (seed : ByteVec 48) (attempts: optParam Nat 10) : IO KeyPair := do
  randombytesInit seed
  let rseed ← randombytes 32
  mkCryptoKemKeypairloop (#v[64] ++ rseed) attempts

structure EncryptionResult where
  ss : ByteBuffer
  ct : ByteBuffer

@[extern "lean_crypto_kem_enc"]
constant mkCryptoKemEnc : @&Mceliece348864Ref.PublicKey → IO EncryptionResult

@[extern "lean_crypto_kem_dec"]
constant cryptoKemDec (ct : @&ByteBuffer) (sk : @&Mceliece348864Ref.SecretKey) : IO ByteBuffer