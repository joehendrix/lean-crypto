namespace ByteArray

theorem eq_of_val_eq : ∀ {x y : ByteArray}, Eq x.data.data y.data.data → Eq x y
  | ⟨⟨x⟩⟩, _, rfl => rfl

theorem val_eq_of_eq {i j : ByteArray} (h : Eq i j) : Eq i.data.data j.data.data :=
  h ▸ rfl

theorem ne_of_val_ne {i j : ByteArray} (h : Not (Eq i.data.data j.data.data)) : Not (Eq i j) :=
  λh' => absurd (val_eq_of_eq h') h

@[extern "lean_bytearray_decide_eq"]
def decideEq : (a b : ByteArray) → Decidable (Eq a b) :=
  fun i j =>
    match decEq i.data.data j.data.data with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

instance : DecidableEq ByteArray := decideEq

end ByteArray

structure ByteBuffer where
  data : ByteArray
  deriving DecidableEq

namespace ByteBuffer

def digitChar (n : UInt8) : Char :=
  if n = 0 then '0' else
  if n = 1 then '1' else
  if n = 2 then '2' else
  if n = 3 then '3' else
  if n = 4 then '4' else
  if n = 5 then '5' else
  if n = 6 then '6' else
  if n = 7 then '7' else
  if n = 8 then '8' else
  if n = 9 then '9' else
  if n = 0xa then 'A' else
  if n = 0xb then 'B' else
  if n = 0xc then 'C' else
  if n = 0xd then 'D' else
  if n = 0xe then 'E' else
  if n = 0xf then 'F' else
  '*'


def toHexDigit (c : UInt8) : String :=
  String.singleton (digitChar (c / 16)) ++ String.singleton (digitChar (c % 16))

--protected def toString (a:ByteBuffer) : String := ""

protected def toString (a:ByteBuffer) : String := 
  a.data.foldl (λs b => s ++ toHexDigit b) ""

instance : ToString ByteBuffer := ⟨ByteBuffer.toString⟩ 

end ByteBuffer

@[extern "open_fd_write"]
constant openByFd : UInt32 → IO IO.FS.Handle

@[extern "init_seed"]
constant initSeed : @&Unit → Array ByteBuffer

namespace Mceliece348864Ref
def name : String := "mceliece348864"
def publicKeyBytes : Nat := 261120
def secretKeyBytes : Nat := 6492

end Mceliece348864Ref

structure KeyPair where
  pk : ByteBuffer
  sk : ByteBuffer

@[extern "lean_crypto_kem_keypair"]
constant mkCryptoKemKeypair : @&ByteBuffer → IO KeyPair

structure EncryptionResult where
  ss : ByteBuffer
  ct : ByteBuffer

@[extern "lean_crypto_kem_enc"]
constant mkCryptoKemEnc : @&ByteBuffer → IO EncryptionResult

@[extern "lean_crypto_kem_dec"]
constant cryptoKemDec (ct sk : @&ByteBuffer) : IO ByteBuffer