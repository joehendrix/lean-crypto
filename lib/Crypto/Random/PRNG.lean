import Crypto.ByteVec

-- A typeclass for a pseudo random number generator that
-- creates pseudo-random bytes.
class PRNG (α : Type) where
  randombytes (prng : α) (n : Nat) : ByteVec n × α
