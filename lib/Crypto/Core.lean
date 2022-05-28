import Crypto.Vec

namespace Crypto

inductive Kind
| bit : Kind
| vec : Nat → Kind → Kind

export Kind(bit)
export Kind(vec)

namespace Kind

@[reducible]
def values : Kind → Type
| bit => Bool
| vec n k => Vec n k.values

instance : CoeSort Kind Type where
   coe := Kind.values

end Kind


class MonadRandom (m : Type → Type v) extends Monad m where
  mkRandom : ∀(k:Kind), m k.values
  -- Invoke when a random computation wants to give up because we have exceeded
  -- a bound on the number of tries.
  giveUp {α} : String → m α

export MonadRandom(mkRandom)
export MonadRandom(giveUp)

end Crypto