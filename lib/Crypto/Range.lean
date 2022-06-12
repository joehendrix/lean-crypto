structure Range where
  base : Nat
  count : Nat

def range (l n:Nat) : Range := ⟨l, n⟩

def rangeH (l h:Nat) : Range := ⟨l, h-l⟩

namespace Range

protected
def forIn {β} {m} [Monad m] (x : Range) (b : β) (f : Nat → β → m (ForInStep β)) : m β :=
  let e := x.base + x.count
  let rec loop : Nat → β → m β
      | 0, b => pure b
      | Nat.succ n, b => do
        let r ← f (e - Nat.succ n) b
        match r with
        | ForInStep.done r => pure r
        | ForInStep.yield r => loop n r
  loop x.count b

instance {m: Type _ → Type _} [Monad m] : ForIn m Range Nat where
  forIn := Range.forIn

end Range