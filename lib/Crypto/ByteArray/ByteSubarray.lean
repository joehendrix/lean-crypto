import Crypto.ToSubarray

structure ByteSubarray where
  as : ByteArray
  start : Nat
  stop : Nat
  h₁ : start ≤ stop
  h₂ : stop ≤ as.size

namespace ByteSubarray

protected constant forIn {β : Type v} {m : Type v → Type w} [Monad m] (s : ByteSubarray) (b : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  let rec loop (n i : Nat) (p : i + n = s.stop) (b : β) : m β := do
    match n, p with
    | 0,   _ => pure b
    | n+1, p =>
      let q1 : i < s.stop := by
        admit
      let q : i < s.as.size := Nat.lt_of_lt_of_le q1 s.h₂
        -- linear arithmetic should solve.
      match (← f (s.as.get ⟨i, q⟩) b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop n (i+1) sorry b
  loop (s.stop - s.start) s.start sorry b

instance : ForIn m ByteSubarray UInt8 where
  forIn := ByteSubarray.forIn

instance : Stream ByteSubarray UInt8 where
  next? s :=
    if h : s.start < s.stop then
      have : s.start + 1 ≤ s.stop := Nat.succ_le_of_lt h
      some (s.as.get ⟨s.start, Nat.lt_of_lt_of_le h s.h₂⟩, { s with start := s.start + 1, h₁ := this })
    else
      none

end ByteSubarray

namespace ByteArray

def toSubarray (as : ByteArray) (start : Nat := 0) (stop : Nat := as.size) : ByteSubarray :=
  if h₂ : stop ≤ as.size then
     if h₁ : start ≤ stop then
       { as := as, start := start, stop := stop, h₁ := h₁, h₂ := h₂ }
     else
       { as := as, start := stop, stop := stop, h₁ := Nat.le_refl _, h₂ := h₂ }
  else
     if h₁ : start ≤ as.size then
       { as := as, start := start, stop := as.size, h₁ := h₁, h₂ := Nat.le_refl _ }
     else
       { as := as, start := as.size, stop := as.size, h₁ := Nat.le_refl _, h₂ := Nat.le_refl _ }

end ByteArray

instance : ToSubarray ByteArray ByteSubarray where
  size := ByteArray.size
  toSubarray := @ByteArray.toSubarray

instance : ToStream ByteArray ByteSubarray where
  toStream a := a[[:a.size]]