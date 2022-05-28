import Crypto.Nat

@[inline] def forFinM {m} [Monad m] (n : Nat) (f : Fin n → m Unit) : m Unit :=
  let rec @[specialize] loop : ∀ (i:Nat), (p : i ≤ n) → m Unit 
    | 0, p => pure ()
    | i+1, p => do
       let q : n-(i+1) < n := Nat.sub_lt (Nat.add_le_implies_le_rhs i p) (Nat.zero_lt_succ _)
       f ⟨n-(i+1), q⟩; loop i (Nat.le_of_succ_le p)
  loop n Nat.le.refl

@[inline] def foreachFin (n : Nat) (f : Fin n → α → α) (a:α) : α :=
  let rec @[specialize] loop : ∀ (i:Nat), (p : i ≤ n) → α → α
    | 0, p, a => a
    | i+1, p, a =>
       let q : n-(i+1) < n := Nat.sub_lt (Nat.add_le_implies_le_rhs i p) (Nat.zero_lt_succ _)
       loop i (Nat.le_of_succ_le p) (f ⟨n-(i+1), q⟩ a)
  loop n Nat.le.refl a
