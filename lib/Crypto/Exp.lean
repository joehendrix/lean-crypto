/--
This defines a commutative multiplicative monoid and
exponentation operation over the monoid.
-/


class CommMulMonoid (α : Type u) extends Mul α, OfNat α 1 where
  mul_assoc := ∀(x y z : α), (x * y) * z = x * (y * z)
  mul_comm  := ∀(x y : α), x * y = y * x
  mul_one := ∀(x : α), x * 1 = x

  sq : α → α := λx => mul x x
  sq_is_self_add : ∀(x : α), sq x = mul x x := by
    intro
    rfl

section

open Nat
private theorem exp_terminates : ∀n, n ≥ 2 → n / 2 < n
  | 2, _ => by decide
  | 3, _ => by decide
  | n+4, _ => by
    rw [div_eq, if_pos]
    refine succ_lt_succ (Nat.lt_trans ?_ (lt_succ_self _))
    exact exp_terminates (n+2) (succ_lt_succ (zero_lt_succ _))
    exact ⟨by decide, succ_lt_succ (zero_lt_succ _)⟩

end

def exp' {α : Type u} [h: CommMulMonoid α] (r x : α) (n : Nat) : α :=
  if h : n ≥ 2 then
    let r := if n%2 = 1 then r * x else r
    exp' r (CommMulMonoid.sq x) (n / 2)
  else
    if n = 1 then x * r else r
decreasing_by exact exp_terminates _ ‹_›

def exp {α : Type u} [CommMulMonoid α] (x : α) (n : Nat) : α :=
  let _h : OfNat α 1 := CommMulMonoid.toOfNat
  exp' 1 x n