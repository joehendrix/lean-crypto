
namespace Nat

@[simp]
theorem zero_sub (x:Nat) : 0 - x = 0 := by
  induction x with
  | zero => rfl
  | succ x xh => simp [Nat.sub_succ, xh]

theorem sub_pos_implies_lt : ∀ {y x z : Nat}, succ z = x - y → y < x := by
  intro y
  induction y with
  | zero =>
    intros x z inv
    simp at inv
    simp [Eq.symm inv, zero_lt_succ]       
  | succ y yh =>
    intros x z inv
    cases x with
    | zero =>       
      simp at inv
    | succ x =>
      simp [Nat.succ_sub_succ] at inv
      exact Nat.succ_lt_succ (yh inv)

theorem sub_implies_add
: ∀ {y x z : Nat}, y ≥ z → x = y - z → x + z = y := by
  intro x y z
  revert x
  induction z with
  | zero =>
    simp 
    intros x p s
    exact s
  | succ z iz =>
    intros x p s
    cases x with
    | zero =>
      cases p
    | succ x =>
      simp [Nat.add_succ]
      apply iz (le_of_succ_le_succ p)
      simp [succ_sub_succ_eq_sub] at s
      exact s

theorem add_implies_sub
: ∀ {y x z : Nat}, y ≥ z → x + z = y → x = y - z := by
  intros x y z
  revert x
  induction z with
  | zero =>
    intros x p s
    exact s
  | succ z iz =>
    intros x p s
    cases x with
    | zero =>
      cases p
    | succ x =>
      simp [succ_sub_succ_eq_sub]
      apply iz (le_of_succ_le_succ p)
      simp [Nat.add_succ] at s
      exact s

end Nat