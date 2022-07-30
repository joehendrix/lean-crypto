import Mathlib.Data.List.Basic
import Mathlib.Data.List.Perm

/-! Nat -/

lemma Nat.sub_lt_of_lt {n m k : Nat} (h : n < m) : n - k < m :=
  lt_of_le_of_lt (sub_le n k) h

/-! Bitwise operations on Nat -/

theorem Bool.beq_symm (a b : Bool) : (a == b) = (b == a) := by
  cases a <;> cases b <;> rfl

theorem Bool.bne_symm (a b : Bool) : (a != b) = (b != a) := by
  simp [beq_symm, bne]

namespace Nat

theorem div_two_lt_self_of_ne_zero (hNe : n ≠ 0) : n / 2 < n :=
  Nat.div_lt_self (Nat.zero_lt_of_ne_zero hNe) (Nat.lt_succ_self _)

theorem bitwise_comm_of_comm (f : Bool → Bool → Bool) (hComm : ∀ x y, f x y = f y x) {a b : Nat}
    : bitwise f a b = bitwise f b a := by
  induction a using Nat.strongInductionOn generalizing b with
  | ind a ih =>
    unfold bitwise
    cases (inferInstance : Decidable (a = 0)) with
    | isTrue hEq => cases b <;> simp [hEq, hComm]
    | isFalse hNe =>
      have := div_two_lt_self_of_ne_zero hNe
      simp [ih (a / 2) this, hNe, hComm]

@[simp] theorem bitwise_bne_eq (a b : Nat) : bitwise bne a b = a ^^^ b := by rfl

@[simp] theorem zero_xor (n : Nat) : 0 ^^^ n = n := by rfl
@[simp] theorem xor_zero (n : Nat) : n ^^^ 0 = n := by cases n <;> rfl

@[simp] theorem xor_self (n : Nat) : n ^^^ n = 0 := by
  induction n using Nat.strongInductionOn with
  | ind n ih =>
    cases (inferInstance : Decidable (n = 0)) with
    | isTrue hEq => simp [hEq]
    | isFalse hNe =>
      show bitwise bne n n = 0
      unfold bitwise
      simp (config := {zeta := false}) only [bitwise_bne_eq]
      have := div_two_lt_self_of_ne_zero hNe
      simp [ih (n / 2) this, hNe]

theorem xor_comm (a b : Nat) : a ^^^ b = b ^^^ a :=
  bitwise_comm_of_comm bne (Bool.bne_symm)

@[simp] theorem zero_shr : 0 >>> n = 0 := sorry
@[simp] theorem shr_zero : n >>> 0 = n := rfl
@[simp] theorem shr_add (n k l : Nat) : n >>> k >>> l = n >>> (k + l) := sorry

-- TODO(WN): @[csimp] would be nice
theorem mul_two_pow_eq_shiftLeft (n k : Nat) : n * (2 ^ k) = n <<< k := by
  induction k generalizing n with
  | zero =>
    show n * 1 = n
    rw [Nat.mul_one]
  | succ k ih =>
    show n * (2^k * 2) = (2*n) <<< k
    -- ac_refl :'(
    simp [← ih, Nat.mul_assoc, Nat.mul_comm]

-- @[csimp]
theorem div_two_pow_eq_shiftRight (n k : Nat) : n / (2 ^ k) = n >>> k := by
  induction k generalizing n with
  | zero =>
    show n / 1 = n
    rw [Nat.div_one]
  | succ k ih =>
    show n / (2^k * 2) = (n >>> k) / 2
    simp [← ih, Nat.div_div_eq_div_mul]

end Nat

/-! Permutations -/

theorem List.perm_append_singleton {a : α} {l : List α} : l ++ [a] ~ a :: l := by
  suffices l ++ [a] ~ a :: (l ++ []) by
    rw [List.append_nil] at this
    assumption
  apply perm_middle

theorem List.perm_reverse {l : List α} : l.reverse ~ l := by
  induction l with
  | nil => exact .refl []
  | cons x xs ih =>
    rw [reverse_cons]
    apply Perm.trans (l₂ := x :: reverse xs)
    . apply perm_append_singleton
    . exact .cons x ih

/-! Alternative List.range. Not such a great model so probably don't PR -/

def List.rangeModel : Nat → List Nat
  | 0   => [] 
  | n+1 => rangeModel n ++ [n]

@[csimp]
theorem List.rangeModel_eq_range : @rangeModel = @range :=
  have aux (n : Nat) (r : List Nat) : rangeAux n r = rangeModel n ++ r := by
    induction n generalizing r with
    | zero => simp [rangeModel]
    | succ n ih => simp [rangeModel, ih, append_assoc]
  funext fun n => by simp [range, aux]

theorem List.lt_of_mem_rangeModel : ∀ { i : Nat }, i ∈ rangeModel n → i < n := by
  induction n with
  | zero =>
    intro _ h
    cases h
  | succ n ih =>
    rw [rangeModel, forall_mem_append]
    apply And.intro
    . intro _ h
      exact Nat.lt_succ_of_lt <| ih h
    . rw [forall_mem_singleton]
      exact Nat.lt.base n

theorem List.rangeModel_succ {n : Nat} : rangeModel (n+1) = rangeModel n ++ [n] := rfl

/-! List lemmas -/

@[simp] theorem List.getD_cons : List.getD (x :: xs) i d = if i = 0 then x else List.getD xs (i-1) d :=
  sorry

lemma List.foldl_ext (f g : α → β → α) (a : α)
  {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
  l.foldl f a = l.foldl g a :=
by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    unfold foldl
    rw [ih (f a x) (fun a b hB => H a b <| mem_cons_of_mem x hB), H a x <| mem_cons_self x xs]

-- by Mario
def List.withPred (P : α → Prop) : (as : List α) → (h : (a : α) → a ∈ as → P a) → List { x : α // P x }
  | [], _ => []
  | a :: as', h => ⟨a, h a (.head ..)⟩ :: withPred P as' fun a h' => h a (.tail _ h')

def List.withMems (l : List α) : List { x : α // x ∈ l } :=
  withPred (· ∈ l) l fun _ => id

def List.mapMems (l : List α) (f : (x : α) → x ∈ l → β) : List β :=
  go l (fun _ => id)
where go : (l' : List α) → (∀ x ∈ l', x ∈ l) → List β
  | [],    _ => []
  | a::as, H =>
    have hA : a ∈ l := H a <| mem_cons_self _ _
    have hAs : ∀ x ∈ as, x ∈ l := forall_mem_of_forall_mem_cons H
    f a hA :: go as hAs

@[specialize]
def List.foldlMems {α β} (l : List β) (f : α → (x : β) → x ∈ l → α) (init : α) : α :=
  go init l (fun _ => id)
where go (acc : α) : (l' : List β) → (∀ x ∈ l', x ∈ l) → α
  | nil,   _ => acc
  | b::bs, H =>
    have hB : b ∈ l := H b <| mem_cons_self _ _
    have hBs : ∀ x ∈ bs, x ∈ l := forall_mem_of_forall_mem_cons H
    go (f acc b hB) bs hBs

theorem List.foldl_eq_of_comm_of_perm {l₁ l₂ : List β} (f : α → β → α) (init : α) (H : ∀ a b₁ b₂, f (f a b₁) b₂ = f (f a b₂) b₁)
    (p : l₁ ~ l₂) : l₁.foldl f init = l₂.foldl f init :=
  by induction p generalizing init with
  | nil => rfl
  | cons _ _ ih => simp [foldl, ih]
  | swap => simp [foldl, H]
  | trans _ _ ih₁ ih₂ => simp [ih₁, ih₂]

@[simp]
theorem List.foldl_append (f : α → β → α) :
    ∀ (a : α) (l₁ l₂ : List β), foldl f a (l₁ ++ l₂) = foldl f (foldl f a l₁) l₂
  | a, []     , l₂ => rfl
  | a, (b::l₁), l₂ => by simp [cons_append, foldl, foldl_append f (f a b) l₁ l₂]

/-! Fin and Fin ranges -/

theorem Fin.induction {n : ℕ}
    {motive : Fin (n + 1) → Sort u} 
    (zero : motive ⟨0, Nat.zero_lt_succ _⟩)
    (succ : ∀ (i : Fin n), motive ⟨i, Nat.lt_succ_of_lt i.isLt⟩ → motive i.succ) 
    (i : Fin (n + 1)) : motive i := by
  let ⟨i, h⟩ := i
  induction i with
  | zero => exact zero
  | succ i ih => exact succ ⟨i, Nat.lt_of_succ_lt_succ h⟩ (ih _)

def List.rangeFinUpTo (n : Nat) : (m : Nat) → m ≤ n → List (Fin n)
  | 0,   _ => []
  | m+1, h => rangeFinUpTo n m (Nat.le_of_succ_le h) ++ [⟨m, Nat.lt_of_succ_le h⟩]

def List.rangeFin (n : Nat) : List (Fin n) :=
  rangeFinUpTo n n (Nat.le_refl _)

@[simp]
theorem List.rangeFinUpTo_length (n m : Nat) (h : m ≤ n) : (rangeFinUpTo n m h).length = m :=
  by induction m with
  | zero => rfl
  | succ m ih =>
    rw [rangeFinUpTo, length_append, length_singleton, ih (Nat.le_of_succ_le h)]

@[simp]
theorem List.rangeFin_length (n : Nat) : (rangeFin n).length = n :=
  by simp [rangeFin]

theorem List.rangeFinUpTo_complete (m : Nat) (i : Fin m) (h : m ≤ n)
    : ⟨i, Nat.lt_of_lt_of_le i.isLt h⟩ ∈ (rangeFinUpTo n m h) :=
  by induction m with
  | zero => exact i.elim0
  | succ m ih =>
    cases (inferInstance : Decidable <| i.val = m) with
    | isTrue hEq => simp [rangeFinUpTo, hEq]
    | isFalse hNeq => 
      let i' : Fin m := ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) hNeq⟩
      simp [rangeFinUpTo, ih i' (Nat.le_of_succ_le h)]

theorem List.rangeFin_complete (n : Nat) (i : Fin n) : i ∈ rangeFin n :=
  rangeFinUpTo_complete n i (Nat.le_refl _)

/-! Pointwise decidable, bounded universals can be decided by looping over their domain -/

-- defns from tests/bench/states35

class Enumerable (α : Type u) where
  elems    : List α
  complete : ∀ a : α, a ∈ elems

instance : Enumerable (Fin n) where
  elems := List.rangeFin n
  complete i := List.rangeFin_complete _ i

def List.allTrue (p : α → Prop) [(a : α) → Decidable (p a)] : List α → Bool
  | [] => true
  | a :: as => p a && allTrue p as

theorem List.of_allTrue [(a : α) → Decidable (p a)] (hc : allTrue p as) (hin : a ∈ as) : p a := by
  induction as with
  | nil => contradiction
  | cons b bs ih =>
    cases hin with simp [allTrue] at hc
    | head => simp [*]
    | tail _ h => exact ih hc.2 h

theorem List.allTrue_of_forall [(a : α) → Decidable (p a)] (h : ∀ a, p a) : allTrue p as := by
  induction as <;> simp [allTrue, *]

instance [Enumerable α] (p : α → Prop) [(a : α) → Decidable (p a)] : Decidable (∀ a, p a) :=
  have : List.allTrue p Enumerable.elems → (a : α) → p a :=
    fun h a => List.of_allTrue h (Enumerable.complete a)
  decidable_of_decidable_of_iff (Iff.intro this List.allTrue_of_forall)
