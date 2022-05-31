import Crypto.Array
import Crypto.IsList
import Crypto.ByteArray.ByteSubarray

namespace ByteArray

theorem eq_of_val_eq : ∀ {x y : ByteArray}, Eq x.data.data y.data.data → Eq x y
  | ⟨⟨x⟩⟩, _, rfl => rfl

theorem val_eq_of_eq {i j : ByteArray} (h : Eq i j) : Eq i.data.data j.data.data :=
  h ▸ rfl

theorem ne_of_val_ne {i j : ByteArray} (h : Not (Eq i.data.data j.data.data)) : Not (Eq i j) :=
  λh' => absurd (val_eq_of_eq h') h

@[extern "lean_byte_array_decide_eq"]
def decideEq : (a b : ByteArray) → Decidable (Eq a b) :=
  fun i j =>
    match decEq i.data.data j.data.data with
    | isTrue h  => isTrue (eq_of_val_eq h)
    | isFalse h => isFalse (ne_of_val_ne h)

instance : DecidableEq ByteArray := decideEq

theorem size_push : ∀(a:ByteArray) (b:UInt8), (a.push b).size = a.size + 1
| ⟨a⟩, b => by simp [ByteArray.size, ByteArray.push]

theorem size_append : ∀(x y:ByteArray), (x ++ y).size = x.size + y.size
| ⟨a⟩, ⟨b⟩ => by
  simp [HAppend.hAppend, Append.append, ByteArray.append]
  simp [copySlice, size]
  simp [Nat.le_implies_zero_sub, Nat.le_add_right]

@[inlineIfReduce]
def fromListAux : List UInt8 → ByteArray → ByteArray
  | [],       r => r
  | a :: as, r => fromListAux as (r.push a)

@[inline, matchPattern]
protected def fromList (as : List UInt8) : ByteArray :=
  fromListAux as (ByteArray.mkEmpty as.redLength)

instance : IsList ByteArray where
  element := UInt8
  fromList := ByteArray.fromList

/-
@[simp]
theorem size_empty : size empty = 0 := rfl

@[simp]
theorem data_empty : empty.data = #[] := rfl
-/

theorem size_mkEmpty (n:Nat) : size (mkEmpty n) = 0 := rfl

theorem size_fromListAux : ∀(l:List UInt8) (r:ByteArray), (fromListAux l r).size = r.size + l.length
| [] , r => rfl
| a :: as, r => by simp [fromListAux, size_fromListAux as _, Nat.add_succ, Nat.succ_add, size_push]

theorem size_from_list : ∀(l:List UInt8), ByteArray.size (fromList l) = l.length
| [] => rfl
| a :: as => by simp [fromList, IsList.fromList, ByteArray.fromList, size_fromListAux, size_mkEmpty]

def replicateAux : ByteArray → Nat → UInt8 → ByteArray
| a, 0, _ => a
| a, Nat.succ n, c => replicateAux (a.push c) n c

def replicate (n:Nat) (c:UInt8) : ByteArray := replicateAux (ByteArray.mkEmpty n) n c

theorem size_replicateAux (a:ByteArray) (n:Nat) (c:UInt8) : (replicateAux a n c).size = a.size + n := by
  revert a
  induction n with
  | zero =>
    intro a
    simp [replicateAux]
  | succ n nh =>
    intro a
    simp [replicateAux, nh, ByteArray.size_push, Nat.add_succ, Nat.succ_add]

theorem size_replicate (n:Nat) (c:UInt8) : (replicate n c).size = n := by
  simp [replicate, size_replicateAux, size_mkEmpty]

def sequenceAux : ByteArray → Nat → ByteArray
| a, 0 => a
| a, Nat.succ n => sequenceAux (a.push (UInt8.ofNat a.size)) n

-- Creates a vector [0..n)
def sequence (n:Nat) : ByteArray := sequenceAux (ByteArray.mkEmpty n) n

theorem size_sequenceAux (a:ByteArray) (n:Nat) : (sequenceAux a n).size = a.size + n := by
  revert a
  induction n with
  | zero =>
    intro a
    simp [sequenceAux]
  | succ n nh =>
    intro a
    simp [sequenceAux, nh, ByteArray.size_push, Nat.add_succ, Nat.succ_add]

theorem size_sequence (n:Nat) : (sequence n).size = n := by
  simp [sequence, size_sequenceAux, size_mkEmpty]

theorem size_extract : ∀(a:ByteArray) (s e : Nat), (a.extract s e).size = min e a.size - s
| ⟨a⟩, s, e => by
  simp [extract, copySlice, size, empty, mkEmpty, Array.size_empty, min]
  cases Decidable.em (e ≤ Array.size a) with
  | inl h1 =>
    cases Decidable.em (s ≤ e) with
    | inl h2 =>
      simp [h1, Nat.add_sub_of_le h2]
    | inr h2 =>
      have s3 := Nat.le_of_lt (Nat.gt_of_not_le h2)
      simp [h1, Nat.le_implies_zero_sub, s3]
      cases Decidable.em (s ≤ a.size) with
      | inl h3 =>
        simp [h3]
      | inr h3 =>
        have s3 := Nat.le_of_lt (Nat.gt_of_not_le h3)
        simp [Nat.le_implies_zero_sub, s3, h3]
  | inr h1 =>
    cases Decidable.em (s ≤ e) with
    | inl h2 =>
      simp [h1, Nat.add_sub_of_le h2]
    | inr h2 =>
      have n_le_s : e ≤ s := Nat.le_of_lt (Nat.gt_of_not_le h2)
      simp [h1, Nat.le_implies_zero_sub, n_le_s]
      cases Decidable.em (s ≤ a.size) with
      | inl h3 =>
        have h11 : a.size ≤ e := Nat.le_of_lt (Nat.gt_of_not_le h1)
        have h31 : a.size ≤ s := Nat.le_trans h11 n_le_s
        simp [h3, Nat.le_implies_zero_sub, h31]
      | inr h3 =>
        simp [h3]

def extractN (a:ByteArray) (s n : Nat) : ByteArray :=
  let b := a.extract s (s+n)
  b ++ replicate (n-b.size) 0

theorem size_extractN (a:ByteArray) (s n : Nat) : (a.extractN s n).size = n := by
  simp [extractN, size_append, size_extract, size_replicate, min]
  cases Decidable.em (s + n ≤ a.size) with
  | inl h1 =>
    simp [h1, Nat.add_sub_self_left]
  | inr h1 =>
    have h11 : a.size ≤ s+n := Nat.le_of_lt (Nat.gt_of_not_le h1)
    have p : a.size - s ≤ n := by
           apply Nat.le_sub_of_le_add
           rw [Nat.add_comm]
           exact h11
    have q := Nat.add_sub_of_le p
    simp [h1, q]


def generateAux {n:Nat} (f:Fin n → UInt8) : ∀(a:ByteArray) (j : Nat), a.size + j = n → ByteArray
| a, 0, p => a
| a, Nat.succ j, p =>
  let q : a.size < n := by
    apply Nat.add_le_implies_le_rhs j
    apply Nat.le_of_eq
    rw [Nat.add_comm]
    simp [Nat.succ_add]
    exact p
  let r : (a.push (f ⟨a.size, q⟩)).size + j = n := by
        simp [size_push, Nat.add_succ, Nat.succ_add]
        exact p
  generateAux f (a.push (f ⟨a.size, q⟩)) j r

def generate (n:Nat) (f:Fin n → UInt8) : ByteArray :=
  let p : (mkEmpty n).size + n = n := by simp [size_mkEmpty]
  generateAux f (mkEmpty n) n p

theorem size_generateAux {n:Nat} (f:Fin n → UInt8) {a:ByteArray} (j:Nat) (p:a.size + j = n)
    : (generateAux f a j p).size = n := by
  revert a p
  induction j with
  | zero =>
    intros a p
    exact p
  | succ j ind =>
    intros a p
    exact ind _

theorem size_generate (n:Nat) (f:Fin n → UInt8) : (generate n f).size = n := by
  exact (size_generateAux _ _ _)

end ByteArray