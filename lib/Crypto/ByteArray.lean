import Crypto.Array
import Crypto.ByteArray.ByteSubarray
import Crypto.IsList
import Crypto.List
import Crypto.Nat

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
| ⟨a⟩, b => by simp only [ByteArray.size, ByteArray.push, Array.size_push]

theorem append_data : ∀(x y:ByteArray), (x ++ y).data = x.data ++ y.data
| ⟨a⟩, ⟨b⟩ => by
  simp [HAppend.hAppend, Append.append]
  simp [ByteArray.append, copySlice]
  have p : a.size + b.size ≥ a.size := Nat.le_add_right a.size b.size
  simp [size, Array.extract_all, Array.extract_end_empty p, Array.append_empty (a++b) ]
  trivial

theorem size_append : ∀(x y:ByteArray), (x ++ y).size = x.size + y.size := by
  intro x y
  simp only [size]
  have q := append_data x y
  simp only [HAppend.hAppend, Append.append] at q
  simp only [q]
  apply Array.size_append

@[inline, matchPattern]
protected def fromList (l : List UInt8) : ByteArray := { data := { data := l } }

instance : IsList ByteArray where
  element := UInt8
  fromList := ByteArray.fromList

theorem size_mkEmpty (n:Nat) : size (mkEmpty n) = 0 := rfl

theorem size_from_list : ∀(l:List UInt8), ByteArray.size (fromList l) = l.length := by
  simp [fromList, ByteArray.fromList, size]

def replicateAux : ByteArray → Nat → UInt8 → ByteArray
| a, 0, _ => a
| a, Nat.succ n, c => replicateAux (a.push c) n c

def replicateNoList (n:Nat) (c:UInt8) : ByteArray := replicateAux (ByteArray.mkEmpty n) n c

@[implementedBy replicateNoList]
def replicate (n:Nat) (c:UInt8) : ByteArray := fromList (List.replicate n c)

theorem replicateAuxAsList (a:ByteArray) (j: Nat) (c:UInt8)
    : replicateAux a j c = a ++ fromList (List.replicate j c) := by
  revert a
  induction j with
  | zero =>
    intro a
    apply ByteArray.eq_of_val_eq
    simp [replicateAux, append_data, Array.append_data, fromList, ByteArray.fromList]
  | succ n nh =>
    intro a
    apply ByteArray.eq_of_val_eq
    simp [replicateAux, nh, append_data, Array.append_data, fromList, ByteArray.fromList]
    simp [push, Array.push, List.concat_to_cons]

theorem replicateNoListCorrect (n: Nat) (c:UInt8)
    : replicateNoList n c = replicate n c := by
  simp [replicateNoList, replicateAuxAsList, replicate]
  apply ByteArray.eq_of_val_eq
  simp only [append_data, Array.append_data]
  trivial

theorem size_replicate (n:Nat) (c:UInt8) : (replicate n c).size = n := by
  simp [replicate, size, fromList, ByteArray.fromList]

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
  -- Reduce byte array theorem to array theorem
  simp only [extract, copySlice, size, empty, mkEmpty]
  -- Reduce array problem to arithmetic
  simp only [Array.size_append, Array.size_extract, Array.size_empty]
  -- Cleanup ite
  simp only [min, ite_same]
  -- Cleanup arithmetic
  simp only [Nat.zero_sub, Nat.zero_add, Nat.add_zero]
  cases Decidable.em (e ≤ a.size) with
  | inl h1 =>
    simp [h1]
    cases Decidable.em (s ≤ e) with
    | inl h2 =>
      have h3 : s + (e - s) ≤ a.size := by
              simp only [Nat.add_sub_of_le h2]
              exact h1
      simp [h3]
      simp only [Nat.add_sub_cancel_left]
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
  let q : a.size < n := Nat.eq_add_implies_lt p
  let r : (a.push (f ⟨a.size, q⟩)).size + j = n := by
        simp only [size_push, Nat.succ_add]
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

def generateMapAux {n:Nat} (f:Fin n → ByteArray) : ∀(a:ByteArray) (i j : Nat), i + j = n → ByteArray
| a, i, 0, p => a
| a, i, Nat.succ j, p =>
  have p2 : Nat.succ (j + i) = n := by
         simp [Nat.add_comm j i]
         exact p
  let q : i < n := Nat.add_le_implies_le_rhs j (Nat.le_of_eq p2)
  let r : Nat.succ i + j = n := by
    simp [Nat.succ_add]
    exact p
  generateMapAux f (a ++ (f ⟨i, q⟩)) i.succ j r

def generateMap (n:Nat) (f:Fin n → ByteArray) (limit := 0) : ByteArray :=
  generateMapAux f (mkEmpty limit) 0 n (Nat.zero_add n)

theorem size_generateMapAux_same {m n:Nat} (f:Fin n → ByteArray) (p : ∀(k:Fin n), (f k).size = m)
   (a:ByteArray) (i j:Nat) (h:i + j = n)

    : (generateMapAux f a i j h).size = a.size + m*j := by
  revert a i h
  induction j with
  | zero =>
    intros a i h
    simp [generateMapAux]
  | succ j ind =>
    intros a i h
    simp [generateMapAux]
    apply Eq.trans
    apply ind
    simp [size_append, p, Nat.mul_succ, Nat.add_assoc, Nat.add_comm m]

theorem size_generateMap_same (n:Nat) (f:Fin n → ByteArray) {m:Nat} (p : ∀(i:Fin n), (f i).size = m)
   : (generateMap n f).size = n*m := by
  simp [generateMap, size_generateMapAux_same f p]
  simp [size_mkEmpty]
  apply Nat.mul_comm

theorem size_set! (a : ByteArray) (i : Nat) (e : UInt8) : (a.set! i e).size = a.size := by
  simp only [set!, size, Array.size_set!]

end ByteArray