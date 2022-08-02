import Crypto.Fin

theorem ite_same {α:Type} (p:Prop) [h:Decidable p] (a:α) : (if p then a else a) = a := by
  cases h with
  | isFalse q =>
     simp only [q]
     trivial
  | isTrue q =>
    simp only [q]
    trivial

namespace Array

theorem size_mkEmpty {α: Type _} (n:Nat) : size (mkEmpty n : Array α) = 0 := rfl

def generate (n:Nat) (f : Fin n → α) : Array α :=
  foreachFin n (λi a => a.push (f i)) (mkEmpty n)

theorem size_generate {α} (n:Nat) (f:Fin n → α) : (generate n f).size = n := by
  simp only [generate, foreachFin]
  have h : ∀(i:Nat) (p:i ≤ n) (a:Array α),
             size (foreachFin.loop n (fun i a => push a (f i)) i p a) = a.size + i
              := by
    intro i p
    induction i with
    | zero =>
      intro a
      simp only [foreachFin.loop]
      trivial
    | succ i h =>
      intro a
      simp only [foreachFin.loop, h, size_push]
      simp only [Nat.succ_add]
      trivial
  apply Eq.trans (h _ _ _)
  simp only [size_mkEmpty, Nat.zero_add]

theorem size_append {α:Type} : ∀(x y:Array α), (x ++ y).size = x.size + y.size
| a, b => by
  simp only [HAppend.hAppend, Append.append, Array.append]
  simp only [foldl, foldlM]
  simp
  have h : ∀{j k:Nat} (_ : j+k = b.size) (r:Array α) (p: b.size ≤ b.size),
            size (Id.run (foldlM.loop (fun r v => push r v) b b.size p j k r))
              = r.size + j := by
    intro j k q r p
    revert k q r
    induction j with
    | zero =>
      intro k q r
      unfold foldlM.loop
      have not_q : ¬(k < b.size) := by
        rw [q.symm]
        simp [ Nat.lt_irrefl]
      simp [not_q]
      trivial
    | succ j ind =>
      intro k q r
      unfold foldlM.loop
      have is_lt : k < b.size := by
        rw [Nat.add_comm] at q
        exact Nat.eq_add_implies_lt q
      simp [is_lt]
      apply Eq.trans
      have q_ind : j + (k + 1) = size b := by
        simp only [Nat.succ_add] at q
        exact q
      apply ind q_ind
      simp only [size_push]
      simp only [Nat.succ_add]
      trivial
  apply h
  trivial

@[simp]
theorem size_ofSubarray {α:Type} (s:Subarray α) : (ofSubarray s).size = s.stop - s.start := sorry

@[simp]
theorem start_toSubarray {α:Type} (a:Array α) (start stop : Nat) (p : start ≤ stop) (q : stop ≤ a.size)
  : (toSubarray a start stop).start = start := by simp [toSubarray, p, q]

@[simp]
theorem start_toSubarray_large {α:Type} (a:Array α) (start stop : Nat) (p : a.size ≤ start) (q : a.size ≤ stop)
  : (toSubarray a start stop).start = a.size := by
    simp only [toSubarray]
    cases Decidable.em (stop ≤ size a) with
    | inl g =>
      simp [g]
      cases Decidable.em (start ≤ stop) with
      | inl h =>
        simp [h]
        have r : start ≤ size a := Nat.le_trans h g
        exact (Nat.le_antisymm r p)
      | inr h =>
        simp [h]
        exact (Nat.le_antisymm g q)
    | inr g =>
      simp [g]
      cases Decidable.em (start ≤ a.size) with
      | inl h =>
        simp [h]
        exact (Nat.le_antisymm h p)
      | inr h =>
        simp [h]

theorem stop_toSubarray_large {α:Type} (a:Array α) (start stop : Nat) (_ : a.size ≤ start) (q : a.size ≤ stop)
  : (toSubarray a start stop).stop = a.size := by
    simp only [toSubarray]
    cases Decidable.em (stop ≤ size a) with
    | inl g =>
      simp [g]
      cases Decidable.em (start ≤ stop) with
      | inl h =>
        simp [h]
        exact (Nat.le_antisymm g q)
      | inr h =>
        simp [h]
        exact (Nat.le_antisymm g q)
    | inr g =>
      simp [g]
      cases Decidable.em (start ≤ a.size) with
      | inl h => simp [h]
      | inr h => simp [h]

@[simp]
theorem stop_toSubarray {α:Type} (a:Array α) (start stop : Nat) (p : start ≤ stop) (q : stop ≤ a.size)
  : (toSubarray a start stop).stop = stop := by simp [toSubarray, p, q]

theorem size_empty {α:Type _} : Array.size (#[] : Array α) = 0 := by rfl

@[simp]
theorem size_extract {α:Type} (src: Array α) (start stop : Nat)
: (src.extract start stop).size = min stop src.size - start := by
  simp [extract, toSubarray]
  cases Decidable.em (stop ≤ size src) with
  | inl g =>
    simp [g, min]
    cases Decidable.em (start ≤ stop) with
    | inl h => simp [h]
    | inr h =>
      have q := Nat.gt_of_not_le h
      simp [h, Nat.sub_self, Nat.lt_implies_zero_sub q]
  | inr g =>
    simp [g, min]
    cases Decidable.em (start ≤ size src) with
    | inl h =>
      simp [h]
    | inr h =>
      have q := Nat.gt_of_not_le h
      simp [h, Nat.sub_self, Nat.lt_implies_zero_sub q]

theorem extract_all (a:Array α)
  : (a.extract 0 a.size) = a := by
    admit

theorem extract_end_empty {a:Array α} {i : Nat} (p : i ≥ a.size) (j : Nat)
  :(a.extract i j) = Array.empty := by
    admit


theorem append_empty {α} (a:Array α) : a ++ empty = a := by
  admit

theorem append_data {α} (a b:Array α) : (a ++ b).data = a.data ++ b.data := by
  admit

theorem size_qsort {α} [Inhabited α] (a:Array α) (lt : α → α → Bool)
  : Array.size (Array.qsort a lt) = a.size := by
  admit

@[simp]
theorem size_setD (a:Array α) : (a.setD i e).size = a.size := by
  simp only [setD]
  cases Decidable.em (i < a.size) with
    | inl h => simp [h]
    | inr h => simp [h]

theorem size_set! (a:Array α) : (a.set! i e).size = a.size := by
  simp [set!, size_setD]

end Array
