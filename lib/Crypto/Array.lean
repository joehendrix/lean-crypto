import Crypto.Nat

namespace Array

@[simp]
theorem ite_same {α:Type} (p:Prop) [h:Decidable p] (a:α) : (if p then a else a) = a := by
  cases h with
  | isFalse q => simp [q]
  | isTrue q => simp [q]

theorem size_foldlM_loop {α:Type} (b:Array α) (stop:Nat) (h:stop ≤ b.size) (i j : Nat) (inv : i = stop - j) (a : Array α)
: size (Id.run (foldlM.loop (fun r v => push r v) b stop h i j a)) = a.size + i := by
  simp [Id.run, foldlM.loop]
  revert j a
  induction i with
  | zero => 
    intros j inv a
    simp [foldlM.loop]
    cases Decidable.em (j < stop) with
    | inl q => simp [q]
    | inr q => simp [q]
  | succ i ih => 
    intros j inv a
    simp [foldlM.loop]
    have q : j < stop := Nat.sub_pos_implies_lt inv
    have r : i = stop - (j + 1) := by 
      apply Nat.add_implies_sub q
      have q_leq : j ≤ stop := Nat.le_of_lt q
      have s : Nat.succ i + j = stop := Nat.sub_implies_add q_leq inv
      simp [Nat.succ_add] at s
      exact s
    simp [q, ih (j+1) r, Nat.succ_add, Nat.add_succ]      

@[simp]
theorem size_append {α:Type} : ∀(x y:Array α), (x ++ y).size = x.size + y.size
| a, b => by
  simp [HAppend.hAppend, Append.append, Array.append, Array.foldl]
  have h : size b ≤ size b := Nat.le.refl
  simp [foldlM, h, size_foldlM_loop]    

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

@[simp]
theorem stop_toSubarray_large {α:Type} (a:Array α) (start stop : Nat) (p : a.size ≤ start) (q : a.size ≤ stop)
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

theorem size_empty : Array.size (#[] : Array UInt8) = 0 := by rfl

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

end Array
