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

@[simp]
theorem size_push : ∀(a:ByteArray) (b:UInt8), (a.push b).size = a.size + 1
| ⟨a⟩, b => by simp [ByteArray.size, ByteArray.push]

@[simp]
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

@[simp]
theorem size_empty : size empty = 0 := rfl

@[simp]
theorem data_empty : empty.data = #[] := rfl

@[simp]
theorem size_mkEmpty (n:Nat) : size (mkEmpty n) = 0 := rfl

theorem size_fromListAux : ∀(l:List UInt8) (r:ByteArray), (fromListAux l r).size = r.size + l.length
| [] , r => rfl
| a :: as, r => by simp [fromListAux, size_fromListAux as _, Nat.add_succ, Nat.succ_add] 

@[simp]
theorem size_from_list : ∀(l:List UInt8), ByteArray.size (fromList l) = l.length
| [] => rfl
| a :: as => by simp [fromList, IsList.fromList, ByteArray.fromList, size_fromListAux] 

theorem size_extract : ∀(a:ByteArray) (s e : Nat), (a.extract s e).size = min e a.size - s
| ⟨a⟩, s, e => by
  simp [extract, copySlice]
  admit

end ByteArray