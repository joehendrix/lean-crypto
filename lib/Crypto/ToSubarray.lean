syntax:max term noWs "[[" term ":" term "]]" : term
syntax:max term noWs "[[" term ":" "]]" : term
syntax:max term noWs "[[" ":" term "]]" : term

class ToSubarray (collection : Type u) (subarray : outParam (Type u)) : Type u where
  size : collection → Nat
  toSubarray (as : collection) (start : Nat := 0) (stop : Nat := size as) : subarray  

export ToSubarray (size)
export ToSubarray (toSubarray)

macro_rules
  | `($a[[$start : $stop]]) => `(toSubarray $a $start $stop)
  | `($a[[ : $stop]])       => `(toSubarray $a 0 $stop)
  | `($a[[$start : ]])      => `(toSubarray a $start a.size)