

class OfList (α : Type _) (β : outParam (Type _)) (C : outParam (List β → Prop)) where
  ofList : ∀(l:List β), C l → α

export OfList (ofList)

syntax "#v[" sepBy(term, ", ") "]" : term

macro_rules
  | `(#v[ $elems,* ]) => `(OfList.ofList [ $elems,* ] (by get_elem_tactic))
