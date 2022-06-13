namespace Bool

protected def xor (x y : Bool) : Bool := if x then not y else y

instance : Xor Bool := ⟨Bool.xor⟩

end Bool