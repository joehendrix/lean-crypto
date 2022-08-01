-- Defines a type class and notation for a Hadamard product

-- A Hadamard product is an "elementwise" product for a structure.
class HadamardProduct (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hadProd : α → β → γ

-- The Hadamard product notation can be typed with "\odot".
-- See [1] for a discussion on why this notation was chosen.
-- [1] https://math.stackexchange.com/questions/20412/element-wise-or-pointwise-operations-notation/601545#601545
infixl:70 " ⊙ "   => HadamardProduct.hadProd