class IsList (α : Type) where
  element : Type
  fromList : List element → α

export IsList (fromList)
