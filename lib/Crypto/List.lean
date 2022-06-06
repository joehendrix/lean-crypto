namespace List

protected
theorem concat_to_cons (a : List α) (b:α) (c : List α)
  : List.concat a b ++ c = a ++ b :: c := by
    admit

end List