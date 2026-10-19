theorem mem_of_list {α : Type} [DecidableEq α] (a : α) (l : List α) : a ∈ l → a ∈ l := by
  intro h
  exact h

theorem list_length_pos {α : Type} (l : List α) (h : 0 < l.length) : 0 < l.length := by
  exact h

def list_contains {α : Type} [DecidableEq α] (a : α) (l : List α) : Bool :=
  if a ∈ l then true else false