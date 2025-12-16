example : ∀ n a : Nat, ∃ k : Nat, k ∣ a^(2 * n + 1) + 1 := by grind

inductive Tree (α : Type) where
  | leaf (value : α) : Tree α
  | node (left right : Tree α) : Tree α
