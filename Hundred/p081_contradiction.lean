import Hundred.p047_predicates_and_relations
open ℕ

/-
The `contradiction` tactic closes a proof with any `p` and `¬ p` in context.
-/
example: ∀n, Odd n → ¬ Odd n → Even n := by
  intro n ho hno
  contradiction
