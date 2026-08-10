import Hundred.p047_predicates_and_relations
import Hundred.p074_induction
import Hundred.p076_semicolon
open ℕ

/-
The `contradiction` tactic closes a proof with any `p` and `¬ p` in context.
-/
example: ∀n, Odd n → ¬ Odd n → Even n := by
  intro n ho hno
  contradiction

-- Here's a case where it comes up more naturally
theorem even_iff_not_odd: ∀ n, Even n ↔ Not (Odd n) := by
  intro n
  constructor
  . intro e o
    exact even_nand_odd n e o
  . intro no
    cases even_or_odd n
    . next => assumption
    . next o =>
      -- `Odd n` and `¬Odd n` at once!
      contradiction
