import Hundred.p047_predicates_and_relations
import Hundred.p082_induction

/-
`exfalso` replaces the goal with `False`.
It is really just nice sugar for `apply False.elim`.
-/
#print False.elim

/-
`exfalso` signals nicely to the reader that
the context has contradictory premises.
As such, it often sets up the use of `contradiction`.
-/
example: ∀n, (Even ℕ.zero → False) → Even n → ¬ Even n → Odd n := by
  intro n f he hne
  exfalso
  apply f
  exact Even.zero

TODO more realistic ex falso
