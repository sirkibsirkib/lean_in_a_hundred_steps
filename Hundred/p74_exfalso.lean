import Hundred.p45_predicates_and_relations
import Hundred.p68_induction

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

/-
Let's see a more realistic proof where `exfalso`
is used in a particular case.
-/

theorem even_iff_not_odd:
  ∀ n, Even n ↔ ¬ Odd n
:= by
  intro n
  induction n
  . constructor
    . intro _ oz
      cases oz
    . intro _
      exact Even.zero
  . case succ n ih =>
    constructor
    . intro e' o'
      cases o'
      cases e'
      rename_i e o
      exact ih.1 e o
    . intro no'
      have eo := even_or_odd n
      cases eo
      . next e =>
        /-
        Here `no'` and `e` are contradictory!
        The goal no longer matters.
        -/
        exfalso
        -- Now `no'` is applicable because it is of the form `_ → False`!
        apply no'
        exact Odd.succ n e
      . next o =>
        exact Even.succ n o
