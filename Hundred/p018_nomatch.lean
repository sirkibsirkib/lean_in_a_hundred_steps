import Hundred.p001_inductive_types
import Hundred.p015_constructor_functions

/-
`nomatch <term>` is like `match ... with`, but
specifically for -- and needed when -- there are
exactly zero cases to match.
(Rocq is more uniform in just doing `match _ with ... end` either way).

Aside from the special syntax, the game is the same:
  the cases must be exhaustive, and all cases must have the same type!
-/
example: Nothing → ℕ :=
  λ (_impossible: Nothing) ↦ nomatch _impossible
