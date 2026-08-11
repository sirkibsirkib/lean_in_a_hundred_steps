import Hundred.p026_structural_recursion
import Hundred.p047_predicates_and_relations
import Hundred.p054_subtype

/-
`congr` (congruence) proves `f x = g y`
given `f = g` and `x = y`.
Or you could say it transforms the former
goal into the latter two subgoals.
-/
#check congr

-- We can use this get inside the binding `n`
-- of this equality of subtypes.
-- (which we can also prove later).
theorem Even_vs_Odd_subtype:
  Even = Not ∘ Odd →
  Evenℕ = { n // ¬ Odd n }
:= by
  intro h
  unfold Evenℕ
  -- desugar the `{ ... }` notation to reveal outer `Subtype`
  change _ = Subtype (Not ∘ Odd)
  -- goal: `Subtype Even = Subtype (Not ∘ Odd)`
  apply congr
  . rfl     -- `Subtype = Subtype`
  . exact h -- `Even = Not ∘ Odd`

-- The `congr` tactic applies the `congr` function
-- (and does some extra steps to try close the goal).
theorem Even_vs_Odd_subtype':
  Even = Not ∘ Odd →
  Evenℕ = { n // ¬ Odd n }
:= by
  intro h
  unfold Evenℕ
  -- desugar the `{ ... }` notation to reveal outer `Subtype`
  change _ = Subtype (Not ∘ Odd)
  -- goal: `Subtype f = Subtype g`
  congr
  -- goal `Subtype = Subtype` closed automatically

/-
You can see that `cong` functions and tactics
boil down to applying a mix of `Eq` methods.

Also, you may also spot that they use `▸`, a standard macro
for transforming `f x` to `f y` given `x = y` or `y = x`.
-/
#print congr
#print Even_vs_Odd_subtype
#print Even_vs_Odd_subtype'
