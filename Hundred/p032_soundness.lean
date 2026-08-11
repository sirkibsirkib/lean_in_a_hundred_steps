import Hundred.p030_propositions

/-
We call Lean (semantically) _sound_ while `False` has no proof.
But later we will see that `False` is endlessly useful
as the premise for contradictory proposions, for reasoning _ad absurdum_.

The following proves (vacuously) that if
`False` is true then `Nothing` has a value!
-/
example: False → Nothing :=
  λ (absurd: False) ↦ nomatch absurd

-- Lean helpfully provides the `False.elim` method
-- as a more readable form of the above.
example: False → Nothing := λ a ↦ a.elim
