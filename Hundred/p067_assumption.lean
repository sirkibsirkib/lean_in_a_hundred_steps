import Hundred.p047_predicates_and_relations

/-
The `assumption` tactic completes the proof
with the first term in context matching the goal.

This is especially handy because even _unnamed_
premises (function arguments) in the context are suitable.

This proof is nice and maintainable; it avoids ever naming the input proposition
-/
example: Prop → Prop := by
  intro _
  assumption
