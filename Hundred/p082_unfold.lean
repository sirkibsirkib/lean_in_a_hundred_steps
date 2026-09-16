import Hundred.p016_matching
open ℕ

/-
The `unfold <name>` tactic simply rewrites
a name in the goal to its definition.
And `unfold <name> at <name'>` does the
same in a premise called `name'`.

Removing this tactic usually does not change proofs,
but it is a useful tool for massaging the context
to reveal what to do next!
-/

example: one = zero.succ := by
  unfold one
  rfl

example: pred one =
    (match one with
    | zero => zero
    | succ n => n) := by
  unfold pred
  rfl
