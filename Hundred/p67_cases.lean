import Hundred.p01_inductive_types
import Hundred.p47_predicates_and_relations

/-
`cases n` is the tactic version of `match n with`.
This breaks the current goal into a set of sub-goals,
one per case of `n`.

There are several styles of proceeding with the sub-goals.

Style 1/3: case constructor patterns as with `match`.
The specifics differ a little bit. The constructor
is not namespaced in tactic mode for some reason?
-/
example: ℕ → ℕ := by
  intro n
  cases n
  case zero    => exact ℕ.zero
  case succ n' => exact n'

/-
Style 2/3: the following tactics are applied to the next unsolved subgoal.
This is the most concise but confusing unless there's one subgoal.

Here, the `cases Hconj` destructs the `XandY` the one way possible,
and then `assumption` proceeds with the first (and only) subgoal
-/
example: ∀ (X Y : Prop), X ∧ Y → X := by
  intro X Y XandY
  cases XandY
  assumption

/-
Style 3/3: focus on the next goal with ".", leaving case bindings inaccessible.

This is quite concise and useful if you are less interested in
using the hypothesis local to each case.
- sometimes the effects on other named hypotheses are enough.
- sometimes you can cherrypick the few hypotheses you need afterward
  via the `rename` tactic (see the next file).
-/
example: ℕ → Bit := by
  intro n
  cases n
  . /- where n is zero -/ exact Bit.yep
  . /- where n is the successor of some unnamed ℕ -/ exact Bit.nah


/-
In fact, `.` can first focus on the subgoal, and then
`case ... =>` can bind its specific parameters.
These are orthogonal and can work together!
This gives a 4th style which works just the 1st, but is perhaps prettier.
-/
example: ℕ → ℕ := by
  intro n
  cases n
  . case zero    => exact ℕ.zero
  . case succ n' => exact n'


-- `case _` can be replaced by `next`, if you want to avoid naming it.
example: ℕ → ℕ := by
  intro n
  cases n
  . next    => exact ℕ.zero
  . next n' => exact n'
