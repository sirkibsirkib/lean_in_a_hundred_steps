import Hundred.p015_matching
import Hundred.p026_structural_recursion
import Hundred.p048_predicates_and_relations
import Hundred.p050_notation
import Hundred.p098_classical_axioms

/-
The `rw` ("rewrite") tactic lets you rewrite
(parts of) types using proofs of shape `x = y` or `x ↔ y`
in either direction.
-/

theorem odd_neven n: Odd n ↔ ¬ Even n := by
  apply Iff.intro
  . intro ho he
    exact even_nand_odd _ he ho
  . intro hne
    cases even_or_odd n
    . next he => contradiction
    . next ho => assumption

theorem even_nodd n: Even n ↔ ¬ Odd n := by
  apply Iff.intro
  . intro he ho
    exact even_nand_odd _ he ho
  . intro hno
    cases even_or_odd n
    . next he => assumption
    . next ho => contradiction

-- Here `Iff.mpr` projects the ↔ (called `odd_neven n`)
-- to its leftward component `Odd n ← ¬ Even`.
example: ∀n, ¬ Even n → Odd n := by
  intro n
  exact Iff.mpr (odd_neven n)

/-
Arguably, a more convenient way of doing this is a trivial case of rewrite.
We use `rw` to rewrite the goal from `Odd n` to `¬ Even n`
using `odd_neven n: Odd n → ¬ Even n` f
-/
example: ∀n, ¬ Even n → Odd n := by
  intro n _
  have f: Odd n ↔ ¬ Even n := odd_neven n
  rw [f]
  assumption

/-
`rw` is smart enough to fill in parameters like `n:ℕ`
based on what we are rewriting.
-/
example: ∀n, ¬ Even n → Odd n := by
  intro n _
  rw [odd_neven]
  assumption

/-
This showcases that the rewrite can transform _parts_
of what is being rewritten!
Here the `Odd n` term of the larger `¬Even n → Odd n` type is rewritten!
-/
example: ∀n, ¬ Even n → Odd n := by
  intro n
  -- goal: ¬Even n → Odd n
  rw [odd_neven]
  -- goal: ¬Even n → ¬Even
  intro _
  assumption

/-
Use `at <premise_name>` to apply the rewrite
to a premise in context, instead of the goal!

`rw [...] at _` is very helpful forward-reasoning:
building on top of (changing) premises to reach a (largely unchanging) goal.
-/
example: ∀n, Odd n → ¬ Even n := by
  intro n h
  rw [odd_neven] at h
  exact h

-- Here's an example of a classical theorem using `rw`
example: ∀ (P: Prop), ¬¬P → P := by
  intro p h
  classical
  rw [Classical.not_not] at h
  assumption

/-
Here is how you rewrite in the _other_ direction!
You put a `← ` at the front of the `[...]`.
-/
example n: Odd n → ¬ Even n := by
  intro _
  rw [← odd_neven]
  assumption

-- Here we are rewriting from right to left in a premise.
theorem neven_odd n: ¬ Even n → Odd n := by
  intro h
  rw [← odd_neven] at h
  assumption


-- Here we are rewriting from right to left in a premise.
example n: ¬ Even n → Odd n := by
  intro h
  rw [← odd_neven] at h
  assumption
