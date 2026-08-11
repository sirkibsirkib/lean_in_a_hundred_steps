import Hundred.p014_constructor_functions
import Hundred.p048_predicates_and_relations

/-
The `specialize` tactic transforms
a premise in-place by applying it to
a specified argument.

It feels like "peeling off a parameter".
-/

-- forward, transforming a premise
example: (∀ n, Even n) → Odd ℕ.two := by
  intro h
  specialize h ℕ.one
  exact Odd.succ _ h

-- backward, transforming the goal
example: (∀ n, Even n) → Odd ℕ.two := by
  intro h
  apply Odd.succ
  exact h ℕ.one

/-
The `generalize` tactic transforms a
premise in-place by
-/
example: (∀ n, Even n) → Odd ℕ.two := by
  intro h
  specialize h ℕ.one
  exact Odd.succ _ h
