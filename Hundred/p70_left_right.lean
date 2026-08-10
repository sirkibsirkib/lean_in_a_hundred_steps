import Hundred.p14_constructor_functions
import Hundred.p47_predicates_and_relations
open ℕ

/-
Tactics `left` and `right` are sugar for applying
the first and second constructor (respectively)
whenever the goal is an inductive type with 2 constructors.

The canonical usages are for `Or` and `Sum`.
-/
example {A B: Prop}: A → A ∨ B := by
  intro _
  -- A ⊢ A ∨ B
  left -- apply Or.Inl
  -- A ⊢ A
  assumption

example {A B: Prop}: B → A ∨ B := by
  intro _
  -- B ⊢ A ∨ B
  right -- apply Or.Inr
  -- B ⊢ B
  assumption

-- See how `left` and `right` work for ℕ,
-- because it also has two constructors?
example: three = (by
  right -- apply ℕ.succ
  right -- apply ℕ.succ
  right -- apply ℕ.succ
  left  -- apply ℕ.zero
) := Eq.refl _


/-
`left` and `right` work for `Even`, because it only has two constructors.
But they don't work for `Odd`, because it has just one constructor: `Odd.succ`.
-/
example: Even two := by
  right -- Apply Even.succ
  apply Odd.succ
  left  -- Apply Even.zero
