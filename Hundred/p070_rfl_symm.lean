import Hundred.p014_constructor_functions

/-
Recall that `Eq.refl` is the only constructor for `_ = _`.
`rfl` is sugar for `apply Eq.refl`.
You see it often when working with equality (often).

The utility of `rfl` is so minor I often forget that it exists.
-/
example: ∀n: ℕ, n=n := Eq.refl
example: ∀n: ℕ, n=n := by exact Eq.refl
example: ∀n: ℕ, n=n := by apply Eq.refl
example: ∀n: ℕ, n=n := by intro n ; rfl
example: ∀n: ℕ, n=n := by apply rfl

-- The `symm` tactic applies `Eq.symm`, flipping the equality in a premise / goal
example (x y: Sort u): x=y → y=x := by
  intro h
  symm
  symm at h
  symm
  assumption
