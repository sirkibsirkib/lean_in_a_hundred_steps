import Hundred.p26_structural_recursion

/-
Let's define the `Add` typeclass for `ℕ`.
We actually defined `ℕ.sum` already, which
maps neatly to what `Add.sum` expects.
-/
instance: Add ℕ where
  add := ℕ.sum

/-
Now the notation `x + y` is defined for `ℕ`-type values,
and any (standard) definitions atop `Add` apply to `ℕ`.
-/
example: ℕ := ℕ.zero + ℕ.two
