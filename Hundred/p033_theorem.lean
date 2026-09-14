import Hundred.p032_propositions
open ℕ

/-
In Lean, `theorem` is the same as `def`, but
(only) the former is intended for proving propositions.
1. You get an error if you use `theorem` to define values in `Type`
2. You get a warning if you use `def` to define values in `Prop`

(`example` is happy with either).
-/
example: Prop := SomeℕExists
example: ℕ → SomeℕExists := SomeℕExists.this_one

theorem ℕ.non_empty: SomeℕExists :=
  SomeℕExists.this_one ℕ.four

-- This does the same but generates a warning (as of Lean v4.33 at least)

/--
warning: Definition `non_empty'` is a proposition;
use `theorem` instead of `def`
Note: This linter can be disabled
with `set_option linter.defProp false`
-/
#guard_msgs (whitespace := lax) in
def ℕ.non_empty': SomeℕExists :=
  SomeℕExists.this_one ℕ.four

-- The type of this definition is `ℕ → SomeℕExists`
-- where `ℕ: Type` and `SomeℕExists: Prop`
-- Use `theorem` here, because the _output_ is what matters!
theorem ℕ.SomeℕExists: ℕ → SomeℕExists := SomeℕExists.this_one
