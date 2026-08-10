import Hundred.p014_constructor_functions
import Hundred.p042_inductive_parameters_vs_indices
open ℕ

/-
`Exists` is in the Lean prelude, for proposing that
some element of some type exists which satisfies a proposition.
-/
example (T: Sort u): (T → Prop) → Prop := Exists -- There exists ...
example: (ℕ → Prop) → Prop := Exists -- There exists a ℕ ...
example: Prop := Exists Cool -- There exists a ℕ which is Cool

/-
Proving `Exists (pred: T → Prop)` means providing
- some `witness: T`
- some proof of `pred witness`
-/
example: ∀n, Cool n → Exists Cool := Exists.intro
example: Cool one → Exists Cool := Exists.intro one -- fix the witness

example: {n: ℕ} → Cool n := Cool.intro
example: Exists Cool := Exists.intro one (@Cool.intro one)

-- Lean provides `∃ (_: _), P x` as notation for `Exists P`.
def CoolExists: Prop := ∃ (n: ℕ), Cool n
example: CoolExists := Exists.intro one (@Cool.intro one)
example: CoolExists := Exists.intro one   Cool.intro

/-
Note the intentional resemblance between `∀ x, P x` and `∃ x, P x`.
Even though the former is somehow foundational to Lean and the latter is just
notation for an inductive data type like any other (e.g., which the user could define),
the lean prelude includes all sorts of results showing how they are related
in all the ways that mathematicians would expect!
-/
example
  /-
  for any predicate over any sort,
    it is false that any value exists that satisfies the predicate
    iff
    each value does not satisfy the predicate
  -/
  : ∀ (α: Sort u_1) (pred: α → Prop), (¬∃ x, pred x) ↔ ∀ (x: α), ¬pred x
  := @not_exists
