import Hundred.p001_inductive_types
import Hundred.p063_less_than
import Hundred.p059_subtype

/-
The `change <goal'>` tactic replaces the current goal with `<goal'>`,
as long as the two are _definitionally_ equal (in the sense of p020's `#reduce`).

Nothing forces you to use it: any later tactic (`exact`, `apply`, `cases`, ...)
already sees through definitional equality on its own. But `change` is handy
for making an unfolding step _explicit_, e.g. to strip away notation or a
class projection before continuing, without permanently `unfold`ing the name.
-/

-- `<` is notation for `LT.lt`, which (via the `LTℕ` instance from before)
-- unfolds to our own `ℕ.lt`. `change` lets us jump straight to it.
example: ℕ.zero < ℕ.one := by
  change ℕ.lt ℕ.zero ℕ.one
  exact ℕ.lt.base ℕ.zero

/-
Recall `{ n // P n }` is just notation for `Subtype P`.
`change` can move between the two views, in either direction.
-/
example: Subtype Even := by
  change { n // Even n }
  exact Evenℕ.two

example: { n // Even n } := by
  change Subtype Even
  exact Evenℕ.two

/-
`change` demands _definitional_ equality: the two sides must reduce
to the same term. It is not enough that they are merely both provable,
or both well-formed propositions. Here, swapping the arguments of
`ℕ.lt` gives a different (and, incidentally, false) proposition,
so `change` correctly refuses to equate them.
-/

/--
error: 'change' tactic failed, pattern
  ℕ.one.lt ℕ.zero
is not definitionally equal to target
  ℕ.zero < ℕ.one
-/
#guard_msgs in
example: ℕ.zero < ℕ.one := by
  change ℕ.lt ℕ.one ℕ.zero

-- `show` is like `change` but specialized to transforming the hypothesis.
example: { n // Even n } := by
  show Subtype Even
  exact Evenℕ.two
