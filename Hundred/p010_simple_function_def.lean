import Hundred.p001_inductive_types

/-
`λ (<x> : <X>) ↦ <y>` is a function that,
when applied to some `X`-type value, returns `y`.
-/
def bit_const_nah := λ (_b: Bit) ↦ Bit.nah

/-
The utility of functions is that they can have _dependent values_:
The output `y` can be formulated in terms of the binding `x`.

Below, this is the case, the trivial case: the body _is_ the binder.
Intuitively, this defines the _identity function_ for the `Bit`-type:
  given any Bit as input, the output is the same bit.
-/
def bit_id := λ (b: Bit) ↦ b

/-
Wildcard `_` can be used in place of a binder
to still mark a parameter, but bind it to no name.

This has two usability benefits:
1. it avoids cluttering up the scope inside the function body
2. it avoids suggesting that the parameter is used in the body.
-/
def bit_const_nah' := λ (_: Bit) ↦ Bit.nah

/-
`A → B` is the type of a function `λ (_: A) ↦ (_: B)`.

Later, we will detail how `A → B` is
a special case of something more general:
`(a: A) → B` is the type of a function
`λ (_: A) ↦ (_: B)` whose type `B` potentially depends on a.

But for now, we stick to `A → B`,
where `B` is independent on the input value.
-/
example: Bit → Bit := bit_id
example: Bit → Bit := bit_const_nah
example: Bit → Bit := bit_const_nah'

-- Note: in `λ _ ↦ _`,
-- - the `λ` can alternatively be spelled `fun`
-- - the `↦` can alternatively be spelled `=>`
-- - the `→` can alternativelu be spelled `->`
