import Hundred.p021_currying
open Bit
/-
Multiple (chained) binders are made easier on the eyes
with some nice shorthand.

`λ` and `→` are all right-associative, so
parentheses on the right (e.g., resulting from Currying)
can be omitted without changing the meaning.
-/
def const_bit₃ := λ (_:Bit) ↦ λ (_:Bit) ↦ nah
example: Bit → Bit → Bit := const_bit₃

/-
`λ` takes it a step further, but letting
sequenced binders share one `λ ... ↦`.

Sadly, this is not the case for `→`.
You really need one `→` per argument.
-/
def const_bit₄ := λ (_:Bit) (_:Bit) ↦ Bit.nah
example: Bit → Bit → Bit := const_bit₄

-- Thus, we can neatly express N-ary functions!
def const_bit: Bit → Bit → Bit :=
  λ b1 _ ↦ b1

example: Bit → Bit → Bit := const_bit
example:       Bit → Bit := const_bit nah
example:             Bit := const_bit nah nah

#reduce const_bit nah nah
#reduce const_bit nah yep
#reduce const_bit yep nah
#reduce const_bit yep yep


/-
Finally, successive binders of the same type like `(a:A) (b:A)`
can be grouped under the same `(... : <type>)`!
-/
def const_bit' := λ (b1 _: Bit) ↦ b1
