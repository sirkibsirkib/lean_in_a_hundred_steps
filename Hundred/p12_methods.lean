import Hundred.p11_abbreviation

/-
Lean has a convenient feature:
`a.f` is sugar for `(f a)` whenever
1. `f` is a function in some namespace `A`
2. `a : A`
3. `f` has some type `A → B`
-/
example: Bit := Bit.nah.bit_id -- with sugar
example: Bit := Bit.bit_id Bit.nah -- without
