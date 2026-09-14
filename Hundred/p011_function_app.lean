import Hundred.p010_simple_function_def

/-
`<f> <x>` applies the function `f` to value `x`.
Lean will check that `f` is some function of some type `∀ (i:I), O`
and then check that `x:I`.

The result of the function application has type `O`
(possibly dependent on `x`).
-/
example: Bit → Bit := bit_id -- the function
example: Bit       := Bit.nah   -- the input
example:       Bit := bit_id /- application whitespace -/ Bit.nah
