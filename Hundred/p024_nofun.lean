import Hundred.p001_inductive_types

/-
`nofun` is similar to `nomatch`, except that it
picks an arbitrary vacuous parameter.
Essentially, it is just shorthand.
-/
example: Nothing → Bit := λ x ↦ nomatch x
example: Nothing → Bit := nofun

example: Bit → Nothing → Nothing → Bit → Bit := λ _ n _ _ ↦ nomatch n
example: Bit → Nothing → Nothing → Bit → Bit := λ _ _ n _ ↦ nomatch n
example: Bit → Nothing → Nothing → Bit → Bit := nofun
