import Hundred.p022_structure

/-
`<term>.<n: natural number>` projects any
inductively-typed `term` to its `n`th parameter.
(where the count starts with `1`).

This only works for terms of "conjunctive" types,
which have exactly one constructor.
As such, it works for all `structure` types.
-/
example: ℕPair → ℕ := λ p ↦ p.1
example: ℕPair → ℕ := λ p ↦ p.2
#reduce (ℕPair.mk ℕ.zero ℕ.two).2
