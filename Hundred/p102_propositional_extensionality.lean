import Hundred.p091_contradiction
import Hundred.p100_proof_irrelevance

/-
Lean's standard library (and prelude) offer axioms
for lifting _extensional equality_ to _equality_ for some things,
where extensional equality roughly means "equal input/output behaviour".
-/

/-
_Propositional extensionality_ asserts that two
logically equivalent proofs (`p ↔ q`) are equal (`p = q`).

This is not derivable in core Lean, so it is
formulated as an axiom available in the prelude.
The developers of Lean make sure that these axioms preserve soundness.
-/
#print propext

/-
`propext` is handy because it lets you _interchange_
logically equivalent propositions.
For example, lets use it to prove that `Evenℕ` is _equal_ to
the subtype `{ n // ¬ Odd n }`, which formulates the property
very differently, but which we previously proved
(as `even_iff_not_odd`) is logically equivalent to `Evenℕ.property`.
-/

/-

`propext` is handy because it lets you _interchange_
logically equivalent propositions.

Let's use it to prove something that seems
weird if you stick with the original,
strict reading of `=`, but makes perfect sense if
you understand `=` as "safely substitutable"!
-/
example: ∀ n, Even n = Not (Odd n) := by
  intro n
  -- goal: `Even n = ¬Odd n` :(
  apply propext
  -- goal: `Even n ↔ ¬Odd n` :)
  exact even_iff_not_odd n
