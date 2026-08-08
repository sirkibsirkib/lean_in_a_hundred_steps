import Hundred.p01_inductive_types
import Hundred.p03_definitions

/-
`example` can be used in place of `def <name>`.
As such, examples do not introduce any names into the namespace.
They are essentially dead code which Lean checks then discards.

But they are instructive for a reader, because they
are still checked by Lean for well-formedness, well-typedness, etc.

The reader can understand an example as an assertion that...
- `<term>` exists, and is well-typed, and
- (optionally) `<term>` has the type `<type>`.
  and hence `<type>` is inhabited by some term (namely `<term>`).
  When we get to proofs, we are often interested _only_ in this!
  Because types are propositions and (being inhabited) means (proven true).
-/
example: Type := Bit
example: Type := Bit₂ -- Bit₂ is defined in "t03_definitions"
example := Bit
