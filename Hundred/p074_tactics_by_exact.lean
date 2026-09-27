/-
So far, we have only interacted with Lean's (arguably primary) _term_ mode,
which is typical functional programming.

But lean also has another _tactic_ language, which has a little bit
of an imperative style, and aims to read like more
conventional mathematical pen-and-paper proofs.

`by <tactics>` is a valid term.
`exact <term>` is a valic tactic.
Thus you can dance in and out of the two languages / modes.
-/
example: Type := Prop
example: Type := by exact Prop
example: Type := by exact by exact Prop
example: Type := by
  exact (by exact Prop)

/-
Proof mode and tactics are not strictly necessary.
For example, Agda does just fine without proof mode!

But tactics are just another tool in your belt;
some terms are more easily defined via tactics,
which provide some metaprogramming magic to be quite concise and frictionless.
-/
