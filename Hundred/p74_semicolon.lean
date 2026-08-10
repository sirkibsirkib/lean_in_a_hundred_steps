/-
`;` composes two tactics into one.
* You see no intermediate result.
* You can put them on one line.
-/
example: ∀ (A B: Prop), A → A ∨ B := by
  intro _ _ a; left ; exact a

/-
`;` also works in term mode.

It is particularly useful in combination with `let`,
which ordinarily needs a line break to split the bound term
from the term which uses the binding.
-/
inductive Foo: Type where
  | foo: (let id t := t; id Foo) → Foo
