import Hundred.p030_propositions

/-
Several of the types in Lean's prelude are polymorphic.
For example, here are examples of the typical logical connectives in Lean.
You can expect to encounter these all the time.
-/
example: Prop → Prop → Prop := And
example: Prop → Prop → Prop := Or
example: Prop := And SomeℕExists SomeℕExists
example: Prop := Or  SomeℕExists SomeℕExists

example: Prop → Prop := Not
example: Prop := Not SomeℕExists
