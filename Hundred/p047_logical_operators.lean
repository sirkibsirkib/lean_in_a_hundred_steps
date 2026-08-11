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

-- Proving `Not p` means proving `p → False`.
#print Not.intro

/-
`Not.elim` is a handy utility for proving anything given any `p` and `Not p`.
Its formulation (in namespace `Not` and with `Not p` as the first argument),
affords its usage as a method of a proof of a negative.
-/
example: ∀ {P Q}, Not P → P → Q :=         Not.elim
example: ∀ {P Q}, Not P → P → Q := λ np   ↦ np.elim
example: ∀ {P Q}, Not P → P → Q := λ np p ↦ np.elim p

-- `absurd` is just `Not.elim` with the positive first (and not as a method).
-- Sometimes this comes in handy.
example: ∀ {P Q}, P → Not P → Q := absurd
example: ∀ {P Q}, P → Not P → Q := λ p np ↦ absurd p np
