import Hundred.p051_predicates_and_relations
open ℕ

/-
Lean also has _patterns_ for more powerful bindings.

a sequence of `,`-separated names `⟨` inside angle brackets `⟩`
break a structure with n components and bind them instead.

Many places accepting names also accept patterns.
A very common case: `intro`
-/
example (A B: Prop): A ∧ B → A := by
  intro ⟨a,_⟩
  exact a

-- The equivalent of intro (λ _) works the same way!
example (A B: Prop): A ∧ B → A :=
  λ ⟨a,_⟩ ↦ a

/-
You will see `rintro` documented as handling these patterns.
But at some stage `intro` itself was generalised, so
now their behaviour is the same.
(And both are kept for backwards-compatibility?)
-/
example (A B C: Prop): (A → B → C) → A ∧ B → C := by
  rintro f ⟨a,b⟩ -- same as `intro ...`
  exact f a b

/-
`rcases <name> with <pattern>` really is a generalisation of `cases <name>`.
The pattern does in-line what the cases usually following `cases` do.

Below I use `|` as a pattern combinator to distinguishes cases.

This is only available in some places like tactic `rcases`,
where it enriches the pattern language, e.g., beyond what is available in term mode.
Intuitively, this usage of `|` mimicks the meaning of `|` in term mode,
-/
example n: Even n ∨ Even n.succ.succ → Odd n.succ := by
  intro h
  rcases h with (h_e0 | h_e2)
  . exact Odd.succ n h_e0
  . cases h_e2 ; assumption

/-
`rcases <name>` (without the `with <pattern>`) is just like `cases <name>`.
Here is the same proof as above using cases instead of a pattern.
-/
example n: Even n ∨ Even n.succ.succ → Odd n.succ := by
  intro h
  rcases h
  . next h_e0 => exact Odd.succ n h_e0
  . next h_e2 => cases h_e2 ; assumption
