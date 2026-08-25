import Hundred.p049_predicates_and_relations

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
inductive Strange: Type where
  | mk: (let id t := t; id Strange) → Strange
example: Strange → Strange := Strange.mk

-- Here `;` is mixed in a bit to declutter a realistic proof
theorem even_nand_odd: ∀ n, Even n → Odd n → False := by
  intro n; induction n
  . case zero =>
    intro he ho; cases ho
  . case succ n ih =>
    intro he ho
    apply ih
    . cases ho; assumption
    . cases he; assumption

/-
`<;>` is a similar tactic combinator:
it applies the second tactic to each subgoal created by the first.

Think of `a <;> b`
as
`a`
`. b ...`
`. b ...`
`. b ...`

TODO example
-/
