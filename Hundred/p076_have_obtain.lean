import Hundred.p015_constructor_functions
import Hundred.p045_inductive_parameters_vs_indices
import Hundred.p051_predicates_and_relations

/-
`have` is the tactic version of `let`.
In proofs, it affords a foward reasoning style,
where you build intermediates from terms in
the context, rather than working backward
where you focus on transforming your goal.
-/
open ℕ

example: Even four := by
  have h: Even  zero := Even.zero
  have h:  Odd   one :=  Odd.succ _ h
  have h: Even   two := Even.succ _ h
  have h:  Odd three :=  Odd.succ _ h
  have h: Even  four := Even.succ _ h
  exact h

/-
`obtain` is like `have`,  except that the
right hand side is just the name of a premise,
which is removed afterwards.
-/

example: ∀ (P Q: Prop), (P ↔ Q) → P → Q := by
  intro P Q i

  have ⟨l, r⟩ := i
  -- `i` remains. `l` and `r` created.

  obtain ⟨l, r⟩ := i
  -- `i` is gone. Prior `l` and `r` are in scope,
  -- but inaccessible, as their names are shadowed.

  exact l
