import Hundred.p014_constructor_functions
import Hundred.p047_predicates_and_relations
open ℕ

/-
The `constructor` tactic applies the first constructor applicable to the goal!
The tactic fails if no constructors apply.
-/
example: Odd three := by
  -- ⊢  Odd three
  constructor -- `apply  Odd.succ`
  -- ⊢ Even two
  constructor -- `apply Even.succ` (because `Even.zero` does not apply)
  -- ⊢  Odd one
  constructor -- `apply  Odd.succ`
  -- ⊢ Even zero
  constructor -- `apply Even.zero`

-- You will be surprised how often `constructor` suffices
example
: (zero = by constructor) -- here `constructor` is `apply ℕ.zero`
:= by constructor         -- here `constructor` is `apply Eq.refl`
