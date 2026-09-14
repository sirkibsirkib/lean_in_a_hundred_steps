import Hundred.p015_constructor_functions

open ℕ
def plus: ℕ → ℕ → ℕ
| zero   => id
| succ a => λ b ↦ (plus a b).succ

variable (n: ℕ)

-- `n` occurs in the following,
-- so Lean silently adds (n: N) to the parameters.
def n': ℕ := n
example: ℕ → ℕ := n'

-- But now you see `n'` actually has type `ℕ → ℕ` and not `ℕ`,
-- despite `n''` actually using `n` the same way.
def n'': ℕ := plus n (n' n)
example: ℕ → ℕ := n''

/-
I find `variable` in Lean rather useless.
Rocq's version is much better. Dependency on a variable
bubbles up intelligently until the scope is closed,
whereafter the definition has an extra parameter, as in Lean.
-/
