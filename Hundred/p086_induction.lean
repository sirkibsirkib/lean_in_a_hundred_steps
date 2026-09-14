import Hundred.p053_notation
import Hundred.p051_predicates_and_relations
import Hundred.p063_less_than
import Hundred.p064_add

namespace Lyst
  variable {T: Type}

  /-
  We have already seen recursive function definitions:
    you simply use the function being defined inside the definition!
  This is quite natural to do in some cases, like this.
  -/
  def len₁: Lyst T → ℕ
    | ⟦⟧ => ℕ.zero
    | _ ∷ l => l.len₁.succ

  -- This also works in tactic mode
  def len₂: Lyst T → ℕ := by
    intro l
    cases l
    . exact ℕ.zero
    . rename_i _ l
      exact l.len₂.succ

end Lyst

/-
But a more conventional thing to do in tactic mode is
to use the `induction <t:T>` tactic instead.
This behaves much like `cases <t:T` in splitting into
subgoals, one per constructor of `T`.
But for inductive constructors, you acquire an _induction hypothesis_ in context,
  where the current goal is already proven for `T`-type subterm of `t`.

Let's use it to prove "every number is odd or even"
-/
theorem even_or_odd: ∀ n, Even n ∨ Odd n := by
  intro n
  induction n
  . left
    exact Even.zero
  . case succ n ind_hyp =>
    -- `ind_hyp : Even n ∨ Odd n`
    cases ind_hyp
    . case inl h =>
      right
      exact Odd.succ n h
    . case inr h =>
      left
      exact Even.succ n h

  -- Note that this theorem can be defined in term mode just fine, via recursion!
theorem even_or_odd': ∀ n, Even n ∨ Odd n
  | .zero => Or.inl Even.zero
  | .succ n =>
    match even_or_odd' n with
    | .inl ind_hyp =>
      .inr (Odd.succ n ind_hyp)
    | .inr ind_hyp =>
      .inl (Even.succ n ind_hyp)

-- Here's something we will use later:
-- A simple proof using `induction` and `constructor`
theorem ℕzero_lt_succ: ∀ (a: ℕ), ℕ.zero < a.succ := by
  intro n
  induction n
  . constructor
  . constructor
    assumption

/-
Let's prove that `ℕ.succ` distributes
over the right hand side of `ℕ.sum`.
-/
@[simp]
theorem ℕ.sum_succ:
  ∀ (a b: ℕ),
    sum a b.succ = (sum a b).succ
:= by
  intro a
  induction a
  . intro b
    rfl
  . case succ a' ih =>
    intro b
    exact ih b.succ

/-
`induction x generalizing y with ...` is sugar
for
`revert y`
`induction x`
`. intro y ...`
`. intro y ...`
`. intro y ...`

Combining such tricks can make proofs more readable!
-/
theorem ℕ.sum_succ' (a b: ℕ):
  sum a b.succ = (sum a b).succ
:= by induction a generalizing b with
  | zero       => rfl
  | succ a' ih => exact ih b.succ
