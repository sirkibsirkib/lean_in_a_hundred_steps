import Hundred.p26_structural_recursion
import Hundred.p72_induction

/-
Here's a more substantial proof:
`ℕ.add` (aka `ℕ.sum`) is symmetric.
-/

#check Trans

-- sum a 0 = a
theorem ℕ.sum_zero:
  ∀ a,
    sum a zero = a
:= by
  intro a
  induction a with
  | zero => simp [sum]
  | succ a' ih =>
    -- goal: sum a'.succ zero = a'.succ
    -- prove
    calc
      sum a'.succ zero   = sum a' zero.succ   := by simp [sum]
      sum a' zero.succ   = (sum a' zero).succ := sum_succ a' zero
      (sum a' zero).succ = a'.succ          := by rw [ih]

theorem ℕ.sum_symm:
  ∀ a b,
    sum a b = sum b a
:= by
  intro a
  induction a with
  | zero => intro b; simp [sum, sum_zero]
  | succ a' ih =>
    intro b
    calc sum a'.succ b = sum a' b.succ := by simp [sum]
      _ = sum b.succ a'                := ih b.succ
      _ = sum b a'.succ                := by simp [sum]
