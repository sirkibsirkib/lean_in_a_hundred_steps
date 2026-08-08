import Hundred.p15_matching
import Hundred.p45_predicates_and_relations
import Hundred.p80_simp
open ℕ

-- `repeat <tactic>` will repeat the given tactic while it works
-- (or fail after some configured maximum, to ensure termination).
theorem predsucc_2: ∀n:ℕ, pred (pred n.succ.succ) = n := by
  intro n
  repeat rw [pred_succ] -- repeats twice!

-- This is a case where `simp` could also be used instead.
theorem predsucc_2': ∀n:ℕ, pred (pred n.succ.succ) = n := by
  intro n
  simp [pred_succ] -- repeats twice!

/-
`repeat` actually accepts a sort of `(first | ...)`pattern,
where the following list of alternative tactics are
tried in depth-first fashion, going as far as possible.
-/
theorem EvenFour: Even four := by
  -- goal: Even four
  repeat (first | apply Even.succ | apply Odd.succ)
  -- goal: Even zero
  exact Even.zero

-- Or even just with `repeat`!
theorem EvenFour': Even four :=
  by repeat (first | exact Even.zero | apply Even.succ | apply Odd.succ)

theorem EvenFour'': Even four := by repeat constructor

-- But `Even four` is a case where `repeat` did something `simp` cannot
-- because simp only tries rewriting the goal, not applying constructors.
