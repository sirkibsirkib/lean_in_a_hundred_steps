import Hundred.p015_matching
import Hundred.p047_predicates_and_relations

/-
The `simp` tactic normalises the goal
(and `simp at <name` normalises the primise `<name>`).
-/

-- Here, `simp` reduces a match statement (twice).
theorem pred_succ: ∀n, pred n.succ = n := by
  intro n
  induction n
  . case zero =>
    unfold pred
    simp
  . case succ n ih =>
    unfold pred
    simp

/-
`simp [...]` normalises the goal along with
unfolding all the definitions inside the `[...]`.
This can complete proofs surprisingly fast!
It will also try applying lemmas inside the `[...]`!
-/
theorem pred_succ': ∀n, pred n.succ = n := by
  simp [pred]

theorem pred_odd_even: ∀n, Odd n → Even (pred n) := by
  intro _ ho
  cases ho
  simp [pred]
  assumption
