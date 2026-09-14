import Hundred.p016_matching
import Hundred.p051_predicates_and_relations

/-
The `simp` tactic normalises the goal
(and `simp at <name` normalises the primise `<name>`).
-/

-- Here, `simp` reduces a match statement (twice).
theorem pred_succ: ∀n, pred n.succ = n := by
  intro n
  cases n
  . case zero =>
    unfold pred
    simp
  . case succ n =>
    unfold pred
    simp

/-
`simp [...]` normalises the goal along with
unfolding all the definitions inside the `[...]`.
This can complete proofs surprisingly fast!
It will also try applying lemmas inside the `[...]`!
-/
theorem pred_odd_even: ∀n, Odd n → Even (pred n) := by
  intro _ ho
  cases ho
  simp [pred]
  assumption

-- tag a lemma with `@[simp]` to let future calls to `simp` try it simplicitly!
@[simp]
theorem pred_succ': ∀n, pred n.succ = n := by
  simp [pred]

example: pred ℕ.zero.succ = ℕ.zero := by
  simp -- uses `pred_succ'` to rewrite `pred ℕ.zero.succ` to `ℕ.zero`!
