import Hundred.p47_predicates_and_relations

/-
The `apply <f>` tactic transforms the goal `X`
into `Y` if `f: A → B`.

As the name suggests, it is the tactic form of applying
a given function. It just slaps `f` into your proof term.
-/
example: ∀ n, Even n → Odd n.succ := by
  -- goal is `∀ n, Even n → Odd n.succ`
  intro n _
  -- goal is `Odd n.succ`
  apply (Odd.succ: ∀ n, Even n → Odd n.succ )
  -- goal is `Even n.succ`
  assumption

-- The argument to `apply` is a _term_, which allows you
-- to partially apply the function in-line. Convenient!
example: Odd ℕ.zero → Even ℕ.one := by
  intro Hnonsense
  apply Even.succ ℕ.zero
  assumption

-- And `apply x` can always substitute `exact x` ...
example: ℕ := by exact ℕ.zero
example: ℕ := by apply ℕ.zero
-- ... but `apply` may be misleading in such cases,
-- by suggesting the proof is more complicated than it is.
example: Odd ℕ.zero → Even ℕ.one := by
  intro Hnonsense
  apply Even.succ ℕ.zero Hnonsense

/-
Applying a function with N parameters gives you N subgoals!
-/
example (A B C: Prop): (A → B → C) → A ∧ B → C := by
  intro f
  intro ab
  cases ab
  next a b =>
  apply f -- two goals! `A` and `B`!
  . exact a
  . exact b
