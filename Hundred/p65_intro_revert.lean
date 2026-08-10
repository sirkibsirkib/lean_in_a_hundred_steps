import Hundred.p47_predicates_and_relations
open ℕ

/-
`intro (x : Y)` builds `λ (x : Y) ↦ <body>` in tactic mode,
and then continues building term `<body` in tactic mode.
Logically, it changes goal `a → b` into `b` and moves `a` into the _context_:
  the collection of definitions in the local scope.
-/
example: ℕ → ℕ := by
  intro n -- premise n:ℕ added to context!
  exact zero

/-
`revert n` undoes `intro n`.
This "massages the proof term" in the sort of
non-structural way that is only possible in proof mode.

Here, `intro n; revert n` just cancel out, leaving no
trace on the resulting proof term
-/
def const_zero: ℕ → ℕ := by
  intro n
  revert n
  intro n
  exact zero
#print const_zero

-- As one λ can bind several arguments, `intro` can introduce a list.
example: ℕ → ℕ → ℕ → ℕ := by
  intro _ b _
  exact b
