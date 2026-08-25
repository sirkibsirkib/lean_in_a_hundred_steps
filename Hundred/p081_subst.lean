import Hundred.p015_matching
import Hundred.p026_structural_recursion
import Hundred.p051_notation
import Hundred.p043_inductive_parameters_vs_indices
import Hundred.p049_predicates_and_relations
open ℕ

/-
`subst <name>` removes `name` from the context
by substituting it with something in context
with which it is equal (`n = ...`) or
definitionally equal (`n := ...`).
-/
theorem try_pred'_some_not_zero
: ∀ (a b: ℕ),
  try_pred' a = Maybe'.some b →
  a ≠ ℕ.zero
:= by
  intro a b heq
  intro _
  subst a
  simp [try_pred'] at heq

theorem try_pred'_none_zero
: ∀ (n: ℕ),
  try_pred' n = Maybe'.none →
  n = ℕ.zero
:= by
  intro n heq
  cases n
  . rfl
  . case succ n =>
    exfalso
    simp [try_pred'] at heq

theorem try_pred'_some_iff_not_zero
: ∀ a,
    a ≠ ℕ.zero ↔ (∃b, try_pred' a = Maybe'.some b)
:= by
  intro a
  constructor
  . intro h
    cases a
    . contradiction
    . rename_i a
      apply Exists.intro a
      simp [try_pred']
  . intro ⟨b, hb⟩
    cases a
    . simp [try_pred'] at hb
    . next a =>
      intro
      contradiction
