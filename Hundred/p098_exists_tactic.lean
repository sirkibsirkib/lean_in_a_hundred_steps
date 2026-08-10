import Hundred.p026_structural_recursion
import Hundred.p042_inductive_parameters_vs_indices

/-
Recall that `Exists` is just some standard inductive
definition with only the `intro`
1. some term

The `exists <term>` tactic is handy
whenever you have a goal of the form `∃ <witness>, _`:
you supply the witness as `term`.

It is roughly equivalent to `apply Exists.intro <witness>`
(but it also does some simplification steps that
may immediately complete the proof).
-/

theorem neq_zero_exists_succ:
  ∀ (a: ℕ),
  a ≠ ℕ.zero →
  ∃ (b: ℕ), a = b.succ
:= by
  intro a hneq
  cases a
  . contradiction
  . clear hneq
    rename_i a
    exists a -- `apply Exists.intro a` (plus some `simp` steps)

theorem try_pred_some_iff_not_zero
: ∀a, a ≠ ℕ.zero ↔ (∃b, try_pred' a = Maybe'.some b)
:= by
  intro a
  constructor -- `apply Iff.intro`, produces goals for `←` and `→`
  . case mp =>
    intro aneq
    have ⟨a, h⟩ := neq_zero_exists_succ _ aneq
    subst h
    exists a
  . case mpr =>
    intro ⟨b, hb⟩
    cases a
    . simp [try_pred'] at hb
    . next a =>
      intro
      contradiction
