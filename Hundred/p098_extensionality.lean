import Hundred.p096_decidable


/-
_Extensionality_ is a very generic idea:
two objects are equal under some weaker notion
of equivalence of components or behaviour.
-/

/-
It is common to define _extensionality lemmas_
for inductive data types, breaking the goal of equality (`=`)
into smaller subgoals.
-/


/-
Lean maintains a registry of lemmas for
breaking down equality goals into subgoals
vial such extensionality lemmas.
- the `@[ext]` annotation registers a lemma.
- the `ext` tactic looks up in the registry,
  and applies lemmas to the goal.

Let's register this as an extensionality lemma
for asserting the equality of `Maybe'` values.
-/
@[ext]
theorem Maybe'.extend_bit:
    {a b: Maybe' Bit} →
    (h: ∀ t: Bit, Maybe'.some t = a ↔ Maybe'.some t = b) →
    a = b
| none  , none  , _ => rfl
| _     , some y, h => (h y).mpr rfl |>.symm
| some x, _     , h => (h x).mp  rfl

#print Maybe'.extend_bit
#print Maybe'.extend_bit_iff

-- The above theorem can be applied manually as usual
example: @Maybe'.none Bit = .none := by
  apply Maybe'.extend_bit
  intro t
  constructor <;> intro h <;> exact h

-- But tactic `ext` will also apply it where it fits!
-- Here I choose to name the introduced variable `t`.
example: @Maybe'.none Bit = .none := by
  ext t
  constructor <;> intro h <;> exact h

/-
With `@[ext]` Lean tries to generate an `*_iff` theorem.
But not all are of the right shape.
The following cannot accept a `@[ext]`,
unless I disable the attempt to generate the `*_iff` theorem.
-/
@[ext (iff := false)]
theorem Maybe'.extend_ℕ:
  (a b: Maybe' ℕ) →
  (∀ n, Maybe'.some n ≠ a) →
  (∀ n, Maybe'.some n ≠ b) →
  a = b
:= by
  intro a b ha hb
  cases a
  . case some a =>
    specialize ha a
    contradiction
  . case none =>
    cases b
    . case some b =>
      specialize hb b
      contradiction
    . case none =>
      rfl

#print Maybe'.extend_ℕ

example: @Maybe'.none ℕ = .none := by
  have h: ∀ n: ℕ, Maybe'.some n ≠ .none := by
    intro n h
    cases h
  ext <;> apply h

/-
Use `@[ext]` on inductive and structure definitions
to generate lemmas for deriving theorems of the form:
  if fields of `x y: Y` are pairwise equal, then `x = y`.
-/
@[ext]
structure Point where mk::
  a: ℕ
  b: ℕ

#print Point.ext
#print Point.ext_iff

-- manually applying `Point.ext`
example a b (h: a = b): Point.mk a b = ⟨b, a⟩ := by
  apply Point.ext
  . exact h
  . exact h.symm

-- applying the lookup of `ext`, which is also `Point.ext`.
example a b (h: a = b): Point.mk a b = ⟨b, a⟩ := by
  ext
  . exact h
  . exact h.symm
