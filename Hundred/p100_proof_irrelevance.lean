import Hundred.p001_inductive_types
import Hundred.p015_constructor_functions
import Hundred.p051_predicates_and_relations
import Hundred.p059_subtype

/-
In Rocq and Lean, things in `Type u` are _computationally relevant_,
so differently-constructed terms of the same type are not unifiable.

In proofs, you will encounter this as cases where `h: x = y`
is in context, and doing `cases h` forces Lean to consider
all the ways to unify `x` and `y`. There are none!
Let's use this to prove `Bit.nah = Bit.yep`
-/

-- In proof mode, `cases h` closes the goal and introduces zero subgoals.
theorem Bit.not_all_same: Bit.nah ≠ Bit.yep := by
  intro h
  -- given `Bit.nah = Bit.yep` prove `False`
  cases h -- zero cases remain! Proof complete

-- In term mode, `nomatch h` defines a mapping for all zero cases.
theorem Bit.not_all_same': Bit.nah ≠ Bit.yep :=
  λ h ↦ nomatch h

/-
In Rocq and Lean, things in `Prop` are _not_ computationally relevant.
Mechanically, Lean and
-/

#print Bit.not_all_same

theorem Bit.nah_neq_yep: nah = yep → False :=
  λ h ↦ nomatch h

theorem Bit.nah_neq_yep₂: nah = yep → False := by
  intro h
  -- h : yep = nah
  cases h -- Lean discovers that `h` is contradictory
  done
#print Bit.nah_neq_yep

-- However, this is fundamentally different for propositions!
-- Lean learns nothing from unifying differently constructed proofs.

inductive Bit': Prop where
  | yep
  | nah

/-
The following would be rejected by Lean!
The `cases h` step does not complete the proof here.
-/

/-- error: unsolved goals
⊢ False -/
#guard_msgs(error) in
example: 1=2 := by
  simp -- proof incomplete!

/-- error: unsolved goals
case refl
⊢ False -/
#guard_msgs in
example: Bit'.yep = Bit'.nah → False := by
  intro h
  -- h : yep = nah
  cases h -- `h` is gone! We learned nothing and the goal remains False!

/- These observations are fundamentally the same in Rocq
`Inductive Bit: Type := yep | nah.`
`Theorem nah_neq_yep: not (yep = nah).`
`Proof.`
`  intro h.`
`  inversion h.`
`Qed.`

`Inductive Bit': Prop := yep' | nah'.`
`Theorem nah'_neq_yep': not (yep' = nah').`
`Proof.`
`  intro h.`
`  inversion h. (* no effect! *)`
`Abort.`
(Rocq `Abort` and is like `sorry` except that
 it is safe because the term is discarded!
 I miss it in Lean dearly.)
-/

/-
Both Rocq and Lean introduce a concept of _proof irrelevance_:
  all proofs of the same proposition are equal.

In Rocq, proof irrlevance is an axiom in the standard library.
But in Lean, it is built into the special treatment of `Prop`,
so it is a theorem trivially proven by `Eq.refl` without an additional axiom.
-/
#print proof_irrel

-- As such, we can prove the inverse of the `Bit'.nah_neq_yep` we tried earlier!
theorem Bit'.nah_eq_yep: yep = nah :=
  proof_irrel yep nah

/-
Mechanically, this is quite handy!

For example, see how proof irrelevance means that the
only computationally relevant part of any `Evenℕ` is
the inner `val: ℕ`, because its proof `property: Even n` is
interchangable with any other proof of that proposition!

As such, we can easily lift equality of `ℕ` to equality of `Evenℕ`.
-/
#print Evenℕ

theorem Evenℕ.lift_eq:
  ∀ (n₁ n₂: Evenℕ),
    n₁.val = n₂.val →
    n₁   = n₂
:= by
  intro ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩ h
  cases h -- unfiies `n₁` and `n₂`
  exact Eq.refl _ -- this applies despites the sides not being syntactically equal!

/-
As such, you should not use Propositions to encode data
that you want to distinguish!

Consider how this separates propositions from other types.
Lots of programs would be useless
-/
