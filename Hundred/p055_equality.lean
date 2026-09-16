import Hundred.p001_inductive_types
import Hundred.p015_constructor_functions
import Hundred.p045_inductive_parameters_vs_indices
open ℕ
/-
Intuitively, `Eq x y` is the standard (strongest)
proposition of equivalence of `x` and `y` of any sort.
(As usual, constructing the proposition does not mean it is provable!)
-/
example: Prop := Eq ℕ ℕ
example: Prop := Eq ℕ Bit
example: Prop := Eq one two
example: Prop := Eq two one.succ
example: ℕ → Prop := Eq two
example: ℕ → ℕ → Prop := Eq
example: Bit → Bit → Prop := Eq

-- The prelude gives `x=y` as notation for `Eq x y`.
example: Prop := ℕ = ℕ
example: Prop := one = two

/-
(Arguably), `Eq` is most crucial for how it can be used!
When `x=y`, you can substitute any occurrence for `x` with `y`.

In the Lean prelude, function `x=y` is foundational for
apply this sort of reasoning.

But note that you may never use `Eq.rec` directly,
but many utilities (like the `rw` tactic) that we discuss later
present these kinds of primitives in a friendlier package.

The overall idea is more important to grasp:
  `x=y` affords a _semantic equality_, because it lets you
  interchange `x` and `y` without otherwise affecting what is provable.
-/
#print Eq.rec

-- Super general: `Eq.rec` lifts any `P x` to any `P y` given `x = y`
example (T: Sort u) (x y: T) (P: T → Prop):  x=y → P x → P y :=
  λ heq px ↦ Eq.rec px heq

-- More concrete: `Eq.rec` lifts any proof that `x:ℕ` is cool
-- to a proof that `y` is cool given that `x=y`.
example (x y: ℕ): x=y → Cool x → Cool y :=
  λ heq coolx ↦ Eq.rec coolx heq

/-
`Eq.refl` is the only constructor for proofs of equality.
It is only applicable in a context with _semantic equality_:
  `Eq.refl` accepts some `x` and then constructs `Eq x x`!
-/
#print Eq.refl

-- Here are some trivial constructions of `Eq` proofs:
example: zero = zero := Eq.refl zero

/-
Here we can see that Lean considers unfoldings of
definitions (and abbreviations) as preserving syntactic equality.
So you could say that `x := y` implies `x = y`.
In such contexts, Lean may fail to (automatically) unfold
the definitions correctly. How hard it tries is one point
where `abbrev` vs `def` matters. Later, in proofs,
the user can control this unfolding explicitly,
thus making `abbrev` vs `def` determine the (syntax) of how
proofs are written, but no (semantic) provability.
-/
example: Eq one.succ two := Eq.refl two

-- `Not (Eq _ _)` is common enough to warrant notation `≠` input as \neq.
example: Prop := one = two
example: Prop := one ≠ two

-- Look! Lean's unfolding of `≠` trivialises the proof
-- that this notation means what we think it means. Meta!
example (x y: Prop): (x ≠ y) = ¬(x = y) := Eq.refl (x ≠ y)


/-
`Eq` propositions and proofs are so common,
that it pays to be familiar with the common
utilities for `Eq` (under the `Eq` namespace and prelude).
-/

-- `Eq.symm` flips the equality.
example: ∀ {m n: ℕ}, m=n → n=m := Eq.symm

-- `Eq.trans` derives `a=c` from `a=b` and `b=c`.
example: ∀ {a b c: ℕ}, a=b → b=c → a=c := Eq.trans

-- `rfl` is an abbreviation of `Eq.refl _`
example: ∀ {n: ℕ}, n=n := rfl
