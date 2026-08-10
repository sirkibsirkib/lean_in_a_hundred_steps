import Hundred.p47_predicates_and_relations
import Hundred.p81_proof_irrelevance
import Hundred.p80_exfalso

/-
Lean's standard library (and prelude) offer axioms
for lifting _extensional equality_ to _equality_ for some things,
where extensional equality roughly means "equal input/output behaviour".
-/

--------- propositional extensionality ---------

/-
_Propositional extensionality_ asserts that two
logically equivalent proofs (`p ↔ q`) are equal (`p = q`).

This is not derivable in core Lean, so it is
formulated as an axiom available in the prelude.
The developers of Lean make sure that these axioms preserve soundness.
-/
#print propext

/-
`propext` is handy because it lets you _interchange_
logically equivalent propositions.
For example, lets use it to prove that `Evenℕ` is _equal_ to
the subtype `{ n // ¬ Odd n }`, which formulates the property
very differently, but which we previously proved
(as `even_iff_not_odd`) is logically equivalent to `Evenℕ.property`.
-/

/-

`propext` is handy because it lets you _interchange_
logically equivalent propositions.
-/

-- `TODO`!!!!!!!!!!!! simple example

--------- functional extensionality ---------

/- For _definitionally equal_ functions, `Eq.refl` suffices to
prove their equality, because they are identical after normalisation.
-/
theorem ℕ.succ_eq_succ: ℕ.succ = ℕ.succ := Eq.refl ℕ.succ

def ℕ.succ' := ℕ.succ
theorem ℕ.succ_eq_succ': ℕ.succ = ℕ.succ' := Eq.refl ℕ.succ

def ℕ.succ_alt: ℕ → ℕ
  | ℕ.zero => ℕ.one
  | n => n.succ

-- ... but we cannot prove this proposition with `Eq.refl` alone,
-- because these functions are not definitionally equal.
def ℕ.succ_eq_succ_alt: Prop := ℕ.succ = ℕ.succ_alt
#reduce ℕ.succ
#reduce ℕ.succ_alt

/-
We can formulate and prove a related property:
_extensional equality_ (of functions) means they
have equal outputs for equal inputs.
-/
abbrev Function.ext_eq {α β} (f g: α → β) := ∀ a, f a = g a

-- We can prove that this is weaker than regular equality.
theorem Function.Eq_implies_ext_eq {α β}:
  ∀ (f g: α → β),
    f = g →
    Function.ext_eq f g
  := by
    intro f g heq
    cases heq
    intro a
    exact Eq.refl (f a)

-- And we can prove `ℕ.succ.ext_eq ℕ.succ_alt`,
-- because `ℕ.succ` does not normalise, but each `ℕ.succ n` does!
def ℕ.succ_ext_eq_succ_alt: ℕ.succ.ext_eq ℕ.succ_alt := by
    intro n
    cases n
    . apply Eq.refl
    . apply Eq.refl

/-
`funext` in the prelude lifts a proof that
two functions are extensionally equal to a proof that they are equal.

`funext` is not derivable in Lean, but the Lean
developers have made sure that it preserves soundness.
-/
#print funext

-- Lets use `funext` to prove `ℕ.succ_eq_succ_alt`!
theorem ℕ.succ_eq_succ_alt_true: ℕ.succ_eq_succ_alt := by
  apply funext
  intro n
  exact ℕ.succ_ext_eq_succ_alt n


-- `funext` is also a tactic that applies `funext`
-- and `intro`s the argument (optionally: with the given name)
example: ℕ.succ_eq_succ_alt := by
  funext n
  exact ℕ.succ_ext_eq_succ_alt n

example: ℕ.succ_eq_succ_alt := by
  funext
  apply ℕ.succ_ext_eq_succ_alt

/-
You can think of `funext` as an axiom, but actually
it is a theorem based on a more fundamental axiom:
`Quot.sound`! You can observe this yourself,
and try to understand `Quot.sound` but it concerns
quotients, which I have not thoroughly understand, to be honest.
-/
#print axioms ℕ.succ_eq_succ_alt_true
#print Quot.sound


--------- both together ---------

/-
Lets use `propext` and `funext` to prove that `Evenℕ` is _equal_ to
the subtype `{ n // ¬ Odd n }`, which formulates the property
very differently, but which we previously proved
(as `even_iff_not_odd`) is logically equivalent to `Evenℕ.property`.
-/

example: Evenℕ = { n // ¬ Odd n } := by
  unfold Evenℕ
  congr -- TODO handle `congr` somewhere!
  funext n
  apply propext
  apply even_iff_not_odd
