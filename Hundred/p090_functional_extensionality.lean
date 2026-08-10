import Hundred.p047_predicates_and_relations
import Hundred.p082_exfalso
import Hundred.p088_proof_irrelevance

/-
For _definitionally equal_ functions, `Eq.refl` suffices to
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

-- simpler case: output type does not depend on the input
abbrev Function.ext_eq_independent {α: Sort u} {β: Sort v} (f g: α → β) :=
  ∀ a, f a = g a

-- general case: output type is dependent on the input
abbrev Function.ext_eq {α: Sort u} {β: α → Sort v} (f g: (a: α) → β a) :=
  ∀ a, f a = g a

-- We can prove that this is weaker than regular equality.
theorem Function.Eq_implies_ext_eq {α: Sort u} {β: α → Sort v}:
  ∀ (f g: (a:α) → β a),
    f = g →
    Function.ext_eq f g
  := by
    intro f g heq
    cases heq
    intro a
    exact Eq.refl (f a)

-- And we can prove `ℕ.succ.ext_eq ℕ.succ_alt`,
-- because `ℕ.succ` does not normalise, but each `ℕ.succ n` does!
theorem ℕ.succ_ext_eq_succ_alt: ℕ.succ.ext_eq_independent ℕ.succ_alt := by
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

-------- using `propext` and `funext` together ----------


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


-------------- How is `funext` defined? -------

/-
`funext` could have been formulated as an axiom.
But actually, it is a theorem, derived from `Quot.sound`.
-/
#print funext
#print axioms ℕ.succ_eq_succ_alt_true
#print Quot.sound


/-
The definition `funext` is incredibly dense.

To (try and) understand it better, let's redefine
`funext`, with more details and incremental comments,
and then let's prove that it is the same as `funext`.

Claude was indespensible here because WOW we are in the weeds.
-/

theorem myFunext
  {α : Sort u} -- the (function) input type
  {β: α → Sort v} -- the output type (dependent on the input)
  {f g: (a: α) → β a} -- two dependent functions of the same type
  (ext_eq: ∀ x, f x = g x) -- extensional equality of `f` and `g`
: f = g
:= by
  -- Step 1: the equivalence relation
  let eqv: ((a: α) → β a) → ((a: α) → β a) → Prop :=
    λ f g ↦ ∀ x, f x = g x

  -- Step 2: `h` is literally a proof that `f` and `g` are `eqv`-related.
  -- No work to do here — it's already in the right shape.
  have hEqv: eqv f g := ext_eq

  -- Step 3: for a fixed argument `a`, "evaluate at `a`" is a function
  -- OUT of the quotient `Quot eqv`. This is well-defined because
  -- `eqv`-related functions agree at every `a` by definition of `eqv`.
  let evalAt: (a: α) → Quot eqv → β a :=
    λ a q ↦ Quot.lift (λ k ↦ k a) (λ f g (eqfun: eqv f g) ↦ eqfun a) q

  -- Step 4: bundle `evalAt` across all `a` into one function that,
  -- given a *fixed* quotient element `a`, reconstructs a full
  -- dependent function `(a: α) → β a`.
  let reassemble: Quot eqv → (a: α) → β a :=
    λ q a ↦ evalAt a q

  -- Step 5: reassembling `Quot.mk eqv f` gives back `f`.
  -- This holds by the computation rule for `Quot.lift`
  -- (`Quot.lift k h (Quot.mk r a)` reduces to `k a`) plus eta
  -- for dependent functions — so it's `rfl`, not extra work.
  have reassemble_mk_f: reassemble (Quot.mk eqv f) = f := rfl
  have reassemble_mk_g: reassemble (Quot.mk eqv g) = g := rfl

  -- Step 6: THE key step. `Quot.sound` turns our relation-level fact
  -- `hEqv: eqv f g` into a genuine `Eq` at the quotient type `Quot eqv`.
  -- This is the one non-definitional ingredient in the whole proof —
  -- everything else so far has been bookkeeping.
  have hq: Quot.mk eqv f = Quot.mk eqv g := Quot.sound hEqv

  -- Step 7: push `hq` through `reassemble` to move the equality
  -- from `Quot eqv` back down to `(a: α) → β a`.
  have hReassembled
  : reassemble (Quot.mk eqv f) = reassemble (Quot.mk eqv g)
  := congrArg reassemble hq

  -- Step 8: rewrite both sides using Step 5 to land on `f = g`.
  rw [reassemble_mk_f, reassemble_mk_g] at hReassembled
  exact hReassembled

theorem myFunext_eq_funext :
    @myFunext = @funext := by

  -- Yes, we use `funext` to reason about `funext` :)
  funext α β f g ext_eq

  /-
  Goal is now: `myFunext h = funext h`.
  Both sides have type `f = g`, a Prop, so this holds by
  definitional proof irrelevance.
  Honestly, I am often impressed what `rfl` can see through.
  -/
  rfl
