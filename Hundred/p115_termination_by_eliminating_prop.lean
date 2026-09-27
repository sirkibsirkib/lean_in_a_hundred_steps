/-
Let us consider an interesting situation,
where we have to combine two gnarly features of
Lean that we addressed separately so far:
1. the quirks of when we may eliminate `Prop` into `Type`
2. convincing Lean that a recursive function that
   is not structurally descreasing is nevertheless terminating
-/

/-
To show the interesting part, let us express:
  "take an arbitrary step function over arbitrary states
  with a done-state recogniser function."

To express this we use yet more quirky features of Lean from earlier:
1. type classes
3. variables, which implicitly parametrise all definitions that use them.
2. opening namespaces to turn field projections
   into functions in the global scope
   (here `open` abbreviates `TransitionSystem.State` as `State`)
-/

class TransitionSystem where
  State: Type
  step: State → State
  done: State → Bool

variable [TransitionSystem]
open TransitionSystem
-- From now on, we work with opaque definitions of `State`, `step`, and `done`.

-- Let's introduce an inductive defintion we want to reason about:
-- `Bigstep s s'` iff `s` reaches done `s'` after any number of `step` applications.
inductive Bigstep: State → State → Prop
| refl  {s}   : done s = true  → Bigstep s s
| trans {s s'}: Bigstep (step s) s' → Bigstep s s'


/-
This is what we want to define:
- given any `s: State`
- given a _proof_ that it can bigstep to some `s'`
- return some `s'` and proof that `s` bigsteps to `s'`.

The challenge is that the definition with this type absolutely
cannot "extract" the `s'` from the given proof, because it
is trapped in `Prop` and erased at compile time.

Conceptually, the presence of the proof alone guarantees that
some `s'` must exist, but it is up to us to construct it.
The method is clear: we apply `step` until `done`,
_but how can we convince Lean that this would be terminating?_
-/
abbrev Goal := {s: State} → (∃ s', Bigstep s s') → {s' // Bigstep s s'}

/-
The tool we will use is in the standard library, called `Acc`,
used to propose and prove that for some relation,
there is no infinite chain from the given element.
`Acc` also has some hardcoded extra support to
let the Lean compiler handle its recursor
(try defining Acc yourself and it won't compile :[ )
-/
example
  {α: Sort u}          -- for any sort
  (less: α → α → Prop) -- for any `<` relation
  (x: α)               -- pick any element `x`
: Prop                 -- it is a proposition  that ...
:= Acc less x          -- ... no infinite chain `... < _ < x`.

example
  {α: Sort u} {less: α → α → Prop}   -- consider any "less than" relation
: (x: α) →                           -- pick any element `x`
  (h: (y: α) → less y x →               -- prove for each `y < x` ...
    Acc less y) →                    -- ...  no infinite chain `... < _ < y`.
  Acc less x                         -- then no infinite chain `... < _ < x`.
:= Acc.intro
/-
The idea is that you can inductively prove that
there is no infinite chain left of a given element.
- in the base case of `x`, `h` is trivial because there is no `y < x`.
- in the inductive step, you prove every `.. < y` is finite,
  hence every `.. < y < x` is finite!
-/

-- let's formulate our "less than" relation:
-- "`s'` is closer than `s`"
def closer (s' s: State): Prop :=
    step s = s'    -- `s'` is the result of stepping `s`
  ∧ done s = false -- `s` is not done

theorem closer.nah {s s'}: done s → ¬ closer s' s := by
  intro done ⟨_, not_done⟩
  rw [done] at not_done
  contradiction


/-
Prove that if `s` bigsteps to `s'` then
there are no infintely undone step chains starting from `s`.
-/
theorem acc_of_bigstep {s s': State} (big: Bigstep s s'): Acc closer s := by
  induction big
  . case refl s is_done =>
      -- `s` is already done, so construct vacuous `Acc`
      apply Acc.intro
      intro y c
      exact absurd c (closer.nah is_done)
  . case trans s s' h ih =>
      apply Acc.intro
      intro s' ⟨s_step_s', _⟩
      subst s'
      exact ih

/-
This is the heavy lifting part.
It _almost_ has the signature that we want,
but we have restructured the guarantee we are given to
a derivative of the form that we can work with, formulate via `Acc`.
-/
def solve_helper (s: State) (ac: Acc closer s): {s' // Bigstep s s'} := by
  -- destructing `ac` in `Prop` despite the result being in `Type`.
  -- it is allowed because `Acc _ _` has the shape to make this uninformative.
  induction ac
  case intro s _ h =>
  cases hd: done s
  . obtain ⟨s', q⟩ := h (step s) ⟨rfl, hd⟩
    exact ⟨s', Bigstep.trans q⟩
  . exists s
    constructor
    exact hd

def solve: Goal :=
  λ {s} h ↦ solve_helper s (h.elim λ _ hb ↦ acc_of_bigstep hb)
