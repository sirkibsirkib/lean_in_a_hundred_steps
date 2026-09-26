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
| refl  s   : done s = true → Bigstep s s
| trans s s': Bigstep (step s) s' → Bigstep s s'

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
abbrev Goal := (s: State) → (∃ s', Bigstep s s') → {s' // Bigstep s s'}

--------------------
-- First we need some helper definitions

-- shorthand: `a` is one step closer to done than `b`
def closer (a b: State): Prop :=
  done b = false ∧ a = step b

-- `Acc` is precisely the relation from the stdlib that we need:
-- Each `Acc < x` proves that there is no infinite chain `... < _ < _ < x`.
#print Acc
example: State → Prop := Acc closer -- `closer` is the relation `<`.

/-
Step 1:
Relate `Bigstep` and `Acc` via `closer`:
given any `s` that bigsteps to some given `s'`,
prove there is no infinite chain `... closer _ closer _ closer s`
-/
theorem acc_of_bigstep {s s': State} (h: Bigstep s s'): Acc closer s := by
  induction h
  . case refl s hd =>
      exact Acc.intro s (λ y hy ↦ absurd (hd.symm.trans hy.1) (by decide))
  . case trans s s' h ih =>
      exact Acc.intro s (λ y hy ↦ hy.2 ▸ ih)

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
  . obtain ⟨s', q⟩ := h (step s) ⟨hd, rfl⟩
    exact ⟨s', Bigstep.trans s s' q⟩
  . exists s
    constructor
    exact hd

def solve: Goal :=
  λ s h ↦ solve_helper s (h.elim λ _ hb ↦ acc_of_bigstep hb)
