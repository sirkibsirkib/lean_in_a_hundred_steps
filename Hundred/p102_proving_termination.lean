import Hundred.p015_matching
import Hundred.p014_constructor_functions
import Hundred.p043_inductive_parameters_vs_indices
import Hundred.p050_notation

/-
In some cases, you want to define a recursive function
which terminates, but has no _structural recursion_.
Or in any case, Lean fails to see it.

In these cases, you need to opt into completing the
function definition in three steps:
1. define the function term as usual,
2. define the _measure_ (a natural number) which decreases (`<`)
   for each recursive call, and finally,
3. prove per recursive call, that
   the measure of the parameters in function body
   `<`
   the mesure of the arguments to the recursive call.

The idea is that Lean is convinced if _some_
structure with a minimal size is decreasing per call,
because it cannot decrease forever!
-/

/-
Lean requires the _measure_ to be of the standard `Nat` type,
which we have so far approximated ourselves as `ℕ`.
Let's quickly define a conversion function `: ℕ → Nat`.
-/
def ℕNat: ℕ → Nat
  | ℕ.succ n => Nat.succ (ℕNat n)
  | ℕ.zero   => Nat.zero

instance: Coe ℕ Nat where coe := ℕNat

-- Ok now a few preliminaries ...

inductive Cmp where
  | less
  | equal
  | greater

-- Step #1: define a recursive function. Let's computes `Cmp` given two `ℕ`
def ℕ.cmp (a b: ℕ): Cmp :=
  /-
  Here it is handy to keep a proof that the match
  before `(a, b)` and after e.g. `(succ x, succ y)` are `=`.

  We do this by adding `_h: ` to the matched term.
  We don't use it here, but it is also in scope
  in the `termination_by` body below.
  -/
  match _h: (a, b) with
  | (zero  , zero  ) => Cmp.equal
  | (zero  , succ _) => Cmp.less
  | (succ _, zero  ) => Cmp.greater
  | (succ x, succ y) =>
      -- `_h : (a, b) = (x.succ, y.succ)` in scope
      cmp x y

/-
Lean considers the definition of `cmpℕ` incomplete here,
because it fails to infer that it is terminating.

It has trouble understanding the relationship between
structurally decreasing `(a, b)` and `a`.
-/

/-
Step #2: define the measure by which each recursive
call decreases. This must be of type `Nat`.
We use `ℕNat` to wrap up parameter `a`, which we see
goes from some `succ x` to `x` in the recursive call.
-/
termination_by
  ℕNat a

/-
Step #3: ok from our choice in step #2, Lean discharges
a proof obligation per recursive call.
Here we are in a context with `_h : (a, b) = (x.succ, y.succ)`,
and must prove `(ℕNat x) < (ℕNat a)`, where `<`.
-/

decreasing_by
  /-
  a b x y : ℕ
  _h : (a, b) = (x.succ, y.succ)
  ⊢ ℕNat x < ℕNat a

  where `<` here is infix notation for `Nat.lt`.
  -/
  -- from `_h` subst `a ↦ x.succ` and `b ↦ y.succ` then discard `_h`.
  cases _h
  -- rewrite `ℕNat (ℕ.succ x)` into `Nat.succ (ℕNat x)`
  simp [ℕNat]
  -- Lean magically completes the proof, because `simp` tries
  -- rewriting with many basic lemmas over `Nat`.

-- Now the definition of `cmpℕ` is complete! We can use it like any other
example: ℕ → ℕ → Cmp := ℕ.cmp

open ℕ in
example: ℕ.cmp one three = Cmp.less := by
  unfold one
  unfold three
  unfold two
  repeat unfold ℕ.cmp
  rfl

/-
But perhaps the above example was not totally convincing,
because it could be worked around by reformulating the definition.
For example, here is a function essentially similar to `cmpℕ`
in that it peels away layers from `a b: ℕ` at each recursive call.
But now we avoid `(_, _)` and expose the decreasing structure.
As a consequence, Lean automatically proves termination!
-/
def ℕ.abs_diff (a b: ℕ): ℕ :=
  match a with
  | zero => b
  | succ a' =>
    match b with
    | ℕ.zero => a
    | ℕ.succ b' => abs_diff a' b'

section ℕopened
  open ℕ

  example: abs_diff two four = two := by
    simp [abs_diff, one, two, three, four]

  example: abs_diff four two = two := by
    simp [abs_diff, one, two, three, four]


  -------------- TODO WHAT NEXT?

  theorem wah:
    ∀ a b,
      cmp a b      = Cmp.less →
      cmp a b.succ = Cmp.less
  := by
    sorry

  theorem wah2:
    ∀ a b,
      cmp a.succ b = Cmp.less →
      cmp a      b = Cmp.less
  := by
    intro a
    induction a
    . case zero =>
      intro b h
      cases b
      . exfalso
        unfold cmp at h
        contradiction
      . case succ b =>
        simp [cmp]
    . case succ a ih =>
      intro b h

      sorry

  /-
  So let's see a more complex example:

  Step #1: define the function `toward_three`:
  add or remove `succ` from `n` until `n = three`.

  This function sometimes calls with an
  _increasing_ parameter `n`,
  so obviously Lean cannot infer termination.
  -/

  def toward_three (n: ℕ): ℕ :=
    match _h: cmp n three with
    | Cmp.less    => toward_three n.succ
    | Cmp.equal   => n
    | Cmp.greater => toward_three (pred n)

  /-
  Step #2: define the decreasing measure:
    the absolute difference in number of `succ`s
    between `three` and `n`.
  -/
  termination_by
    ℕNat (abs_diff three n)

  /-
  Step #3: prove that the measure decreases
  per recursive call. Now there are two calls!
  -/
  decreasing_by
    . induction n
      . simp [abs_diff, one, two, three, ℕNat]
      . case succ n ih =>

        sorry
    . induction n
      . exfalso
        simp [three, cmp] at _h
      . case succ n ih =>

        sorry
end ℕopened
