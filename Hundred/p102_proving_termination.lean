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

/-
Let's consider a simple case:
let's define `ℕ.cmp`, a recursive comparator of `ℕ` pairs,
and prove that this function terminates.
-/

inductive Cmp where | less | equal | greater

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
  unfold ℕ.cmp
  unfold ℕ.cmp
  rfl

/-
But perhaps the above example was not totally convincing,
because it could be worked around by reformulating the definition.

Here is `ℕ.cmp'` which
1. we prove is definitionally equivalent to `ℕ.cmp`, but
2. is reformulated such that Lean _does_ see that it terminates.
  The trick is subtle: we match a pair `a, b` rather than matching
  a tuple `(a, b)` that we construct and then deconstruct on the fly.
-/
def ℕ.cmp' (a b: ℕ): Cmp :=
  match a, b with
  | zero  , zero   => Cmp.equal
  | zero  , succ _ => Cmp.less
  | succ _, zero   => Cmp.greater
  | succ x, succ y => cmp' x y

#print Nat.lt

#print Nat.lt

theorem ℕ.cmp_less_implies_lt_ℕNat:
  ∀ a b,
    ℕ.cmp a b = Cmp.less →
    ℕNat a < ℕNat b
:= by
  intro a b h
  induction a generalizing b with
  | zero =>
    cases b
    . unfold cmp at h
      cases h
    . exact Nat.succ_pos _
  | succ a ih =>
    cases b
    . rw [ℕ.cmp] at h
      contradiction
    . case succ b' =>
      rw [ℕ.cmp] at h
      have hb': a.cmp b' = Cmp.less := h
      have hlt: ℕNat a < ℕNat b' := ih b' hb'
      rw [ℕNat, ℕNat]
      exact Nat.succ_lt_succ hlt

theorem ℕ.lt_ℕNat_impl_cmp_less:
  ∀ a b,
    ℕNat a < ℕNat b →
    ℕ.cmp a b = Cmp.less
:= by
  intro a b
  induction a generalizing b with
  | zero =>
      intro h
      cases b with
      | zero =>
          rw [ℕNat] at h
          exact absurd h (Nat.lt_irrefl 0)
      | succ b' => rw [ℕ.cmp]
  | succ a' iha =>
      intro h
      cases b with
      | zero =>
          rw [ℕNat, ℕNat] at h
          contradiction
      | succ b' =>
          rw [ℕNat, ℕNat] at h
          have h' : ℕNat a' < ℕNat b' := Nat.lt_of_succ_lt_succ h
          have hcmp : a'.cmp b' = Cmp.less := iha b' h'
          rw [ℕ.cmp]
          exact hcmp

/-
So let's see a more complex example:

Step #1: define the function `toward_three`:
add or remove `succ` from `n` until `n = three`.

This function sometimes calls with an
_increasing_ parameter `n`,
so obviously Lean cannot infer termination.
-/
def ℕ.abs_diff: ℕ → ℕ → ℕ
  |    zero,      b  => b
  |      a ,    zero => a
  | succ a', succ b' => a'.abs_diff b'

def ℕ.sub : ℕ → ℕ → ℕ
  | a,        .zero    => a
  | .zero,    .succ _  => .zero
  | .succ a', .succ b' => sub a' b'

theorem ℕ.sub_eq: ∀ a b, ℕNat (a.sub b) = ℕNat a - ℕNat b := by
  intro a b
  induction a generalizing b with
  | zero => cases b <;> simp [ℕ.sub, ℕNat]
  | succ a' iha =>
    cases b with
    | zero    => simp [ℕ.sub, ℕNat]
    | succ b' =>
      have hi := iha b'
      simp only [ℕ.sub, ℕNat]
      omega

def ℕ.div (a b : ℕ) : ℕ :=
  if hb : ℕNat b = 0 then
    .zero
  else if h : ℕNat a < ℕNat b then
    .zero
  else
    .succ (ℕ.div (a.sub b) b)

termination_by
  ℕNat a

decreasing_by
  rw [ℕ.sub_eq a b]
  omega
