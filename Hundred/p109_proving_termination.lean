import Hundred.p016_matching
import Hundred.p015_constructor_functions
import Hundred.p045_inductive_parameters_vs_indices
import Hundred.p053_notation
import Hundred.p108_nat

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
First, let's consider a simple case:
  `ℕ.cmp` recursively compares `ℕ` pairs.
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

-- Now the definition of `cmpℕ` is complete! We can use it like any other.
-- Let's compute with `cmpℕ`!
#reduce ℕ.zero.cmp ℕ.two
#reduce ℕ.four.cmp ℕ.four
#reduce ℕ.four.cmp ℕ.three

open ℕ in example: ℕ.cmp one three = Cmp.less :=
  by simp [one, two, three, cmp]

-- Let's build definitions atop `cmpℕ`!
theorem ℕ.cmp_greater_lt: ∀ a b, a.cmp b = Cmp.greater → ℕNat b < ℕNat a
  | .zero,    .zero,    h => by rw [ℕ.cmp] at h; contradiction
  | .zero,    .succ _,  h => by rw [ℕ.cmp] at h; contradiction
  | .succ _,  .zero,    _ => by simp [ℕNat]
  | .succ a', .succ b', h => by
      rw [ℕ.cmp] at h
      have ih := ℕ.cmp_greater_lt a' b' h
      simp only [ℕNat]
      exact Nat.succ_lt_succ ih

/-
Sometimes, getting Lean to recognise termination is
just a matter of tweaking the encoding.

Below, we define `ℕ.cmp'` as equal to `ℕ.cmp`
but where
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

theorem ℕ.cmp_eq_cmp': ℕ.cmp = ℕ.cmp' := by
  funext m n
  induction m generalizing n with
  | zero       => cases n <;> simp [cmp, cmp']
  | succ m ihm => cases n <;> simp [cmp, cmp', ihm]

/-
But sometimes you see no way to rewrite your
term such that Lean proves termination automatically.
You may need a more subtle measure, or a more
sophisticated proof that your measure decreases.
Here's an example of the latter.
-/

def ℕ.div (a b: ℕ) (hnz: b ≠ zero): ℕ :=
  match _h: a.cmp b with
  | .greater => succ <| (a - b).div b hnz
  | _        => zero

termination_by ℕNat a
decreasing_by
  have altb: ℕNat b < ℕNat a := ℕ.cmp_greater_lt a b _h
  have zltb: 0 < ℕNat b := by
    cases b
    . exact hnz.elim rfl
    . simp only [ℕNat]; exact Nat.succ_pos _
  have zlta: 0 < ℕNat a := Nat.lt_trans zltb altb
  rw [ℕNat_distributes_over_sub a b]
  exact Nat.sub_lt zlta zltb
