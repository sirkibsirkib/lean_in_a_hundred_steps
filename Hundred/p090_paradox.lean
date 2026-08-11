
/-
Lean would reject the following definition
`inductive P: Prop where`
`  | intro: Not P → P   `
with
`(kernel) arg #1 of 'P.intro' has a non positive`
`occurrence of the datatypes being declared`.

This _restriction_ ensures that `inductive`
definitions preserve Lean's soundness
(that `False` cannot be proved).

If this definition of `P` was not rejected,
here is how we could prove `False`:
1. prove `np: Not P`, i.e, "assuming `P` implies `False`"
  a. take any given `p: P`, it suffices to show `False`
  b. destructure `p` via the only constructor
    into `P.intro (np: P → False)`.
  c. apply `np` to `p`.

2. prove `P`, i.e., "there exists some `P`"
  a. apply `P.intro` to `np` from step #1.

3. prove `False`, "there is an inconsistency"
  b. apply `np` to `p`.

Conceptually, the issue that Lean allows us to
reason backward and forward from proofs of propositions
and all of their possible constructors.
Step 1b destructed  `P` via `P.intro` to obtain  `¬P`.
Step 2a constructed `P` via `P.intro` applied to `¬P`.
So effectively, this inductive proposition asserted `P ↔ ¬P`.

We cannot express the above in Lean,
but we can approximate it in a theorem:
  "for any `P`, `P ↔ ¬P` is contradictory!
-/

theorem p_iff_p_inconsistent:
  ∀ (P: Prop),
    (P ↔ ¬P) → False
:= by

  -- split the `↔` into `←` and `→`.
  intro P ⟨l, r⟩

  -- step 1: `¬P`
  obtain np: ¬P := by
    intro p
    unfold Not at l
    exact l p p

  -- step 2: `P`
  obtain p: P := by
    exact r np

  -- step 3: `False`
  exact np p

/-
More generally, Lean's _restriction_ is as follows:

For a set of types {`T1`, `T2`, ... , `Tn`} mutually defined
For each constructor `c: X1 → X2 → ... Xn → Ti`,
  `Xj` cannot be a function `Y1 → Y2 → ... → Tk → ...`.

For example, the following is also rejected
with `Ti := Foo` and `Xj := Foo' → Bool`.

`mutual                               `
`  inductive Foo where                `
`    | foo: Foo → (Foo' → Bool) → Foo `
`  inductive Foo' where               `
`    | foo: Foo' → (Bool → Foo) → Foo'`
`end                                  `

But, for example, it would be accepted if
`Foo' → Bool` was edited to `Bool → Bool`,

But externally we can reason that
`Foo` and `Foo'` pose no threat to consistency.
Unfortunately, Lean's _restriction_
is an over-approximation of the more
precise (undecidable) property of
"inductive definitions which imply `False`".
-/

/-
This _restriction_ (and some others) prevent
us from ruining consitency via `inductive`.
But we can still "work with inconsitency" in other ways:

1. We can _propose_ whatever we want (including `P ↔ ¬P`),
  because proving such a proposition is another matter.

2. We can reason _ad absurdum_ by working in contexts
  assuming that any proposition is true / type is inhabited.
  (as we did in `p_iff_p_inconsistent`).

3. A small step from #2 is choosing any
  `variable`, making any assumption,
  at the risk of polluting definitions in scope
  with inconsistency (trivialising those results).

4. A small step from #3 is choosing any
  `axiom`, globally asserting our assumption,
  at the risk of polluting our whole codebase
  with inconsistency (trivialising all results).
-/
