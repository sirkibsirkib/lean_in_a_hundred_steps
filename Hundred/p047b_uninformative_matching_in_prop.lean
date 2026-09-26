import Hundred.p015_constructor_functions
import Hundred.p032_propositions

/-
Now that type parameters and indices have been introduced,
we can discuss the final wrinkle in precisely
when Lean does (not) allow destructing proofs in `Type`.

Here, the intuition that a match should be _uninformative_ is helpful.
-/

-- destructing any `Cool n` is _uninformative`_,
-- because its type already tells you the `n`;
-- all you learn is which of the constructors in {any}
-- were used to prove it! You learn nothing!
inductive Cool (n: ℕ): Prop
  | any: Cool n

example n (c: Cool n): ℕ :=
  match c with
  | .any => ℕ.three -- we learned nothing!

inductive SomeℕProp (n: ℕ) (P: ℕ → Prop): Prop
  | has: P n → SomeℕProp n P

example n (s: SomeℕProp n Cool): ℕ :=
  match s with
  | .has _pn =>
    -- we learned `Cool n` but that is another proof,
    -- so we have learned nothing yet.
    ℕ.four

/-
The following example showcases where you
_cannot_ match a proof. We still learn nothing
from knowing which constructor build the proof,
but it exposes something new: some ℕural number `n`!

This is the same reason we could not match `SomeℕExists`
-/
#print SomeℕExists

inductive SomeCool: Prop
  | this: (n: ℕ) → Cool n → SomeCool

/--
error: Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `SomeCool.casesOn` can only eliminate into `Prop`

motive : SomeCool → Sort ?u.5
h_1 : (n : ℕ) → (cn : Cool n) → motive ⋯
s✝ : SomeCool
⊢ motive s✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs in
example (s: SomeCool): ℕ :=
  match s with
  | .this n cn => sorry

/-
Here is perhaps the most subtle case;
we appear to really learn something by matching
the given `is_three` proof object, because its
destruction unconditionally exposes information about
`n`: that it is equal to `ℕ.three`.

Mechanically, this is allowed because the newly exposed
object is a proof object in `Prop`, which you might
recall, is something allowed to happen in
destructuring proofs, even within `Type`.

Conceptually, we understand that this is _still_
not really informative! It is just unwrapping
the relationship between `n` and `ℕ.three`
that is inherent given any `IsThree n`!
-/
inductive IsThree: ℕ → Prop
  | intro: IsThree ℕ.three

example n (is_three: IsThree n): ℕ :=
  match _heq: is_three with
  | .intro =>
    /-
    A proof of `n = ℕ.three` appeared in scope!
    Here `_heq: ...` is special syntax not to be confused with
    `<term> : <type>`. This is part of the `match` instruction
    informing Lean to expose the equations it discovers in the match.

    We will see it more later, when we
    get to proofs working with equality (`=`).
    -/
    let _check: Prop := n = ℕ.three
    ℕ.four
