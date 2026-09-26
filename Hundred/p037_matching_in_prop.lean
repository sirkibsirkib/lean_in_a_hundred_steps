import Hundred.p015_constructor_functions
import Hundred.p032_propositions

/-
When defining data (whose types are in `Type`),
Lean allows matching other such data.
-/
example: ℕ → Bit := λ
  | ℕ.zero => Bit.nah
  | _      => Bit.yep

/-
When defining proofs (whose types are in `Prop`),
Lean allows matching other proofs.
-/
example: ℕsExist → SomeℕExists := λ
  | ℕsExist.final   x   => x
  | ℕsExist.another x _ => x

/-
When defining proofs (whose types are in `Prop`),
Lean allows matching data (whose types are in `Type`).
-/
example: ℕ → SomeℕExists := λ (n: ℕ) ↦
  SomeℕExists.this_one
    (match n with
    | ℕ.zero => ℕ.zero
    | _      => ℕ.one)

/-
_However_, when defining data (whose types are in `Type`),
Lean does _not_ generally allow matching proofs (whose types are in `Prop`).

Here are examples of (functions constructing) proofs
which take data as input, but crucially, no proof is matched!
-/
example: SomeℕExists → ℕ := λ _ ↦ ℕ.zero

-- While it seems similarto the above,
-- Lean rejects the following definition.

/--
error: Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `SomeℕExists.casesOn` can only eliminate into `Prop`

motive : SomeℕExists → Sort ?u.6
h_1 : (n : ℕ) → motive ⋯
x✝ : SomeℕExists
⊢ motive x✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs (whitespace := lax) in
example: SomeℕExists → ℕ
  | SomeℕExists.this_one n => n

example: SomeℕExists → ℕ := λ _ ↦ ℕ.zero

/-
Lean imposes this restriction because proofs are _erased_
during Lean's compilation to LLVM, and only "computational" values remain!

This is something worth keeping in mind!
Choose between inductive definitions in `Prop` and `Type` carefully.

This perspective also explains the cases where you _can_
eliminate from Prop to Type: when it is a singleton constructor
that exposes only more values in Prop!

The rough intuition is that destructing such a structure
is _uninformative_: it reveals no information
that could not be inferred from just having
the entire structure in the first place.
-/

-- Here, we can destruct `Uninformative: Prop` to build `Nat: Type`
inductive Uninformative: Prop
  | uninformative (t: True) (f: False) (s: SomeℕExists)

example (u: Uninformative): Nat :=
  match u with
  | .uninformative t _f _s => -- learned nothing
    match t with
    | .intro => /- learned nothing again -/ 5

/-
Unfortnately, Lean is sometimes too conservative
about which values are informative when matched.
Here, from its definition, we see that `Trivial`
values carry no data (they are isomorphic to `True`),
but Lean forbids us from destructing a `Uninformative'` to expose a `Trivial`.
Fortunately, I have not yet encountered such a case I could not work around.

What Lean enforces is more like:
  destructing a single-constructor proof containing only
  other proofs, is permitted, even within `Type`.
But later we will see even this needs refining.
-/
inductive Trivial: Type
  | intro
inductive Uninformative': Prop
  | uninformative (t: Trivial)

/--
error: Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Uninformative'.casesOn` can only eliminate into `Prop`

motive : Uninformative' → Sort ?u.5
h_1 : (t : Trivial) → motive ⋯
u✝ : Uninformative'
⊢ motive u✝ after processing
  _
the dependent pattern matcher can solve the following kinds of equations
- <var> = <term> and <term> = <var>
- <term> = <term> where the terms are definitionally equal
- <constructor> = <constructor>, examples: List.cons x xs = List.cons y ys, and List.cons x xs = List.nil
-/
#guard_msgs in
example (u: Uninformative'): Nat :=
  match u with
  | .uninformative t => 4 -- we learn nothing from `t` but Lean is not convinced
