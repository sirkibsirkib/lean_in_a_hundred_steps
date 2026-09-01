import Hundred.p014_constructor_functions
import Hundred.p030_propositions

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
Lean does _not_ allow matching proofs (whose types are in `Prop`).

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

/-
Lean imposes this restriction because proofs are _erased_
during Lean's compilation to LLVM, and only "computational" values remain!

This is something worth keeping in mind!
Choose between inductive definitions in `Prop` and `Type` carefully.
-/
