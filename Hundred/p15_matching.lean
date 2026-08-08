import Hundred.p01_inductive_types
import Hundred.p14_constructor_functions

/-
`match <t> with <cases>` lets you break
a value of a given type into its constructors.
Specifically, each case is `<pattern> => <term>`.

There are two conditions that Lean will enforce
1. Together, the patterns must match every conceivable
   value of the matched type, i.e., they are exhaustive.
2. The terms in each case have the same type.

The idea is that the `match x with ...`
defines the resulting value depending on the value `x`.
-/

-- Simple case: match on a constant
example: Bit :=
  match Bit.nah with
  | Bit.nah => Bit.yep
  | Bit.yep => Bit.nah

-- Match on the value of a function argument
def bit_flip: Bit → Bit :=
  λ (b: Bit) ↦
    match b with
    | Bit.nah => Bit.yep
    | Bit.yep => Bit.nah

-- When a case is a constructor function,
-- you also include a (new) binding for the function parameter!
def pred: ℕ → ℕ :=
  λ (n: ℕ) ↦
    match n with
    | ℕ.zero    => ℕ.zero
    | ℕ.succ n' => n' -- when `n` is some `n'.succ`, return `n'`.

/-
You can omit the type but keep the preceding `.`
to mark it as a constructor of some type to be inferred,
to avoid Lean confusing it with a fresh name binding
-/
def bit_flip_alt: Bit → Bit :=
  λ (b: Bit) ↦
    match b with
    | .nah => Bit.yep
    | .yep => Bit.nah

/-
You can avoid naming a binding in a case
by using a wildcard `_` instead of a name.
-/
def is_zero: ℕ → Bit :=
  λ (n: ℕ) ↦
    match n with
    | .zero   => Bit.yep
    | .succ _ => Bit.nah
