import Hundred.p001_inductive_types
import Hundred.p015_matching
import Hundred.p014_constructor_functions

/-
Recall these two features of Lean:
1. methods. `t.foo` abbreviates `T.foo t` when `t:T`.
   we call `t` the _receiver_.
2. parameters. Definitions parametrised by `x:X`
   effectively implicitly precede their types by `∀ x:X, `
   and implicitly         precede their types by `λ x:X ↦`.

These combine in a quirky way that is worth knowing about:
  the _receiver_ may also occur after parameters of another type.
-/

/-
Here the receiver is the _second_ argument to `ℕ.check_zero`.
so invoking the method on the receiver leaves all the
preceding parameters (`b: Bit` here) un-applied
(and then they can be applied as usual).

In practice, this relaxes the order in which
the programmer must define the parameters.
-/
def ℕ.check_zero (b: Bit): ℕ → Bit :=
  λ n ↦
    match n with
    | zero => b
    | succ _ => bit_flip b

example: Bit → ℕ → Bit := ℕ.check_zero
example:       ℕ → Bit := ℕ.check_zero .nah
example: Bit →     Bit := ℕ.zero.check_zero
example:           Bit := ℕ.zero.check_zero .nah

-- It also works when the receiver is a parameter (here, `n: ℕ`).
def ℕ.check_zero' (b: Bit) (n: ℕ): Bit :=
  match n with
  | zero => b
  | succ _ => bit_flip b

example: Bit → ℕ → Bit := ℕ.check_zero'
example:       ℕ → Bit := ℕ.check_zero' .nah
example: Bit →     Bit := ℕ.zero.check_zero'
example:           Bit := ℕ.zero.check_zero' .nah

/-
But Lean is not happy to leave arguments
that are _not_ def parameters unapplied!

In practice this means these are less useful as methods.
-/
def ℕ.check_zero'': Bit → ℕ → Bit :=
  λ b n ↦
    match n with
    | zero => b
    | succ _ => bit_flip b


example: Bit → ℕ → Bit := ℕ.check_zero''
example:       ℕ → Bit := ℕ.check_zero'' .nah
-- example: Bit →     Bit := ℕ.zero.check_zero'' -- DOES NOT WORK
example:           Bit := ℕ.zero.check_zero'' .nah

-- You can see this follows the same rules as named arguments.
-- Lean is happy to skip over named parameters!
  example: Bit →     Bit := ℕ.check_zero'  (n := ℕ.zero) -- ok!
--example: Bit →     Bit := ℕ.check_zero'' (n := ℕ.zero) -- NOT ALLOWED
