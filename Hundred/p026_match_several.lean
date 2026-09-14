import Hundred.p001_inductive_types
import Hundred.p015_constructor_functions

/-
Lean provides a generalisation:
each `match ... with` accepts a comma-separated
_sequence_ of terms to be matched.
Each case is thus also a comman-separated sequence.
-/

-- Here is a function matching one thing at a time
def both_zero₁: ℕ → ℕ → Bit :=
  λ a b ↦
    match a with
    | .zero =>
      match b with
      | .zero => Bit.yep
      | _     => Bit.nah
    | _     => Bit.nah

-- Here is `both_zero₁` reformulated to match two things.
def both_zero₂: ℕ → ℕ → Bit :=
  λ a b ↦
    match a, b with
    | .zero, .zero => Bit.yep
    | _    , _     => Bit.nah

/-
By using N-sequence cases,
we can generalise the def-cases pattern to N-ary functions!
-/
def both_zero₃: ℕ → ℕ → Bit
  | .zero, .zero => Bit.yep
  | _    , _     => Bit.nah

-- Indeed, you can `nomatch` a sequence of terms ...
example: Nothing → Nothing → Bit := λ a b ↦ nomatch a, b

-- ... but why would you? it suffices that one is empty.
example: Nothing → Nothing → Bit := λ a _ ↦ nomatch a
example: Nothing → Nothing → Bit := λ _ b ↦ nomatch b
