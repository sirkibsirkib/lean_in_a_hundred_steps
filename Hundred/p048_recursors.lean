import Hundred.p001_inductive_types
import Hundred.p017_constructor_functions
import Hundred.p034_propositions
import Hundred.p044_inductive_function_types
import Hundred.p047_inductive_parameters_vs_indices

/-
For each inductive data type that you define,
Lean auto-generates a _recursor_ function.

The shape of the recursor reflects the constructors of that type.

Intuitively, the `T`-recursor is defined for any `T`-property
(conventionally called a "motive" for some reason),
it consumes a proof for each constructor:
- prove that the construction has the property ...
  given an _induction hypothesis_ per parameter _of type `T`_:
    that the parameter already has the property
and it produces a proof that every value in `T` has the property.

This is the structure of traditional _inductive proofs_,
which argue that every element of a set has `T` if
- _base case_: the smallest objects have `T`, and
- _inductive step_: whenever any object has `T`, the next ones have `T`

Later we will see the `induction` proof tactic,
which actually interally applies the type's recursor function!
-/
#print ℕ.rec
noncomputable example:
  {motive: Bit → Sort u} → -- given any property of Bit
  motive Bit.yep         → -- proven for .yep
  motive Bit.nah         → -- proven for .nah
  (b: Bit) → motive b      -- acquire a proof that every `Bit has it!
:= Bit.rec

#print Bit.rec
noncomputable example:
  {motive: ℕ → Sort u}                → -- given any property of ℕ
  motive ℕ.zero                       → -- proven for ℕ.zero
  ((n: ℕ) → motive n → motive n.succ) → -- proven for n.succ given it for n
  (n: ℕ) → motive n                     -- acquire a proof for each ℕ
:= ℕ.rec

def SomeBitLyst: ℕ → Type :=
  λ n ↦ LenLyst Bit n

noncomputable example:
  SomeBitLyst ℕ.zero                            → -- proven for ℕ.zero
  ((n: ℕ) → SomeBitLyst n → SomeBitLyst n.succ) → -- proven for n.succ given it for n
  (n: ℕ) → SomeBitLyst n                          -- acquire a proof for each ℕ
:= @ℕ.rec
  SomeBitLyst

noncomputable example:
  ((n: ℕ) → SomeBitLyst n → SomeBitLyst n.succ) → -- proven for n.succ given it for n
  (n: ℕ) → SomeBitLyst n                          -- acquire a proof for each ℕ
:= @ℕ.rec
  SomeBitLyst
  LenLyst.nil

noncomputable example:
  (n: ℕ) → SomeBitLyst n -- acquire a proof for each ℕ
:= @ℕ.rec
  SomeBitLyst
  LenLyst.nil
  (λ _n l ↦ l.cons Bit.nah)

noncomputable example:
  SomeBitLyst ℕ.four  -- acquire a proof for the chosen ℕ
:= @ℕ.rec
  SomeBitLyst
  LenLyst.nil
  (λ _n l ↦ l.cons Bit.nah)
  ℕ.four
