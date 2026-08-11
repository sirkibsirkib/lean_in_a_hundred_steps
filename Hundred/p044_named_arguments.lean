import Hundred.p001_inductive_types
import Hundred.p014_constructor_functions

/-
When applying a function to arguments,
the mapping of arguments to (dependent) bindings
in the function type can be made explicit!

In some cases, you may want this for readability alone.
-/
def poly_constℕ: (T: Type) → (t: T) → (n: ℕ) → ℕ :=
  λ _ _ n ↦ n

example: Bit → ℕ → ℕ := poly_constℕ (     Bit) --
example: Bit → ℕ → ℕ := poly_constℕ (T := Bit) -- making the [T ↦ Bit.yep] binding explicit!

example: ℕ → ℕ := poly_constℕ (T := Bit) (t := Bit.nah)
example:     ℕ := poly_constℕ (T := Bit) (t := Bit.nah) (n := ℕ.zero)

/-
What's really cool is that you can pick out a
parameter by name, leaving all the rest unbound!

Think of this as "skipping over" bindings.
-/
example: (T: Type) → T  → ℕ := poly_constℕ (n := ℕ.zero)
example:             ℕ  → ℕ := poly_constℕ (T := Bit) (t := Bit.nah)
example:            Bit → ℕ := poly_constℕ (T := Bit) (n := ℕ.zero)

/-
Every step of the way, you have a well-formed function.
So you can interleave these with the usual positional arguments!
-/
example: ℕ → ℕ := poly_constℕ Bit (t := Bit.nah)
example: ℕ → ℕ := poly_constℕ Bit (t := Bit.nah)

example:     ℕ := poly_constℕ Bit Bit.nah (n := ℕ.zero)
example:     ℕ := poly_constℕ Bit (t := Bit.nah) ℕ.zero
example:     ℕ := poly_constℕ (T := Bit) Bit.nah ℕ.zero

/-
But what's really convenient is that, as long as you
supply them back to back, Lean is cool with you
supplying named arguments out of order!
-/
example: ℕ := poly_constℕ (T := Bit) (t := Bit.nah) (n := ℕ.zero)
example: ℕ := poly_constℕ (t := Bit.nah) (T := Bit) (n := ℕ.zero)
example: ℕ := poly_constℕ (n := ℕ.zero) (T := Bit) (t := Bit.nah)
example: ℕ := poly_constℕ (t := Bit.nah) (n := ℕ.zero) (T := Bit)
example: ℕ := poly_constℕ (n := ℕ.zero) (t := Bit.nah) (T := Bit)

example: Bit → ℕ := poly_constℕ (n := ℕ.zero) (T := Bit)

-- You can even interleave positional and named arguments ...
example: ℕ := poly_constℕ (T := Bit) (t := Bit.nah) ℕ.zero
example: ℕ := poly_constℕ (t := Bit.nah) Bit (n := ℕ.zero)
example: ℕ := poly_constℕ ℕ.zero (T := Bit) (t := Bit.nah)
example: ℕ := poly_constℕ Bit Bit.nah (n := ℕ.zero)
example: ℕ := poly_constℕ (n := ℕ.zero) Bit.nah (T := Bit)

-- And when skipped arguments are depended upon,
-- Lean will try to infer them! Here, `T := Bit` is implied.
example: ℕ → ℕ := poly_constℕ (t := Bit.nah)
example:     ℕ := poly_constℕ (n := ℕ.zero) (t := Bit.nah)

/-
Lean's system for inferring implicit (type) parameters tends to
handle named arguments well, but it can still let you down.
-/

-- This works fine
def IndexFamily (domain: Type) {codomain: Type} := domain → codomain
example:    @IndexFamily Nat Nat := λ n ↦ n

def IndexFamily'  := (domain: Type) → {codomain: Type} → domain → codomain
def IndexFamily'' := (domain: Type) → {codomain: Type} → domain → codomain

/-
But this does not work.

This does not work; It tries to elaborate `IndexFamily Nat`
before looking right of the `:=`.
`example: IndexFamily Nat     := λ n ↦ n`

In this respect, Rocq excels by elaborating the type and term together.
`Definition index_family (domain: Type) {codomain: Type} := domain -> codomain.`
`Example eg1: index_family nat := fun n => n.`
-/
