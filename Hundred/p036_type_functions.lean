import Hundred.p001_inductive_types

/-
Lean treats terms uniformly:
  every term is a value
  every term has a type!

Where other languages offer different machinery
for defining functions at the type level,
Lean functions just act on terms, which may be types.

As such, the `λ` and `→` we have seen already
are used to define functions whose parameters
may or may not be types, all mixed together!
-/

def first_type: Type → Type → Bit → Type :=
  λ (T1 T2: Type) (b: Bit) ↦
    match b with
    | Bit.yep => T1
    | Bit.nah => T2

-- Lean does not evaluate types eagerly.
-- We need to pass a flag to opt into normalising them.
#reduce (types := true) first_type Bit Nothing Bit.yep
#reduce (types := true) first_type Bit Nothing Bit.nah

/-
But Lean does evaluate them when their outputs are necessary.
Here it normalises `first_type Bit Nothing Bit.yep` into `Bit`
to confirm that it is the type of `Bit.yep`!
-/
example: first_type Bit Nothing Bit.yep := Bit.yep

-- We will really go crazy with functions over sorts
-- after we introduce dependent types.
