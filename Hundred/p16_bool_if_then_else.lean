import Hundred.p01_inductive_types

/-
The Lean standard library provides `Bool`
as what you'd expect: an inductive type
with two constructors: `true` and `false`,
which are in the prelude by default.

(We will only pay it lip service here,
and then go back to modelling it with `Bit`).
-/
example: Type := Bool
example: Bool := Bool.true
example: Bool := true

-- Of course, like many things in the standard library,
-- it comes with lots of fancy methods, theorems, etc.
example: Bool := true.and false

-- As any inductive type, `Bool` can be matched.
def BoolToBit: Bool → Bit :=
  λ (b: Bool) ↦ match b with
    | Bool.true  => Bit.yep
    | Bool.false => Bit.nah

-- But `if ... then ... else` also serves this
-- purpose for `Bool`-type conditions.
example: Bool → Bit :=
  λ (b: Bool) ↦
    if b
    then Bit.yep
    else Bit.nah

/-
Later, we will see that `if ... then ... else`
can handle conditions of other types.
But this requires discussing several other Lean features first.
-/
