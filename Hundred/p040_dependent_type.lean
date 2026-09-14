import Hundred.p001_inductive_types

/-
Recall that function `λ (a: A) ↦ (b: B)` binds some
argument of type `A` to name `a`, such that
the resulting `b` term can depend on `a`.
-/
example := λ (b: Bit) ↦ b

/-
We have thus far seen that the type of each
`λ (a: A) ↦ (b: B)`
is
`A → B`
as in Haskell, and others.

But actually, the input value can be
bound to a name inside in the type, too!
The type of each `λ (a₁: A) ↦ (b: B)`
is actually some `  (a₂: A) → (B: Sort u)`

The `A → B` we have seen until now
is actually just shorthand for the special case `(_:A) → B`.
-/
example:     Bit  → Bit := λ (b: Bit) ↦ b
example: (_b:Bit) → Bit := λ (b: Bit) ↦ b

/-
This feature is called _dependent types_:
- syntactically, in function type `(a: A) → B`, `B` can contain `a`.
- semantically, the output type can depend on the input value.

Let's define a polymorphic identity function!
Here, the function has input `T: Sort u`,
and the output type (and thus value) `T → T` clearly depends on it!
-/
def identity: (T: Type) → (T → T) := λ _ t ↦ t
example: (T: Type) → T → T := identity
example: Bit → Bit := identity Bit
example: Bit := identity Bit Bit.nah

/-
Where the above let Lean infer the types of
the `λ` binders from the name type declaration,
the below does the opposite.
-/
def identity' := λ (T: Type) (t: T) ↦ t

/-
But as usual, the left and right of `→` are
not limited to defined names! Feel free to compute there!
Now with dependencies! Here `identity _ P` reduces to `P`!
-/
theorem prop_identity: (P: Prop) → P → (identity _ P) :=
  λ _ p ↦ p

-- You can get a little crazy!
example :=  (f: Type → Type) → (T: Type) → f T

/-
Now that inputs to functions are inter-dependent,
Lean is able to infer some inputs from others,
so `_` becomes an acceptable _value_ give as input to functions!
-/
example: Bit := identity Bit Bit.nah
example: Bit := identity _   Bit.nah
