import Hundred.p015_matching
import Hundred.p058_class_instance

/-
_instance-implicit binders_     `[a: A] →` and `[A]`
are similar to implicit binders `{a: A} →` and `{A}`.

But instance-implicit binders differ in a few respects:
1. A major restriction: The bound type (`A` above) must be a class.
3. A minor restriction: `[_: ...]` is prohibited for some reason?
   Lean does not allow binding but wildcarding the binding?
2. The main point: the instances are implicitly determined
   by being looked up in the _instance-class resolution_ table!
-/
def ℕClass_is_zero: [ℕClass] → Bit :=
  λ [i: ℕClass] ↦ match i with
    | ℕClass.zero   => Bit.yep
    | ℕClass.succ _ => Bit.nah

-- Let's use an ascription to force Lean to fill in the `_:ℕClass` value!
#reduce (ℕClass_is_zero: [ℕClass] → Bit)
#reduce (ℕClass_is_zero:            Bit)

-- Let's use the surrounding context to force Lean to fill in the `_:ℕClass` value!
#reduce                       ℕClass_is_zero
#reduce (bit_flip: Bit → Bit) ℕClass_is_zero

/-
As with `{ ... }` implicit parameters,
the `[ ... ]` implicit parameters can be
made explicit by preceding the function by `@`.
-/
#reduce ( ℕClass_is_zero: [ℕClass]  → Bit)
#reduce (@ℕClass_is_zero: (ℕClass)  → Bit)
#reduce (@ℕClass_is_zero: (ℕClass)  → Bit)
#reduce (@ℕClass_is_zero ℕClass.zero: Bit)

/-
`inferInstance` Is provided as an approximation of `#synth`
It is just the 2-ary function defined as
`inferInstance: {T} → [t: T] → T := λ {T} [t: T] ↦ t`.

The standard usage `(inferInstance: T)` is really just
1. fixing the output type as `T`, forcing Lean to infer
   the value `T` as the first parameter, and then
2. Forcing Lean to infer the second parameter
   from the class-instance table!
-/

-- class `T` inferred as `ℕClass`
-- from ascribed output `ℕClass`.
-- The instance of `ℕClass` is looked up in the table.
#reduce (inferInstance: ℕClass)
#synth ℕClass

-- class `ℕClass` given explicitly.
-- The instance of `ℕClass` is looked up in the table.
#reduce (@inferInstance ℕClass _)
#synth ℕClass

-- class `ℕClass` given explicitly.
-- The instance of `ℕClass` is given explicitly.
#reduce (@inferInstance ℕClass ℕClass.zero)
#synth ℕClass

/-
From a usability perspective, there is a minor difference between:
1. functions binding class instances
2. functions binding  type instances.
-/
def ℕ__is_z: {_:ℕ}    → Bit := λ {n:ℕ     } ↦ @is_zero        n
def ℕC_is_z: [ℕClass] → Bit := λ [n:ℕClass] ↦ @ℕClass_is_zero n

-- The real difference is how the input value is inferred, at the call site.
example: Bit := bit_flip (@ℕ__is_z ℕ.zero) -- cannot be inferred here!
example: Bit := bit_flip   ℕC_is_z         -- the instance is simply looked up

/-
But what's the point of all this machinery?

The main feature here is the class-instance table.
1. The Lean compiler/interpreter maintains the table
2. The language offers a mechanism for the user to populate the table (`instance`)
3. The language offers a mechanism for triggering the lookup (`[...]` value inferred)

Next, we will see the pattern for when classes and instances are useful.
Later, we will see particular instantiation and usage of standard Lean classes.
/-

-/
Note: Lean reflects some design decisions in separating
1. data types in general
2. classes in particular
via `class` and requiring `A` in `[A]` to be a class, etc.

It is easy to imagine removing this separation.
But by keeping it, Lean type declarations signal to the reader...
- Will this type's elements be tabled and looked up?
- Would `instance` declarations for this type have any effect on `[...]` inference?
The reader understands "yes" iff the type is a class!
-/
