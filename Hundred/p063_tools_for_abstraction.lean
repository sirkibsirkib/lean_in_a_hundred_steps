import Hundred.p015_constructor_functions

/-
The tools we have seen so far offer many ways
to solve the same _abstraction_ pattern:
1. Let's define a bundle of definitions now,
  which are parametrised by some variables.
2. Let's concretise those abstractions
  by filling in the variables with concrete terms.

As a running example of #1, let's take:
  for some "incrementable" thing, lets define
  a function which increments it twice!
-/

/-
Approach #1: Variables as parameters.

Function parameters are all we need to
define abstract terms; our "variables" are parameters!
And more variables that are more entangled is
no problem. Currying and dependent types handle it!
-/
def inc_twice:
    (T: Type) → -- for any type `T`
    (inc: T → T) → -- and a function `inc` that increments `T` values
    (_inc_neq: ∀ t, inc t ≠ t) → -- where `inc` is injective ..
  T → T := -- we can define a 2-increment function!
    λ _ inc _ a ↦ inc (inc a)

/-
Obtaining an instance of our abstraction just requires
filling in all the parameters.
-/

def ℕsucc_neq (n: ℕ): n.succ ≠ n := nofun

def inc_twice_ℕ: ℕ → ℕ :=
  inc_twice
    ℕ
    ℕ.succ
    ℕsucc_neq

-- We can use the concrete instance just fine.
#reduce inc_twice_ℕ ℕ.zero

/-
Approach #2:
Same as #1 but group the variables into one term.
A `structure` is natural, because then you
can easily name the variables individually, as before.

Specifically:
1. Group the variables into a type, e.g., a `structure`.
2. Define the abstract term as a function
   parametrised by an instance of the structure type.
3. Select variables by constructing an instance.
4. Obtain a concrete term: apply the function to the instance.
5. (optional) use the concrete term.
-/

-- step 1: define variables
structure IncStruct (T: Type) where
  inc: T → T
  inc_neq: ∀ t, inc t ≠ t

-- step 2: abstract definition(s)
def inc_twice': (T: Type) → IncStruct T → T → T :=
  λ T (i: IncStruct T) (t: T) ↦ i.inc (i.inc t)

-- step 3: instantiate the variables
def IncStructℕInstance: IncStruct ℕ := {
  inc     := ℕ.succ
  inc_neq := ℕsucc_neq
}

-- step 4: apply the function to the instance
def ℕinc_twice': ℕ → ℕ :=
  inc_twice' ℕ IncStructℕInstance

-- step 5: use the concrete term
#reduce ℕinc_twice' ℕ.zero

/-
Approach #3:
Same as #2 but register the variables-type as a _class_.
Really just the application of function is done differently.
-/

-- step 1: define variables
class IncClass (T: Type) where
  inc: T → T
  inc_neq: ∀ t, inc t ≠ t

-- step 2: abstract definition(s)
def inc_twice'' (T: Type) [i: IncClass T]: T → T :=
  λ a ↦ i.inc (i.inc a)

-- step 3: instantiate the variables
instance IncClassℕInstance: IncClass ℕ where
  inc := ℕ.succ
  inc_neq := ℕsucc_neq

-- step 4: apply the function to the instance
-- (here is the change from approach #2 to #4)
def ℕinc_twice'': ℕ → ℕ :=
  inc_twice'' ℕ -- IncClassℕInstance passed implicitly!

-- step 5: use the concrete term
#reduce ℕinc_twice'' ℕ.zero

/-
A historical note: Lean is reflecting in `structure` vs `class`
the products of two schools of thought for handling abstraction.

## The explicit approach
(Approach #2, using `structure`).

The programmer explicitly chooses
how to concretise the abstraction each time.

This approach shines when fine control of
the instantiation is required.
For example, when the same abstraction
is applied in a lot of different ways.

For example, ML and Rocq mostly reflect this approach,
offering _module types_ as clusters of variables,
_modules_ as instantiations of those variables,
and _functors_: module-level functions,
whose input is a module of a given type,
and whose output is a concrete module.

## The implicit approach
(Approach #2, using `class`).

The programmer defines an instance somewhere,
and then the tools automate the filling in
of the variables wherever they are needed.

This approach shines when the mapping of
classes to instances does not change (much),
so it makes sense to define it once and implicitly
thread the instance everywhere it is needed!

For example, Haskell and Rust mostly reflects this approach,
offering _type classes_ and _traits_ as clusters of
variables, and _implementations_ as instantiations of those variables
concretising any definitions parametrised by constrained types.
-/

/-
Lean offers non-class types and class types as
mechanisms to use both approaches (as many languages do).
But arguably, `class` and `instance` and `[...]`
mostly affording the implicit approach, but also
allowing the user to opt into explicit control by
1. _naming_ the instances, so they can be passed around, and
2. letting `@` coerce implicit `[...]` into explicit `(...)`
   so the caller can pass in instances of their choice as needed.
-/

/-
Using standard utilities (e.g., classical choice)
and notations (e.g., `x + y`) requires instantiating
classes from the Lean standard library.

We will focus on using `Add` and `LT` and `Decidable` later.
-/
