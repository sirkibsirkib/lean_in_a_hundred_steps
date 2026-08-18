import Hundred.p040_inductive_function_types

/-
Recall that structures can interleave
(default) definitions with fields.

Now with dependencies between parameters,
you can see how `structure` can really
model _modules_ and _functors_ from languages like ML and Rocq:
* a _module_ is a bundle of (inter-dependent) definitions.
* a _functor_ is a function from one module to another,
  expressed as (abstract) definitions atop some variables.
  Applying a functor to a module produces a module of (concrete) definitions.
-/

-- Here we have several abstractions coming together.
structure MaybeUtils (T: Type): Type where
  m: Maybe T
  or_default: T → T :=
    λ (default: T) ↦
      match m with
      | Maybe.none _   => default
      | Maybe.some _ t => t

example: Type → Type := MaybeUtils
example:        Type := MaybeUtils ℕ


example: {T: Type} → MaybeUtils T → T → T := MaybeUtils.or_default
example:             MaybeUtils ℕ → ℕ → ℕ := MaybeUtils.or_default

def eg_functor: Type := MaybeUtils ℕ
def eg_module: eg_functor := { m := Maybe.some _ ℕ.zero }

abbrev m := eg_module
example: ℕ → ℕ := MaybeUtils.or_default m
example: ℕ → ℕ :=          m.or_default
example:     ℕ :=          m.or_default ℕ.three

#reduce m.or_default ℕ.three
