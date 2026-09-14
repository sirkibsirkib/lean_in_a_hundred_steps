import Hundred.p015_constructor_functions

/-
Recall the type of a function
`λ(_:A) ↦ (b:B)` is the "function type" term `A → B`.

But what is the type of such a function type?

Here, once again, `Prop` (AKA `Sort` AKA `Sort 0`)
is given special treatment.

The definition is thus:
The type of `a → b` where `a: Sort i` and `b: Sort j` is:
  if `j=0` (i.e., `b: Prop`)
    then `Sort j`
    else `Sort (max i j)`

Let's see some examples.
-/

-- "then" case: fun type = out type
example: Sort 0 := (ℕ     : Sort 1) → (True: Sort 0)
example: Sort 0 := (Sort 3: Sort 4) → (True: Sort 0)
example: Sort 0 := ((Sort 0 → Sort 1): Sort 2) → (True: Sort 0)
example: Sort 0 := ((Sort 1 → True  ): Sort 0) → (True: Sort 0)

-- "else" case: fun type = max (in type) (out type)
example: Sort 5 := (Sort 4: Sort 5) → (ℕ: Sort 1)
example: Sort 1 := (True  : Sort 0) → (ℕ: Sort 1)
example: Sort 2 := ((Sort 0 → Sort 1): Sort 2) → (Sort 0: Sort 1)

-- Where "then" and "else" cases agree:
example: Sort 0 := (True: Sort 0) → (True: Sort 0)
example: Sort 1 := (ℕ            ) → (ℕ: Sort 1)
example: Sort 1 := (True  : Sort 0) → (ℕ: Sort 1)
example: Sort 1 := (Sort 0: Sort 1) → (Sort 0: Sort 1)
example: Sort 2 := (Sort 0: Sort 1) → (Sort 1: Sort 2)
example: Sort 8 := (Sort 5: Sort 6) → (Sort 7: Sort 8)

/-
Originally I was thrown by the following:
  "Why does ascribing the `ℕ` with its type
   seem to change the function type?"

Actually, what's going on is that lean's parser
is confused between two readings of `(ℕ: Sort 1)`:
1. term `ℕ` ascribed with its type `Sort 1` (what I intended)
2. a binder named `ℕ` of the type `Sort 1` (what Lean misreads here).

Explaining why in `(a: A) → B` it makes sense to read `a`
as a binder, we need to dive into _dependent types_! (up next)
-/
example  : Sort 1 :=  ℕ          → Sort 0
def weird: Sort 2 := (ℕ: Sort 1) → Sort 0
#print weird
