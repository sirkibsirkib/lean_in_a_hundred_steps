import Hundred.p14_constructor_functions
import Hundred.p20_currying

/-
In Lean, we must disambiguate two related but distinct meanings of _type_:
Here we need to disambiguate things (from the Lean perspective).
You will encounter both in the literature,
and the confusion comes from their significant but not total overlap.
Ideally, we would use different words for these things, but oh well.

_Firstly, type-of is a relation over terms, whose codomain is "types"._
For example because `ℕ.zero: ℕ` and `True: Prop` and `Sort 3: Sort 4`,
{`ℕ`, `Prop`, `Sort 4`} are types.

This meaning is relevant in some places.
Notably, it is relevant to when `a → b` is well-formed:
precisely when `a` and `b` are types.
-/
example := ℕ → ℕ      -- `ℕ` is a type (e.g., of `ℕ.zero`)
example := Prop → Prop -- `Prop` is a type (e.g., of `True`)
-- `example := ℕ.zero → ℕ.zero` -- this is ill-formed; `ℕ.zero` is not a type.

/-
_Secondly, type is the set of terms whose type is `Type _`._

This second meaning is stricter.
For example, meaning #1 but not #2 includes `True`,
because `True: Prop`.

Henceforth, we mean "_ is a type" as the _first_ meaning.
Where the stricter _second_ meaning is meant instead,
we will say "_ with the type `Type 2`" or whatever.
-/

/-
The two meanings diverge on the universe of `Prop`.
You will see (soon) that `Prop` is given some special treatment.
-/
