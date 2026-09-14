import Hundred.p015_constructor_functions
import Hundred.p016_matching
open ℕ

/-
Like `inductive`, `structure` defines an inductive datatype.
But there is just _one_ constructor, and its parameters are named.
These parameters are called _fields_ of the structure type.
-/
structure ℕPair: Type where
  mk:: -- (optional: naming the constuctor `: ℕ → ℕ → ℕPair`)
  a: ℕ -- param #0
  b: ℕ -- param #1

example: ℕ → ℕ → ℕPair := ℕPair.mk
example:          ℕPair := ℕPair.mk ℕ.zero ℕ.two

/-
Naming the constructor is optional, because
any record `{ <name₁> := <term₁> , <name₂> := <term₂>, ... }`
with precisely the rightly named and typed fields
also constructs an element of the structure type.
-/
def eg: ℕPair := { a := ℕ.zero, b := ℕ.two }

-- Conveniently, the names let you re-arrange the fields.
example: ℕPair := { b := ℕ.two, a := ℕ.zero }

/-
Also conveniently, the declaration of each field name
doubles as the definition of a _projection function_
from a structure value to that field value,
in the namespace of the type.
-/
example: ℕPair → ℕ := ℕPair.a
example: ℕPair → ℕ := ℕPair.b

/-
Also quite cool: you may give _default value_
to any fields by following their declaration with `:= <term>`.
Omitting these from the construction `{ ... }` uses the default.

As with sequences of definitions, later default values
can depend on earlier ones!
(Of course you can do this 'by hand' in the `{ ... }` too.)
-/

structure Clump: Type where
  p: ℕPair
  b: Bit   := is_zero p.a

#reduce ({ p := eg, b := Bit.nah } : Clump)
#reduce ({ p := eg               } : Clump).b
