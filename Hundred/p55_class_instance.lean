import Hundred.p14_constructor_functions
import Hundred.p20_currying
import Hundred.p26_structural_recursion
import Hundred.p47_predicates_and_relations

/-
Conceptually, `class` is just a keyword that defines
an `inductive` or `structure` with an annotation.
We say the type is "registered" as a _class_.

But syntactically,
- `class` is an annotated `structure`.
- `class inductive` is an annotated `inductive`.
(This reflects how the `structure` variant is typical.)
-/
class inductive ℕClass: Type where
  | zero: ℕClass
  | succ: ℕClass → ℕClass

-- First of all, these annotated types are
-- usable much like un-annotated ones.
example: ℕClass := ℕClass.zero.succ.succ

/-
But the real utility of classes is their unique
interaction with the _instance resolution table_,
which lean maintains. A partial function from types to terms.
-/

/-
`instance <name> : <type> := <term>`
adds mapping `<type> ↦ <term>` to the instance
resolution table. But it also behaves like `def` and `example`.
-/
instance whatever: ℕClass := ℕClass.zero -- like `def`
instance         : ℕClass := ℕClass.zero -- like `example`
-- either way, now `ℕClass ↦ ℕClass.zero` is in the table!

-- Use `#synth <type>` to look up the term mapped by `type`.
#synth ℕClass

-- Update the table, overwriting prior mappings
instance: ℕClass := ℕClass.zero.succ
#synth ℕClass

/-
Actually, the table has a _priority_ column as well.
Lookups return (the highest priority, defined most recently),
ordered lexicographically.
-/
instance (priority := 20): ℕClass := ℕClass.zero -- lower priority

/-
The typical use case of classes and instances is in
associating (structures which aggregate) functions to a type.

As such, the common pattern is for classes to
be parametrised by their instance.
-/
class Coolest (T: Type) where
  coolest: T

instance: Coolest ℕ where
  coolest := ℕ.four

example: ℕ := (Coolest.coolest : ℕ).succ.succ

/-
The Lean standard library is full of class definitions,
usually for very abstract concepts.

For example, `LT: Type → Type` is defined with `class`,
so any instantiation of type `LT ℕ` would add an entry to the table!
-/
#print LT
example: Type → Type := LT
example: Type := LT ℕ
