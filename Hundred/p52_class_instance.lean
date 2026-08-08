import Hundred.p14_constructor_functions
import Hundred.p20_currying
import Hundred.p26_structural_recursion
import Hundred.p45_predicates_and_relations

/-
Conceptually, `class` is just a keyword that defines
an `inductive` or `structure` with an annotation.
We say the type is "registered" as a _class_.

But syntactically,
- `class` is an annotated `structure`.
- `class inductive` is an annotated `inductive`.
(This reflects how the `structure` variant is typical.)

In theory these declare types as usual,
and they behave pretty much as usual.
-/
class inductive ℕClass: Type where
  | zero: ℕClass
  | succ: ℕClass → ℕClass

namespace ℕClass
  example: ℕClass → ℕClass := λn ↦ n.succ
end ℕClass

/-
But the real utility of classes is their unique
interaction with `instance` declarations.
-/

/-
On the face of it, `instance` behaves like `def`:
you use it to bind the instance of a given
(or inferred) type to a chosen name.
-/
instance egℕ₁: ℕ := ℕ.zero
def      egℕ₂: ℕ := ℕ.zero

/-
Also, `instance` behaves like `example`:
you may omit the name for the declaration.
-/
instance: ℕ := ℕ.four
example : ℕ := ℕ.four

/-
But `instance` declarations have another important effect.

For each `instance := (<term> : <type>)`, the `(type, term)` pair
becomes an entry in the _class-instance resolution table_
(optionally: also with a specified `priority: Nat`).
-/
instance: ℕClass := ℕClass.zero
instance (priority := 39): ℕClass := ℕClass.zero.succ

/-
In any context, `inferInstance` looks up the `term` associated
to the specified `type` with the highest `priority`.

You can look up the highest priority instance
for a specified class with `inferInstance`
-/
#reduce (inferInstance: ℕClass)
instance (priority := 42): ℕClass := ℕClass.zero
#reduce (inferInstance: ℕClass)

/-
Because this specialised usage of `instance` is so important,
I would argue that using `instance` to define
non-class types is generally misleading and undesirable.
-/

/-
The Lean standard library is full of class definitions,
usually for very abstract concepts.

For example, `LT: Type → Type` is defined with `class`,
so any instantiation of type `LT ℕ` would add an entry to the table!
-/
#print LT
example: Type → Type := LT
example: Type := LT ℕ
