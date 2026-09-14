import Hundred.p015_constructor_functions

/-
We already saw `Type` and `Prop` as data types and propositions.
These are generalised as `Sorts`.
* `Prop` is just an abbreviation for `Sort 0`.
* `Type` is just an abbreviation for `Sort 1`.
-/
example: Prop   := True
example: Sort 0 := True
example: Type   := ℕ
example: Sort 1 := ℕ

/-
Another big idea under Lean is that even types have types!
There is an infinite sequence of them, and `Sort u: Sort (u + 1)`.
This parameter `u` is called the "universe level".

Unfolding abbreviations demystifies the following:
-/
example: Type   := Prop
example: Sort 1 := Sort 0

-- And, as promised, even Type has a Type!
example: Sort 2 := Type
example: Sort 2 := Sort 1

-- `Sort` itself is an abbreviation of `Sort 0`.
example: Sort 1 := Sort

/-
In fact, `Type` is an abbreviation of `Type 0`,
and `Type n` in general is an abbreivation of `Sort (n + 1)`.
It's all sorts all the way down!

These aliases allow for two coexisting views on the sort hierarchy:
* when we want to single out `Prop`, the hierarchy is `Prop : Type 0 : Type 1 : ...`
* when we lump them all together,    the hierarhcy is `Sort : Sort 1 : Sort 2 : ...`
-/
example: Type 1 := Type
example: Type 1 := Type 0
example: Type 1 := Sort 1

/-
Thankfully for my point here, Lean allows
implicit parameters for these universe levels,
and automatically handles basic arithmetic with universes.
-/
example: Type n       := Sort n
example: Sort (n + 1) := Sort n
example: Type (n + 1) := Sort (n + 1)
example: Type (n + 9) := Sort (n + 1 + 8)

/-
The sort hierarchy is necessary to ensure that we cannot define any `U: U`,
otherwise, we get into Russel's and Girard's paradoxes.
The idea is that no term / type is expressed that can contain itself.

I failed to produce a compelling example, but take my word for it.
-/

/-
`inductive` lets you define new types of any sort!
But I have never needed to do so.

Later we will see that you encounter values in these higher sorts
by building functions over sorts.
-/
inductive Binkus: Sort 4 where
  | Bar: ℕ → Binkus
