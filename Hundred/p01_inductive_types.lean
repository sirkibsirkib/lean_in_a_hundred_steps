/-
Inductive definitions define new data types
and all their _constructors_.

Let's begin with a silly version of the Booleans.
This really defines three objects into the lean universe:
1. data type `Bit`, i.e., of type `Type`
2. data `yep` of type `Bit`
3. data `nah` of type `Bit`
We call `yep` and `nah` the _constructors_ of `Bit`.

The Lean convention is that inductive types are in (upper) CamelCase,
and constructors are in (lower) snake_case.
-/
inductive Bit: Type where
  | yep: Bit
  | nah: Bit

-- You are free to define types with zero constructors
inductive Nothing: Type where

-- If there are zero constructors, the `where` is optional.
inductive Nothing': Type
