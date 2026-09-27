/-
We already saw the inductive definition of a new type with
basic constructors: values of the type.
Specifically, we saw `Bit.nah : Bit` and `Bit.yep : Bit`.

Here, we show that constructors of type `T` may also be any function to `T`.
The input type may be anything defined already, or the `T` being defined!

here, `ℕ` here is the Peano encoding of the natural numbers {0,1,2,3, ...}
There are two constructors of natural numbers:
1. `zero` is a natural number
2. `succ` is a function, constructing a natural number from a given natural number.

Now it is perhaps more clear why these are called "inductive" definitions:
  Defining the type defines its values:
  the terms that can be constructed by applying the constructors
  (possibly applied to previously constructed terms).
-/
inductive ℕ: Type where
  | zero: ℕ
  | succ: ℕ → ℕ -- "successor"

-- `ℕ.zero` is a `ℕ`
example: ℕ := ℕ.zero

-- `ℕ.succ ℕ.zero` is a `ℕ`
--   because `ℕ.succ n` is a `ℕ` whenever `n` is a `ℕ`
--   and `ℕ.zero is a ℕ`.
example: ℕ := ℕ.succ ℕ.zero

/-
We can think of any value `t` of an inductive type `T` as a "proof tree",
with `t` at the root, and with some constructor at every node.

```
----------- constructor ℕ.succ
ℕ.zero : ℕ
------------------ constructor ℕ.succ
ℕ.succ ℕ.zero : ℕ
```

Later, we will see why it is not weird to think of this kind of data as a "proof",
and we will see cases of proof trees that are branching, thus more tree-like.
-/

-- For utility later, let's define some ℕ values!
namespace ℕ
  def one:   ℕ := succ zero
  def two:   ℕ := succ one
  def three: ℕ := succ two
  def four:  ℕ := succ three
end ℕ

#reduce ℕ.four
