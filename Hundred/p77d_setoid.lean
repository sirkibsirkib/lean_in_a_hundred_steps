import Hundred.p77c_equivalence

/-
Conceptually, instantiating class `Setoid T`
equips your chosen type `T`
with a canonical equivalence relation.
https://en.wikipedia.org/wiki/Setoid

Mechanically, your instance `i: Setoid T` defines
1. `i.r` the endorelation over `T`
2. a proof of `Equivalence i.r`.

This relation is _canonical_ in the sense that,
by being defined as a class,
you are mapping `T → I` via the instance-resolution table.
Some standard utilities then can do `[i: Setoid T]` to
acquire the setoid, to reason about it or whatever.

The prelude defines `a ≈ b` as notation for `Setoid.r a b`.
-/
#print Setoid

-- Let's define it for `ℕPair`.
instance SetoidℕPair: Setoid ℕPair where
  r := ℕPair.same_sum
  iseqv := ℕPair.same_sum_Equivalence

-- Recall, this is a `structure` instance as usual.
#reduce SetoidℕPair.r

-- And Lean can resolve the setoid over `ℕPair`.
#synth   Setoid ℕPair
#reduce (@Setoid.r ℕPair)
