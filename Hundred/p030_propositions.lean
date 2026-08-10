import Hundred.p001_inductive_types
import Hundred.p014_constructor_functions

/-
Lean (like Rocq and others) is founded on the _constructivist_
philosophy, whose central idea is that data types _are_ logical propositions,
and terms of those types _are_ proofs of those propositions.

This idea is called the "Curry-Howard Correspondence"
(but it is so fundamental, it has been re-discovered
and expanded over time, so it goes by various names).

It is in the Lean spirit to dance back and forth between this
computational and logical interpretation of the same objects.

For example, in the following:
-/
example: Type := ℕ   -- proposition: some natural number exists
example: ℕ := ℕ.four -- a proof of the above by providing four as a witness

/-
At the face of it, `Prop` is just like `Type`.
Primarily, their difference is conventional, guiding their human interpretation.
Choosing between `<A>:Type` and `<A>:Prop` guides the reader to prefer
a computational or logical interpretation, respectively.
Comments and definitions in the Lean prelude reflect this convention.

For example, Lean suggestively names the trivial logical proposition `True`,
which has only one trivial proof (constructor): `True.intro`
(instead of defining `True: Type`, which they could have done instead).
-/
example: Prop := True
example: True := True.intro

-- Lean also defines the trivially unprovable proposition: `False`.
-- It has zero contructors (just like `Nothing` we defined way in the beginning).
example: Prop := False

/-
The cornerstone of constructivism in Lean (and Rocq, etc.)
are the conflated computational and logical readings of `∀` (and thus also `→`):

- Computationally (as we have seen a lot already):
  `∀<a:A>, <B>` is the the type of each function term
  that maps each given `A`-type input values to some `B`-type output value
  (where the type `B` may depend on value `a`).

- Logically,
  `∀<a:A>, <B>` is the proposition that `B` is true given any choice of `a`.

Perhaps a unifying view:
  `∀<a:A>, <B>` is the type of functions transforming any given proof `a`
  of proposition `A` to some proof of proposition `B` (which may depend on `a`).

The special case of `<A> → <B>` is then:
- Computationally, the type of functions mapping `A`-type values to `B` type values.
- Logically, the proposition that `A` being true implies that `B` is true.
-/

/-
The logical reading of this (computational) function
may be a bit weird: the existence of some `ℕ`
implies the existence of some `Bit`.
-/
example: ℕ → Bit := λ _ ↦ Bit.nah

-- We can define and construct new propositions inductively,
-- much as we did with data types.
inductive SomeℕExists: Prop where
  | this_one: ℕ → SomeℕExists
example: ℕ → SomeℕExists := SomeℕExists.this_one
example: SomeℕExists := SomeℕExists.this_one ℕ.zero

/-
Here's a recursively-defined proposition.
Proposition `ℕsExist` is provable given one `SomeℕExists`
Or it is provable given that `ℕsExist` and a `SomeℕExists`
Notice how this essentially encodes a list of `ℕ`!
-/
inductive ℕsExist: Prop where
  | final: SomeℕExists → ℕsExist
  | another: SomeℕExists → ℕsExist → ℕsExist

example: ℕsExist := ℕsExist.final
  (SomeℕExists.this_one ℕ.four)

example: ℕsExist :=
  ℕsExist.final (SomeℕExists.this_one ℕ.two)
  |> ℕsExist.another (SomeℕExists.this_one ℕ.three)

/-
Going forward, we use "proposition" and "proof" to refer only
to things in `Prop` (as we would expect, given the name).
But remember that this special treatment of `Prop` is only convention!
-/
