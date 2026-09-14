import Hundred.p044_def_parameters

/-
We already saw that definitions of terms
(and constructors) can be parametrised,
turning them into functions

But you can also parametrise an `inductive` defintion itself!
Adding explicit parameter `(t: T)` ...
1. adds `(t: T) →` to the type
2. adds `{t: T} →` to each constructor.
3. _and implies the application of `t` in the return type of each constructor!_

Let's use this to make another (neater) defintion of polymorphic "Maybe".
-/
inductive Maybe' (T: Type): Type where
  | some: T → Maybe' T
  | none:     Maybe' T
example: (_: Type) → Type := Maybe'
example:     Type  → Type := Maybe'
example:             Type := Maybe' ℕ
example:             Type := Maybe' Bit

example: {T: Type} → Maybe' T   := Maybe'.none
example:             Maybe' Bit := Maybe'.none
example:             Maybe' ℕ  := Maybe'.none

example: {T: Type} → T → Maybe' T := Maybe'.some
example: {_: Type} → ℕ → Maybe' ℕ := Maybe'.some -- weird but ok
example:             ℕ → Maybe' ℕ := Maybe'.some -- argument `ℕ` is implied.
example:                 Maybe' ℕ := Maybe'.some ℕ.zero -- argument `ℕ` is implied.

-- Let's see how `Maybe'` may be used.
def try_pred': ℕ → Maybe' ℕ
  | ℕ.zero   => Maybe'.none
  | ℕ.succ n => Maybe'.some n

/-
Adding implicit parameter `{t: T)` is the same as explicit `(t: T)`,
only except that the defined type parameter is implicit.
(Constructors are entirely unaffected).
-/
inductive Tree {LeafLabel: Type}: Type where
  | leaf: LeafLabel → Tree
  | node: Tree → Tree → Tree
example          := Tree.leaf ℕ.zero
example: @Tree ℕ := Tree.leaf ℕ.zero
example := Tree.node (Tree.leaf ℕ.zero) (Tree.leaf ℕ.one)

/-
Note that these parametric inductive type definitions
have a certain uniformity.
Point #3 above makes all the constructors fill in
the type parameter the same way: as given.

Let's see a simple example:
all natural numbers are cool!
-/
inductive Cool (n: ℕ): Prop where
  | intro: Cool n
example: {n: ℕ} → Cool n :=  Cool.intro
example: (n: ℕ) → Cool n := @Cool.intro


/-
In fact, parameters suffice to define many useful polymorphic types.
Here are two examples, which we will use later.
For example, here is the polymorphic list
(avoiding `List` already in the standard library).
-/
inductive Lyst (T: Type) where
  | nil : Lyst T
  | cons: T → Lyst T → Lyst T

example: {_: Type} → Lyst Bit := Lyst.nil
example:             Lyst Bit := Lyst.nil

example: {T: Type} →   T → Lyst   T → Lyst   T := Lyst.cons
example:             Bit → Lyst Bit → Lyst Bit := Lyst.cons
example:                   Lyst Bit → Lyst Bit := Lyst.cons Bit.nah
example:                              Lyst Bit := Lyst.cons Bit.nah Lyst.nil

namespace Lyst
  def head {T: Type}: Lyst T → Maybe' T
    | nil => Maybe'.none
    | cons (t: T) (_: Lyst T) => Maybe'.some t

  def length {T: Type}: Lyst T → ℕ
    | nil => ℕ.zero
    | cons _ l => l.length.succ

end Lyst

/-
The inductive function types we saw earlier are freer
(although we have not demonstrated it before).

Constructors can fill in the type parameters in other ways!
These type parameters are called _indices_ in the literature.
They are strictly more powerful.

For example, the following is a variation on `Lyst` where:
- the type `T` of elements comprising the list is parametric as before, but
- `length: ℕ` is an index, another argument which each constructor
  fixes in its own way, as a function of its arguments.

Note: `(length: ℕ)` could also be `ℕ`, because the type
does not depend on `length`, but it is named  for readability;
we can better understand what the `ℕ` encodes!
-/

inductive LenLyst (T: Type): (length: ℕ) → Type where
  | nil:  LenLyst T ℕ.zero
  | cons: (t: T) → {n: ℕ} → LenLyst T n → LenLyst T n.succ

example: Type → ℕ → Type := LenLyst

example: {T: Type} → LenLyst T   ℕ.zero := LenLyst.nil
example:             LenLyst Bit ℕ.zero := LenLyst.nil
example:             LenLyst ℕ   ℕ.zero := LenLyst.nil

example := (LenLyst.nil : LenLyst Bit ℕ.zero)

example :=
  (LenLyst.cons Bit.nah
    (LenLyst.nil : LenLyst Bit ℕ.zero)
  : LenLyst Bit ℕ.one)

example :=
  (LenLyst.cons Bit.nah
    (LenLyst.cons Bit.nah
      (LenLyst.nil : LenLyst Bit ℕ.zero)
    : LenLyst Bit ℕ.one)
  : LenLyst Bit ℕ.two)

example :=
  (LenLyst.cons Bit.nah
    (LenLyst.cons Bit.nah
      (LenLyst.cons Bit.nah
        (LenLyst.nil : LenLyst Bit ℕ.zero)
      : LenLyst Bit ℕ.one)
    : LenLyst Bit ℕ.two)
  : LenLyst Bit ℕ.three)

/-
Sometimes, the same concepts can be defined
via either a parameter or an index.
There is no consequential difference.
Even the underlying machinery ends up the same.

Here, for example, Lean generates an isomorphic `rec` method,
which (as we later see) determines how we reason via _induction_.
-/
inductive  P (b: Bit):   ℕ → Prop -- `b` is a parameter
| z:       P b ℕ.zero
| s n:     P b n → P b n.succ

inductive  I: (b: Bit) → ℕ → Prop -- `b` is an index
| z {b}:   I b ℕ.zero
| s {b} n: I b n → I b n.succ

#check P.rec
#check I.rec
