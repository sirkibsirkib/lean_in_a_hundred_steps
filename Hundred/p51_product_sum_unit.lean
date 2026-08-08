import Hundred.p14_constructor_functions

/-
The Lean prelude has two polymorphic that are commonly used.
- `Prod` is a structure with fields `fst` and `snd`.
  Think of it as the `Type` version of `And`.
- `Sum` is an inductive type with unary constructors `inl` and `inr`.
  Thin of it as the `Type` version of `Or`.
-/
example: Type → Type → Type := Prod
example: Type := Prod Prop ℕ
example: Type := Prod Prop ℕ
example: Prod Prop ℕ → Prop := Prod.fst
example: Prod Prop ℕ → ℕ := Prod.snd
example: Prod ℕ Prop := { fst := ℕ.three, snd := True  }
example: Prod ℕ Prop := Prod.mk ℕ.zero True
example: ℕ := (Prod.mk ℕ.zero True).fst
example: ℕ := (Prod.mk ℕ.zero True).1
example: Prop := (Prod.mk ℕ.zero True).snd
example: Prop := (Prod.mk ℕ.zero True).2

example: Type → Type → Type := Sum
example: Type := Sum Prop ℕ
example: Sum Prop ℕ := Sum.inl True
example: Sum Prop ℕ := Sum.inr ℕ.zero
example: Sum Prop ℕ → Prop
  | Sum.inl p => p
  | Sum.inr n => n = ℕ.zero

/-
But you will seldom see identifiers `Prop` and `Sum` in the wild.
Much as `∧` is used for `And` and `∨` is used for `Or`,
`×` (\times) is used for `Prod`  and `⊕` (\oplus) is used for `Sum`.
-/
example: ℕ × Prop → ℕ := Prod.fst
example: ℕ × Prop → ℕ := λ pair ↦ pair.1
example: Prop ⊕ ℕ → Prop
  | Sum.inl p => p
  | Sum.inr n => n = ℕ.zero

/-
Products are so common, in fact, that there is
also notation for the constructor: `(a,b)`!
-/
example: ℕ × Prop := (ℕ.zero, True)

/-
They had the presence of mind to define × and ⊕ and (_,_) notations right-associatively!
Most commonly, this lets you define N-ary products and their N-tuple values.
-/
example: Prop               := (True)
example: Prop × Prop        := (True, True)
example: Prop × Prop × Prop := (True, True, True)

-- these are the same
example: Prop ×  Prop × Prop  := (True,  True, True )
example: Prop × (Prop × Prop) := (True, (True, True))

/-
The `Unit` type is a trivial structure provided by Lean,
which has only the trivial constructor `Unit.unit : Unit`.

But Lean defines `()` as notation for `Unit.unit` to suggest that
`Unit` is the nullary product and `()` is the nullary tuple.
-/
example: Unit := Unit.unit
example: Unit := ()
