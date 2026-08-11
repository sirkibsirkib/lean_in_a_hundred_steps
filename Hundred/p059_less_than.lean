import Hundred.p014_constructor_functions
import Hundred.p048_predicates_and_relations

/-
`LT` is defined in the Lean standard library,
as a class with one parameter.

Or you could say each `LT x` is a class.
-/
#print LT
example: Type → Type := LT
example: Type := LT ℕ
example: {T: Type} → [LT T] → T → T → Prop := LT.lt

/-
Let's instantiate class `LT ℕ`, or informally,
"let's define the `LT` typeclass for type `ℕ`".
-/

instance LTℕ: LT ℕ where
  -- `LT.lt` is the only field of `LT`.
  -- `ℕ.lt` is an inductive predicate that we imported from earlier.
  lt := ℕ.lt

/-
At first glance, `LT.lt` has a wickedly complex type.
But that's just because of two layers of implicit parameters.
Let's drill down through these layers of abstraction
-/
example: {T: Type} → [LT T] → T → T → Prop := LT.lt
example:             [LT ℕ] → ℕ → ℕ → Prop := @LT.lt ℕ
example:                       ℕ → ℕ → Prop := @LT.lt ℕ LTℕ -- given explicitly
example:                       ℕ → ℕ → Prop := @LT.lt ℕ _ -- inferred via lookup!
example:                                Prop := @LT.lt ℕ LTℕ ℕ.zero ℕ.one -- given explicitly
example:                                Prop := @LT.lt _ LTℕ ℕ.zero ℕ.one -- `T := ℕ` inferred from `ℕ.zero`
example:                                Prop := @LT.lt _ _   ℕ.zero ℕ.one -- `T := ℕ` inferred and instance looked up
example:                                Prop :=  LT.lt       ℕ.zero ℕ.one -- `T := ℕ` inferred and instance looked up


/-
At first glance, we have gone through a lot
of trouble for nothing, because `LT.lt` and `ℕ.lt`
construct definitionally equivalent propositions the same way!
-/
example: Prop := LT.lt ℕ.zero ℕ.four
example: Prop :=  ℕ.lt ℕ.zero ℕ.four

-- But there are two good reasons we want `LT ℕ`.

/-
_Firstly_, we inherit `<` from the Lean prelude as
a neat infix notation for `Lt.lt`, without the
ambiguity of defining a conflicting notation for symbol `<`.
-/
example: Prop := LT.lt ℕ.zero   ℕ.four
example: Prop :=       ℕ.zero < ℕ.four


/-
_Secondly_, `LT.lt` can be used in abstract,
in contexts that generalise `ℕ.lt`, by generalising
1. the type `T` of the two arguments (here `ℕ`)
2. the definition of the `lt` predicate over `T`
-/
example: Prop := LT.lt ℕ.zero ℕ.four
example: Prop :=  ℕ.lt ℕ.zero ℕ.four

/-
Besides stuff from the Lean standard library defined
atop `LT`, we can define our own generic things:
-/
def gt {T: Type} [i: LT T] (a b: T): Prop :=
  (¬ LT.lt a b) ∧ (a ≠ b)

example: ℕ → ℕ → Prop := gt
example:         Prop := gt ℕ.four ℕ.two
