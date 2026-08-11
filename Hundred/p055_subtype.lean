import Hundred.p048_predicates_and_relations

/-
Recall that Lean offers tools for conjoining two things:
- `And` is for propositions (in `Prop`).
- `Sum` is for data types   (in `Type`).

Lean offers `Subtype` as a way to conjoin a data-proof pair.
Specifically,
1. some `val` in `Type`
2. some propety of `val`.

As such, `Subtype (T: Type) (P: T → Prop)` represents
the type of all `T`-elements that satisfy `P`.
-/
#print Subtype

def Evenℕ := @Subtype ℕ Even
def Evenℕ.two: Evenℕ := Subtype.mk ℕ.two Even.two
#reduce Evenℕ.two.val
#reduce Evenℕ.two.property

/-
Lean offers `{ <name> // <proposition> }` as notation for
`Subtype.mk <name> (λ <name> ↦ <proposition>)`.
This lets you concisely express the dependency.
-/
def Evenℕ' := { n // Even n }

-- Because it is notation, it simply boils away under reduction.
example: Evenℕ = Evenℕ' := Eq.refl _
