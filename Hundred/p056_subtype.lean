import Hundred.p048_predicates_and_relations

/-
`Subtype` is essentially `Sigma` but whose
second element is in `Prop`.
The assymetry is reflected in the
difference in names between the fields.
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
