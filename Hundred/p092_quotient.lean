import Hundred.p091_setoid

/-
Lean's `Quotient` class
-/

#print Quotient
#print Quotient.mk
#reduce Quotient SetoidℕPair

abbrev ℕPairQ: Type := Quotient (inferInstance: Setoid ℕPair)

-- Equivalent formulations of `ℕPairQ`
example: { t // t = ℕPairQ } where
  val := @Quotient ℕPair inferInstance
  property := rfl

example: { t // t = ℕPairQ } where
  val := Quotient SetoidℕPair
  property := rfl

-- Particular elements of quotient `ℕPairQ`,
-- i.e., equivalence classes of `ℕPair`.
def ℕPairQ.mk: ℕPair → ℕPairQ := Quotient.mk _

example: ℕPairQ := ℕPairQ.mk (ℕ.three, ℕ.zero )
example: ℕPairQ := ℕPairQ.mk (ℕ.three, ℕ.one  )
example: ℕPairQ := ℕPairQ.mk (ℕ.zero , ℕ.three)

-- Nothing about `ℕPair` is changed per se.
theorem ℕPair_eq
: (ℕ.two , ℕ.one) ≠ (ℕ.one, ℕ.two)
:= by
  intro h
  cases h

-- But `Eq` _inside the quotient_ coincides
-- with the setoid equality.
theorem ℕPairQ_eq_example
: ℕPairQ.mk (ℕ.two , ℕ.one) = ℕPairQ.mk (ℕ.one, ℕ.two)
:= by
  -- goal: prove `_ = _`
  apply Quotient.sound
  -- goal: prove `_ ≈ _` (Setoid equality)
  rfl

-- Mechanically, (only) `ℕPairQ_eq_example` relies on
-- an axiom about `Quotient` that is given in Lean's prelude.
#print axioms ℕPair_eq
#print axioms ℕPairQ_eq_example

-- This axiom does not threaten Lean's soundness thanks
-- to _proof irrelevance_ (which we discuss next).
