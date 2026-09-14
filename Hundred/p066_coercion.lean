import Hundred.p022_structure

/-
Whenever a term `x: X` is expected to have type `Y`,
Lean checks for an instance `i: Coe X Y`.
If it finds it, Lean silently replaces the `x` with
`i.coe x: Y`; we say `x` was _coerced_ to type `Y`.
-/

-- Let's let our previously-defined `ℕPair` structure
-- be coerced back and forth from `ℕ × ℕ`.
instance: Coe (ℕ × ℕ) ℕPair where
  coe := λ (x, y) ↦ ℕPair.mk x y

example: ℕPair := (ℕ.zero, ℕ.two)

instance: Coe ℕPair (ℕ × ℕ) where
  coe := λ npair ↦ (npair.1, npair.2)

example: ℕ × ℕ := ℕPair.mk ℕ.zero ℕ.three
