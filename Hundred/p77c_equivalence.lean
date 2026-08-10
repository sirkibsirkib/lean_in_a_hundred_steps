import Hundred.p77b_trans_calc

/-
`Equivalence r` is a standard `structure` that
bundles proofs that relation `r` is reflective,
symmetric, and transitive (defined in the usual way).
https://en.wikipedia.org/wiki/Equivalence_relation

let's prove that `ℕPair.same_sum` is an equivalence relation!
-/

theorem ℕPair.same_sum_Equivalence: Equivalence ℕPair.same_sum where
  refl _ := rfl
  symm   := Eq.symm
  trans  := ℕPair.same_sum_Transitive
