import Hundred.p001_inductive_types
import Hundred.p048_predicates_and_relations
import Hundred.p100_decidable

/-
Using some metaprogramming wizardry,
people have already defined derivation macros
for generating instances for some common
standard classes for new inductive types.

Here, let's demonstrate how we could have
defined `DecidableEq ℕ` by doing it with
a fresh type (isomorphic to `ℕ`) with a one-liner:
  `deriving instance <class> for <type>`
-/
inductive Freshℕ: Type where
  | zero: Freshℕ
  | succ: Freshℕ → Freshℕ

-- This automates what we did manually before
deriving instance DecidableEq for Freshℕ

-- Suffix a type definition with `deriving <name>`
-- as a shorthand way to derive for the new type.
inductive ℕwrapper where
  | intro (n: ℕ)
deriving DecidableEq
