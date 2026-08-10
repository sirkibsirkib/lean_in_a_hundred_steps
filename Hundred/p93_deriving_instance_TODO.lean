import Hundred.p01_inductive_types
import Hundred.p47_predicates_and_relations

/-
Using some metaprogramming wizardry,
people have already defined derivation macros
for generating instances for some common
standard classes for new inductive types
-/

deriving instance DecidableEq for Bit
deriving instance DecidableEq for ℕ

def ℕℕProd := ℕ × ℕ
deriving instance DecidableEq for ℕℕProd


-- `deriving DecidableEq` immediately after
-- the type def does the same job.
inductive ℕ': Type where
  | zero: ℕ'
  | succ: ℕ' → ℕ'
deriving DecidableEq
