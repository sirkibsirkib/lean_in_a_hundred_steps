import Hundred.p043_inductive_parameters_vs_indices
import Hundred.p049_predicates_and_relations

-- The `rename_i` tactic assigns the given name to the first
-- inaccessible name in context, so it can be used as usual.
example: ℕ → ℕ := by
  intro n
  cases n
  . exact ℕ.four
  . -- `.` then `rename_i` here does the same as `case succ n =>`
    rename_i n
    exact n

-- In fact, `rename_i` binds a list of given names in sequence.
-- Use `_` to skip the names you aren't interested in.
example: Lyst ℕ → Lyst ℕ := by
  intro l
  cases l
  . exact Lyst.nil
  . rename_i _ l -- we want to drop the first name
    exact l
