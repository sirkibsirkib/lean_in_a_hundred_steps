import Hundred.p055_predicates_and_relations

/-
We already know that `Eq.symm` and the `symm` tactic
let you flip around an equality.
-/
#print Eq.symm

/-
And we already know that `rw` lets you
rewrite `a` to `b` inside a term if `a = b`.
-/

example (m n: ℕ) (heq: m = n) (ho: Odd m): Odd n := by
  rw [heq] at ho
  exact ho

/-
if `h: a = b` then `h ▸ t` is the result of
rewriting the type of `t` in either direction.
It feels like "casting t".
-/
example (m n: ℕ) (heq: m = n) (ho: Odd m): Odd n :=
  heq ▸ ho

-- use type ascriptions to control what is rewritten
example (m n: ℕ) (heq: m = n) (ho: Odd m): Odd n := heq ▸ ho -- m ↦ n
example (m n: ℕ) (heq: m = n) (ho: Odd m): Odd m := heq ▸ ho -- nothing
example (m n: ℕ) (heq: m = n): m = n := heq ▸ heq -- nothing
example (m n: ℕ) (heq: m = n): m = m := heq ▸ heq -- n ↦ m
example (m n: ℕ) (heq: m = n): n = m := heq ▸ heq -- m ↦ n
example (m n: ℕ) (heq: m = n): m = n := heq ▸ heq -- {m ↦ n, n ↦ m}

-- You can chain `▸`, of course.
-- Here it works on both sides because they are both of shape `_ = _`.
example (m n: ℕ) (heq: m = n) :=
  (
    (
      (heq ▸ heq: n = m)
      ▸
      (heq ▸ heq: m = m)
      : m = n
    )
    ▸
    heq
    : m = m
  )
