import Hundred.p14_constructor_functions

#print Setoid

class Intlike (T: Type) where
  inc: T → T
  dec: T → T


structure Integer₂ where
  abs: ℕ
  pos: Bool
  h: ¬ (abs = ℕ.zero ∧ pos = false)


structure Integer₁ where
  pos: ℕ
  neg: ℕ
  h: pos = ℕ.zero ∨ neg = ℕ.zero

instance: Intlike Integer₁ where
  inc i := by
    cases h: i.neg
    . refine ⟨ i.pos.succ, ℕ.zero, ?_⟩
      right
      rfl
    . case succ n =>
      refine ⟨ i.pos, n, ?_⟩
      cases i
      rename_i x y j
      cases j
      . subst x
        simp at *
      . subst y
        simp at *

  dec i := by
    cases h: i.pos
    . refine ⟨ ℕ.zero, i.neg.succ, ?_⟩
      left
      rfl
    . case succ n =>
      refine ⟨ n, i.neg, ?_⟩
      cases i
      rename_i x y j
      cases j
      . subst x
        simp at *
      . subst y
        simp at *

theorem q:
  ∀ (i: Integer₁),
    Intlike.dec (Intlike.inc i) = i
:= by
  intro i
  obtain ⟨p, n, h⟩ := i
  cases h
  . subst p
    simp [Intlike.inc]




inductive Integer where
  | Pred (i: Integer)
  | Succ (i: Integer)





namespace Integer
  def balance: Integer → Balance := λ
    intro i
    cases i

end Integer

def succ_first: Integer → Integer
  | .Pred

instance: Setoid ℕ where
