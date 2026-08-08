import Hundred.t27_dependency
import Hundred.t29_inductive_parameters_and_indices
import Hundred.t31_notation
open ℕ

def try_dec: ℕ → Option₁ ℕ
  | zero => Option₁.none
  | succ n => Option₁.some n

inductive lt: ℕ → ℕ → Prop where
  | base: ∀ (n: ℕ), lt zero n.succ
  | step: ∀ (a b: ℕ), lt a b → lt a.succ b.succ

def is_lt (a b: ℕ): Bool :=
  match b with
  | zero => false
  | succ b' => match a with
    | zero => true
    | succ a' => is_lt a' b'

-- I did not expect lean to accept that this is terminating. Cool!
def bubble: Lyst ℕ → Lyst ℕ
  | Lyst.cons x (Lyst.cons y l) =>
    if is_lt x y
    then Lyst.cons x (bubble (Lyst.cons y l))
    else Lyst.cons y (bubble (Lyst.cons x l))
  | l => l

instance : Repr ℕ where
  reprPrec n _ := ℕRepr n
  where ℕRepr
    | .zero => "z"
    | .succ n' => ℕRepr n' ++ "+"

-- formatting
instance : Repr (Lyst ℕ) where
  reprPrec n _ := "⟦" ++ LystℕRepr true n ++ "⟧"
  where LystℕRepr (first: Bool)
    | .nil => ""
    | .cons n l => (if first then "" else ", ") ++ repr n ++ LystℕRepr false l

#eval bubble ⟦one, four, two, three⟧

-- TODO define bubble sort and prove its termination

/-
def try_dec_lyst (l: Lyst ℕ): Option₁ (Lyst ℕ)
  | Lyst.nil => Option₁.some Lyst.nil
  | Lyst.cons n l' =>
      match try_dec n with
      | Option₁.none => Option₁.none
      | Option₁.some n' =>
          match try_dec_lyst ()
-/
