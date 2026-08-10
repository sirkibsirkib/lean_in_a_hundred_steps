import Hundred.p14_constructor_functions

/-
N-ary relations are just propositions with N parameters.
Predicates are another name for 1-ary relations.
(But, as in the literature, by "relation" we often mean 2-ary relation).

The type of relations over concrete types requires no dependency.
-/
def ℕ_Pred := ℕ → Prop
def ℕℕ_Rel := ℕ → ℕ → Prop

/-
But defining relations over arbitrary types,
and then giving them structure,
very quickly requires dependent (indexed) types.
-/
abbrev EndoRelation (T: Type) := T → T → Prop
abbrev Predicate    (T: Type) := T → Prop
def trivT: Predicate ℕ := λ (_:ℕ) ↦ True


def proof_triv: trivT ℕ.four :=
  by
  have q := Predicate
  unfold trivT
  exact True.intro

#reduce (proofs := true) proof_triv

example: Predicate ℕ := λ (_:ℕ) ↦ False

namespace ℕ

    -- read `lt` as "less than"
    inductive lt: EndoRelation ℕ where
      -- any number < its successor
      | base: (n: ℕ) → -- given any `n` ...
          n.lt n.succ   -- ... `n < n.succ` is proven.

      -- incrementing greater preserves <
      | step: {a b: ℕ} → -- given any `a` and `b` ...
          a.lt b →   -- and ... given `a < b` ...
          a.lt b.succ -- ... `a < b.succ` is proven.

    def one_lt_two:   one.lt two   := lt.base one
    def one_lt_three: one.lt three := lt.step one_lt_two

    -- read `gt` as "greater than"
    def gt_one: Predicate ℕ := one.lt -- (λn ↦ one.lt n)
    example: gt_one three := one_lt_three

end ℕ

-- Here is a common encoding of even/odd for natural numbers
-- We will use it a lot later.
mutual
  inductive Even: Predicate ℕ where
    | zero : Even ℕ.zero
    | succ : ∀ n, Odd n → Even n.succ

  inductive Odd: Predicate ℕ where
    | succ : ∀ n, Even n → Odd n.succ

end

def Odd.one:   Odd ℕ.one :=  Odd.succ _ Even.zero
def Even.two: Even ℕ.two := Even.succ _  Odd.one


abbrev Transitive {T: Type} (R: EndoRelation T) :=
  ∀ {x y z: T},
    R x y   →
    R   y z →
    R x   z

abbrev Symmetric {T: Type} (R: EndoRelation T) :=
  ∀ {x y: T},
    R x y →
    R y x
