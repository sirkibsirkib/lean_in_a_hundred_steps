import Hundred.p01_inductive_types
import Hundred.p14_constructor_functions
import Hundred.p59_add
import Hundred.p47_predicates_and_relations

/-
Conceptually, instantiating class `i: Setoid t`
equips your chosen type `t` with some
equivalence relation `i.r` over `t` pairs (i.e., `i.r : t → t → Prop`).
`Equivalence r` is just a basic structure bundling
proofs that any relation `r` is reflective,
symmetric, and transitive.

These models standard mathematical concepts:
1. https://en.wikipedia.org/wiki/Setoid
2. https://en.wikipedia.org/wiki/Equivalence_relation

Mechanically, `Setoid: Type → Type` has fields for `r`
and a proof that `Equivalence r`.
By making `Setoid r` a class, instantiating it
effectively informs Lean of how to look up
the canonical instance `i: Setoid t` from `t`.

The prelude defines `a ≈ b` as notation for `Setoid.r a b`.
The idea is that you can define something similar to `=` yourself.
-/
#print Setoid

/-
As an exercise, let's define a Setoid over `ℕ × ℕ`: They
are the same if they have the same _sum_.

First, we define the relation.
-/
def ℕ.Pair.same_sum: EndoRelation (ℕ × ℕ) :=
  λ (a, b) (x, y) ↦ a + b = x + y

theorem ℕ.Pair.same_sum.refl: ∀ pair, ℕ.Pair.same_sum pair pair :=
  λ _ ↦ rfl

theorem ℕ.sum.symm: ∀ (a b: ℕ),
  ℕ.sum a b = ℕ.sum b a
:= by
  intro a b
  induction a
  . unfold ℕ.sum
    induction b
    . simp
    . case zero.succ a aih =>
      simp

  . sorry


theorem ℕ.Pair.same_sum.symm: ∀ p1 p2,
  ℕ.Pair.same_sum p1 p2 →
  ℕ.Pair.same_sum p2 p1
:= by
  intro ⟨a, b⟩ ⟨x, y⟩ h
  unfold same_sum at *


-- Next, we prove that this relation is an equivalence.
def ℕ.Pair.same_sum.Equivalence: Equivalence ℕ.Pair.same_sum where
  refl h := Eq.refl _

  symm := by
    intro ⟨a, b⟩ ⟨x, y⟩ h1
    induction a
    . simp







def Bit.func_to_out_eq (T: Type): EndoRelation (T → Bit) :=
  λ (f g: T → Bit) ↦
    ∀ (t: T),
      f t = g t

/-
Now let's prove that each `Bit.func_to_out_eq T` is an equivalence relation.
-/
theorem Bit.func_to_out_eq.Equivalence (T: Type)
: Equivalence (Bit.func_to_out_eq T) where

  refl x := by
    unfold func_to_out_eq
    intro t
    rfl

  symm x y := by
    unfold func_to_out_eq at *
    exact (x y).symm

  trans x y z := by
    rename_i t1 t2 t3
    unfold func_to_out_eq at *
    specialize x z
    specialize y z
    rw [x, y]

-- Now we instantiate the Setoid!
instance (T: Type): Setoid (T → Bit) where
  r := Bit.func_to_out_eq T
  iseqv := Bit.func_to_out_eq.Equivalence T

-- Now Lean can resolve the setoid!
#reduce (Setoid.r     : EndoRelation (ℕ → Bit))
#reduce (Setoid.iseqv : @Equivalence (ℕ → Bit) _)
