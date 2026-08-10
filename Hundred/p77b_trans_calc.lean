import Hundred.p26_structural_recursion
import Hundred.p72_induction

/-
`Trans` is a super generic typeclass for
relations which are (proven to be) transitive.
Notably the standard library proves that `Eq` is transitive.
-/
#print Trans
#print Trans.trans

#print instTransEq -- named instance of `Trans Eq _ _`

/-
The `calc` tactic lets you prove relationship `x₁ ∼ xₙ`
for any relation `∼` that is transitive (has a `Trans` instance),
by taking a list of incremental steps from `x₁` to `xₙ`:
1. `x₁ ∼ x₂`
2.       `x₂ ∼ x₃`
3.             `x₃ ∼ x₄`
...
n.                         `xₙ₋₁ ∼ xₙ`.
-/
example (T: Sort u): T → T → Prop := @Eq T
#print instTransEq
#synth Trans Eq _ _
#print Trans

/-
Let's use the fact that `Trans Eq _ _` is instantiated
to prove that a different relation is transitive.
-/

abbrev ℕPair := ℕ × ℕ

abbrev ℕPair.pair_sum: ℕPair → ℕ :=
  λ (x, y) ↦ x + y

def ℕPair.same_sum: EndoRelation ℕPair :=
  λ n1 n2 ↦ n1.pair_sum = n2.pair_sum

abbrev Transitive {T: Type} (R: EndoRelation T) :=
  ∀ {x y z: T},
    R x y   →
    R   y z →
    R x   z

theorem ℕPair.same_sum_Transitive
: Transitive ℕPair.same_sum
:= by
  unfold Transitive
  unfold ℕPair.same_sum
  intro x y z h1 h2
  -- goal: `x.pair_sum = z.pair_sum`
  calc
    -- here we use calc
    _ = y.pair_sum := h1 -- left inferred from goal
    _ = _          := h2 -- left inferred from above. right inferred from goal
