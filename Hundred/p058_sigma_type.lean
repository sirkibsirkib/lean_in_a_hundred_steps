import Hundred.p045_inductive_parameters_vs_indices
import Hundred.p051_predicates_and_relations

/-
Recall that `Prod` is the type of pairs in `Type`.

`Sigma` is similar, but it is formulated such that
the second element's type depends on the first element.
As such, it is also often called _dependent pair_.
-/
example: (α: Type u) → (    Type v) → Type (max u v) := Prod
example: {α: Type u} → (α → Type v) → Type (max u v) := Sigma


example: (α: Type _) → (α → Type _) → Type _ := @Sigma
example:               (ℕ → Type _) → Type _ := @Sigma ℕ
example:                              Type _ := @Sigma ℕ (LenLyst Prop ·.succ)
-- ^ the type of `⟨n,l⟩` pairs where `l: LenLyst Prop n.succ`.


-- `Sigma.mk` constructs dependent pairs.
-- First, a quick refresher on how `LenLyst` is defined
example: LenLyst Prop ℕ.zero := LenLyst.nil
example: LenLyst Prop ℕ.one := LenLyst.cons True (LenLyst.nil)

/-
Now let's construct a dependent pair!
1. fix the first element is `ℕ.zero`
2. fix the second element as `LenLyst.cons True .nil`,
  whose type Lean confirms is `(LenLyst Prop ·.succ) ℕ.zero` i.e., `LenLyst Prop ℕ.one`
-/
abbrev eg_sigma: Type := @Sigma ℕ (LenLyst Prop ·.succ)
def eg_dep_pair: eg_sigma := Sigma.mk .zero (.cons True .nil)

-- `fst` and `snd` project to the pair elements as usual.
example: eg_dep_pair.fst = ℕ.zero            := Eq.refl _
example: eg_dep_pair.snd = (.cons True .nil) := Eq.refl _

/-
The Lean prelude defines `Σ x, P x` as notation for
constructing `Sigma` types in a more legible style.
Because it is just notation, it boils away under reduction.
-/
example: (Σ n:ℕ, LenLyst Prop n.succ) = eg_sigma := Eq.refl _

-- Here's another very simple example:
-- any data (`snd`) tagged with its type (`fst`)!
example: Σ t, t := Sigma.mk ℕ ℕ.zero
