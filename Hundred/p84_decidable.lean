import Hundred.p01_inductive_types
import Hundred.p14_constructor_functions
import Hundred.p55_less_than
import Hundred.p68_induction

/-
`Decidable` is another parametric class
in the Lean standard library, which is often useful.

In this case, it is `inductive`, with two constructors.
-/
example: Prop → Type := Decidable
example: {P: Prop} → (p:  P) → Decidable P := Decidable.isTrue
example: {P: Prop} → (p: ¬P) → Decidable P := Decidable.isFalse

/-
Conceptually, `Decidable P` is like `P ∨ ¬P`: either
1. wrapping a proof that `P` is true, or
2. wrapping a proof that `p` is false.

What distinguishes `Decidable` from `Or` is that
1. the two arms must be inverses (where `Or` has arbitrary disjuncts), and
2. `Decidable _: Type` where `Or _ _: Prop`.
-/
example: Prop := ℕ.two = ℕ.two
example: Type := Decidable (ℕ.two = ℕ.two)
example: ℕ.two = ℕ.two := Eq.refl ℕ.two
example: Decidable (ℕ.two = ℕ.two) := Decidable.isTrue (Eq.refl ℕ.two)

/-
By living in `Type`, a value of type `Decidable P`
is "computationally relevant", and can be
eliminated (matched) to produce values in `Type`!
This is not the case for `P ∨ ¬P`.
-/
example: Decidable (ℕ.two = ℕ.two) → ℕ
  | Decidable.isFalse _proof => ℕ.zero
  | Decidable.isTrue  _proof => ℕ.three

-- Let's define `Decidable (a = b)` for `a b: Bit` and `a b: ℕ`.

instance: (a: Bit) → (b: Bit) → Decidable (a = b)
  | .nah, .nah => .isTrue  rfl
  | .nah, .yep => .isFalse nofun
  | .yep, .nah => .isFalse nofun
  | .yep, .yep => .isTrue  rfl

-- we name this instance only so we can do a recursive call!
instance dec_eq_ℕ (a b: ℕ): Decidable (a = b) :=
  match a, b with
  | .zero  , .zero   => .isTrue  rfl
  | .zero  , .succ _ => .isFalse nofun
  | .succ _, .zero   => .isFalse nofun
  | .succ x, .succ y =>
    match dec_eq_ℕ x y with
    | .isTrue  h => isTrue  (by rw [h])
    | .isFalse h => isFalse (by
      intro heq
      cases heq
      contradiction
    )


-- Let's define `Decidable (a < b)` for `a b: ℕ`.

-- First we need a bunch of preliminaries!

theorem ℕlt_succ_lr: ∀ (a b: ℕ), a.lt b → a.succ.lt b.succ := by
  intro a b h
  induction h
  . case base n =>
    constructor
  . case step a b _ ih =>
    constructor
    assumption

theorem ℕlt_pred_left : ∀ (a b : ℕ), a.succ.lt b → a.lt b := by
  intro a b h
  generalize hc: a.succ = c at h
  revert hc
  induction h
  . case base n =>
    intro hc
    cases hc
    exact ℕ.lt.step (ℕ.lt.base a)
  . case step h ih =>
    intro hc
    cases hc
    exact ℕ.lt.step (ih rfl)

theorem ℕlt_succ_lr': ∀ (a b: ℕ), a.lt b ↔ a.succ.lt b.succ := by
  intro a b
  constructor
  . apply ℕlt_succ_lr
  . intro h
    cases h
    . constructor
    . rename_i h'
      exact ℕlt_pred_left a b h'

theorem neg_iff: ∀ (P Q: Prop), (P ↔ Q) → (¬P ↔ ¬Q) := by
  intro P Q ⟨x, y⟩
  constructor
  . intro np q
    apply np
    apply y q
  . intro nq p
    apply nq
    apply x p

theorem ℕlt_n_succ_lr: ∀ (a b: ℕ), ¬ a.lt b ↔ ¬ a.succ.lt b.succ := by
  intro a b
  apply neg_iff
  apply ℕlt_succ_lr'

instance dec_lt_ℕ (a b: ℕ): Decidable (a < b) :=
  match a, b with
  |       _, .zero   => .isFalse nofun
  | .zero  , .succ _ => .isTrue  (ℕzero_lt_succ _)
  | .succ x, .succ y =>
    match dec_lt_ℕ x y with
    | .isTrue  h  => isTrue (ℕlt_succ_lr   x y h)
    | .isFalse h => isFalse ((ℕlt_n_succ_lr x y).mp h)

/-
Phew, ok. But what have we got? `dec_lt_ℕ` gives us...

1. Because `dec_lt_ℕ: ∀ a b: ℕ, Decidable (a < b)` was somehow defined,
   its the logical assertion of its type `∀ a b: ℕ, Decidable (a < b)`
   holds! We know that the proposition `a < b` is decidable for
   any two `a b: ℕ`!

2. Because `dec_lt_ℕ` returns a value `Decidable (a < b): Type`,
   we can discriminate this data into the `.isTrue` and `.isFalse` cases,
   computationally! `dec_lt_ℕ` is a function that computes
   the decision, carrying proofs with it in either case.
-/
#reduce dec_lt_ℕ ℕ.two ℕ.three
#reduce dec_lt_ℕ ℕ.two ℕ.two
#reduce dec_lt_ℕ ℕ.two ℕ.one
#reduce dec_lt_ℕ ℕ.one ℕ.one
#reduce dec_lt_ℕ ℕ.zero ℕ.one
