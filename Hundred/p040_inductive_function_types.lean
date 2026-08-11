import Hundred.p014_constructor_functions
import Hundred.p015_matching
/-
Previously, we have seen the inductive definition of
values in `Type` (e.g., `ℕ`) and values in `Prop` (e.g., `ℕsExist`).

Now let's see how you can inductively define type functions.
-/

/-
Here is what is often called "Maybe" or "Option".
As can be seen in the example, `Maybe` is not in `Type`,
rather `Maybe` is a _function_, in `Type → Type`.

- Haskellers will know this as a _higher-kinded type_,
  specifically of the kind `* -> *` (unary type function).

- Coming from other languages, you may understand
  `Maybe` as a _(parametric) polymorphic type_.
-/
inductive Maybe: Type → Type where
  | none: (T: Type) → Maybe T
  | some: (T: Type) → T → Maybe T

-- `Maybe` is a function mapping types to types.
example: Type → Type := Maybe
example: Type := Maybe ℕ

-- `Maybe.none` is a function mapping given `T: Type` to `Maybe T`.
-- Recall from above that each `Maybe T` is a type!
example: (T: Type) → Maybe T := Maybe.none
example: Maybe ℕ := Maybe.none ℕ

-- `Maybe.some` is a binary function mapping given `T: Type` and `T` to `Maybe T`.
example: (T: Type) → T → Maybe T := Maybe.some
example: ℕ → Maybe ℕ := Maybe.some ℕ
example: (T: Type) → T → Maybe T := Maybe.some
example: Maybe ℕ := Maybe.some ℕ ℕ.three

-- As we saw before, dependencies between types mean
-- Lean has more opportunities to infer types!
example: Maybe ℕ := Maybe.some ℕ ℕ.three -- no type inference here
example          := Maybe.some ℕ ℕ.three -- example type can be inferred from args
example          := Maybe.some _ ℕ.three -- first arg can be inferred from second arg

/-
I don't think I need to convince you that polymorphic types
are very helpful as general tools for specific problems.
Here, the generic `Maybe` is used, but specialized to `Maybe ℕ`.
-/
def try_pred: ℕ → Maybe ℕ
  | ℕ.zero   => Maybe.none ℕ
  | ℕ.succ n => Maybe.some ℕ n
#reduce try_pred ℕ.zero
#reduce try_pred ℕ.four

/-
And dependently typed functions can define many
useful polymorphic functions over polymorphic types.
-/
def maybe_or: ∀ (T: Type) (_:Maybe T) (_:Maybe T), Maybe T :=
  λ (T: Type) (x: Maybe T) (y: Maybe T) ↦
    match x with
    | Maybe.some _ _ => x
    | Maybe.none _   => y
#reduce maybe_or ℕ (try_pred ℕ.zero) (try_pred ℕ.four)

def wraps_some: (A B: Type) → (f: A → B) → (A → Maybe B) :=
  λ _ _ f a ↦ Maybe.some _ (f a)
example: ℕ → Maybe ℕ := wraps_some ℕ ℕ pred
