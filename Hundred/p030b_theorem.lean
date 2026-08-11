import Hundred.p030_propositions
open ℕ

/-
In Lean, `theorem` is the same as `def`, but
(only) the former is intended for proving propositions.
1. You get an error if you use `theorem` to define values in `Type`
2. You get a warning if you use `def` to define values in `Prop`

(`example` is happy with either).
-/
example: Prop := SomeℕExists
example: ℕ → SomeℕExists := SomeℕExists.this_one

theorem ℕ.non_empty: SomeℕExists :=
  SomeℕExists.this_one ℕ.four

-- This does the same but generates a warning (as of Lean v4.33 at least)
def    ℕ.non_empty': SomeℕExists :=
  SomeℕExists.this_one ℕ.four

-- The type of this definition is `ℕ → SomeℕExists`
-- where `ℕ: Type` and `SomeℕExists: Prop`
-- Use `theorem` here, because the _output_ is what matters!
theorem ℕ.SomeℕExists: ℕ → SomeℕExists := SomeℕExists.this_one


/-
This is yet another asymmetry in Lean between `Type` and `Prop`
that reinforces that these have different connotations.
Roughly, we primarily care _that_ theorems are proven (the _type_),
and only secondarily care _how_ theorems are proven (the _value_).
-/

/-
/-
In Lean (and Rocq etc) "proving" and "proofs" connote
definitions of terms with complex types, usually in Prop.

A common suggestion is that we are more interested _that_
some object of that type exists (because it witnesses the
truth of the proposition) and less interested _what_ that object is.

Here's a proof that every ℕ is either Odd or Even
(as defined earler).
-/
def ℕOddOrEven: ∀ (n : ℕ), Odd n ∨ Even n :=
  λ (n : ℕ) ↦
    match n with
    | zero    => -- goal: Odd zero ∨ Even zero
      Or.inr Even.zero
    | succ n' => -- goal: Odd n'.succ ∨ Even n'succ
      match ℕOddOrEven n' with -- recursive call. Is n' odd or even?
      | Or.inl (H: Odd  n') => -- if n' is odd
        Or.inr (Even.succ _ H) -- ... then n'.succ is even
      | Or.inr (H: Even n') => -- if n' is even
        Or.inl ( Odd.succ _ H) -- ... then n.succ is odd

/-
It is more canonical to define such a term via "theorem",
which is exactly like "def" but:

- Mechanical: Theorems are only allowed for propositions (unlike Rocq)
  so they are treated as opaque by the compiler, during evaluation with #reduce.
  Also some minor quirks like the Lean LSP unver VSCode annotates type-checked
  theorems (not defs) with ✓✓ in the left margin. Neato I guess.

- Conventional: .. as such, theorems signal terms which are less interesting
  for _how_ they are defined, but more just _that_ they are defined,
  thus witnessing the truth of the proposition that is their type.

... but every "theorem" can be changed to "def" without doing any harm.
-/
theorem ℕOddOrEven': ∀ (n : ℕ), Odd n ∨ Even n := ℕOddOrEven

-- Note that the proposition could be defined itself first if desired.
def ℕOddOrEven_Prop: Prop := ∀ (n : ℕ), Odd n ∨ Even n
theorem ℕOddOrEven'': ℕOddOrEven_Prop := ℕOddOrEven'
-/
