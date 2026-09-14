import Hundred.p001_inductive_types
import Hundred.p015_constructor_functions

/-
Definitions of any kind (`def`, `example`, `inductive`, ...)
can be parametrised with bindings before the term (and type).

Effectively, name parameter `(t: T)` adds...
* `∀ (t: T), ` to the type
* `λ (t: T) ↦` to the term.
-/
def idBit₂           : ∀ (_b : Bit), Bit := λ (_b : Bit) ↦ _b
def idBit₁ (_b: Bit) :               Bit :=                 _b
example: Bit → Bit := idBit₁
example: Bit → Bit := idBit₂

-- examples work the same. The parameters go just after "example".
example              : ∀ (_b : Bit), Bit := λ (_b : Bit) ↦ _b
example (_b: Bit)    :               Bit :=                 _b

/-
Implicit parameters `{ ... }` add
* `∀ {t: T}, ` to the type
* `λ {t: T} ↦` to the term, as you probably expected.

-- Here is a recursive example:
-/
def map_n {T: Type}: (f: T → T) →  ℕ → T → T :=
  λ f n t ↦
    match n with
    | ℕ.succ n' => f (map_n f n' t) -- Here, `map_n` made explicit is `@map_n T`
    | ℕ.zero    => t
#print map_n

-- Constructors are definitions too, so they may be parametrised like `def`.
inductive Someℕ': Prop where
  | intro_explicit (n:ℕ): Someℕ'
  | intro_implicit {n:ℕ}: Someℕ'
example: Someℕ' :=  Someℕ'.intro_explicit ℕ.zero

-- Here, I need `@` because `{n}` cannot be inferred from context
example: Someℕ' := @Someℕ'.intro_implicit ℕ.zero

/-
The meaning of parameters can be confusing sometimes.
Consider the following. Do they have the same meaning?
Does moving bindings `(_ : _)` from the left
to the right (or vice versa) of `:=` preserve the meaning? ...
-/
def IndexFamily₁      (i: Type)   (o: Type) := i → o
def IndexFamily₂ :=   (i: Type) → (o: Type) →  i → o

/-
No! `IndexFamily₁` and `IndexFamily₂` are not the same.
The parameters of `IndexFamily₁` make it a _function_ `λ i o ↦ ...`,
whose output is a 1-ary function type `i → o`.
While `IndexFamily₂` is simply a 3-ary (dependent) _function type_.

Here are alternative formulations of `IndexFamily₁` and `₂`
which might help to reveal the difference.
-/
def IndexFamily₁' := λ (i: Type) (o: Type) ↦ i → o
def IndexFamily₂' := ∀ (i: Type) (o: Type) , i → o
