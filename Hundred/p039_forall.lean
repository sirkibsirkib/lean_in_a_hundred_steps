/-
`∀ (a: A),  B` is an alternative notation for
`  (a: A) → B`.

The convention is that
- `∀`       favours a logical       reading (associated with `Prop`)
- `(_:_) →` favours a computational reading (associated with `Type`).

Indeed, this is what Lean seems to encourage:
in output, `∀` is shown in `Prop`
and        `(_:_) →` is shown in `Type`,
regardless of which was originally used.
-/

def total_prop₁  := ∀ (P: Prop),  P
def total_prop₂  :=   (P: Prop) → P
def total_type₁  := ∀ (P: Type),  P
def total_type₂  :=   (P: Type) → P
#print total_prop₁
#print total_prop₂
#print total_type₁
#print total_prop₂

/-
However, you will find plenty of cases of
`∀` being used in a computational context, too.
Perhaps this reflects `∀` being more common in
other languages. For example, Rocq has only `∀`.
-/

/-
Aside from the aforementioned suggestion of `Prop` vs. `Type`,
each notation has its own little usability advantages.
Let's enumerate them here.
-/

/-
Pro `(_:_) →` #1:
Neat generalisation of `→` means refactors to add
and remove dependencies from existing types is easier.
-/
example :=   (t: Type) →    Type  → Type → Prop
example :=   (t: Type) → (  Type) → Type → Prop
example :=   (t: Type) → (_:Type) → Type → Prop -- dependent
example :=   (t: Type) → (x:Type) → Type → Prop -- dependent

/-
Pro `(_:_) →` #2:
`(_:_) →` and `→` have a nice symmetry with `λ`:
The `→` corresponds visually and conceptually with the `↦`.
-/
example: (_:Type) → Prop :=
       λ (_:Type) ↦ True

/- Pro `∀` #1:
`∀`-bindings that go unused are picked up as dead code
(at least by my editor), which can help to catch typos.
-/
example := ∀ (t: Type),  True --    warning for unused `t`!
example :=   (t: Type) → True -- no warning for unused `t`?

/- Pro `∀` #2:
`∀` has a nice symmetry with `λ`:
multiple arguments (even of different types) can share the binder.
-/
example: ∀ (_:Type) (_:Prop), Prop := λ (_:Type) (_:Prop) ↦ True

-- Fortunately, both can take multiple arguments _of the same type_:
example := (_ _ _: Prop) → Type
example := ∀_ _ _: Prop,   Type
