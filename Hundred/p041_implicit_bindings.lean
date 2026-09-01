import Hundred.p015_matching
import Hundred.p040_inductive_function_types

/-
An "implicit binding" in lean is a binding surrounded by `{ ... }`.
Conceptually, they occur in pairs:
- in the type     (e.g., bound by `∀`)
- in the function (e.g., bound by `λ`)

Note:
- `λ {A:B}` is allowed.
- `{_:A} → B` and `∀{_:A}, B` are allowed.
- `λ {A}` is allowed (it is sugar for `λ {A:_}`).
- `{A} → B` and `∀{A}, B` are not allowed.
  Later we can see an argument that they are seldom useful.
  But honestly, I don't understand why they are prohibited.
-/
example: ∀ {_:Type}, Type := λ {_:Type} ↦ Bit

namespace Maybe

  -- Running example: a function with an implicit then explicit parameter
  def some': ∀ {T: Type} (_: T),  Maybe T :=
             λ {T: Type} (t: T) ↦ some T t

  /-
  The main utility of a function with an implicit parameter:
  Lean fills in the implicit argument automatically from context!

  Because the context is needed, implicit parameters are most useful
  when they are dependencies of other parameters.
  -/

  -- Here, the implicit argument (`ℕ`) is derived from the next argument.
  example := some ℕ ℕ.zero
  example := some'  ℕ.zero -- argument `ℕ` is implied

  -- Here, the implicit argument `ℕ` is derived from the example's type.
  example: {T: Type} → T → Maybe T := some' -- no arguments
  example:             ℕ → Maybe ℕ := some' -- argument `ℕ` is implied
  example                          := (some': ℕ → Maybe ℕ) -- argument `ℕ` is implied

  /-
  If you want to explicitly choose the implicit parameter,
  prefix the name with `@`. Lean then interprets
  arguments to parameters as if they were all explicit.
  -/
  example: Maybe ℕ :=  some'   ℕ.zero
  example: Maybe ℕ := @some' ℕ ℕ.zero

  -- You can generally think of the `@`-version as
  -- the original with implicits made explicit ...
  example: {T: Type} → T → Maybe T :=  some'
  example: (T: Type) → T → Maybe T := @some'
  example := @some'

  -- Except that, if forced by context, Lean is also
  -- happy to keep parameters implicit.
  example: {T: Type} → T → Maybe T := @some'

  -- The opposite is not true. Lean won't coerce implicits to explicit without `@`!
  -- Here, lean is not exposing the implicit first argument.

  /--
  error: Type mismatch
    some'
  has type
    ?m.1 → Maybe ?m.1
  of sort `Type` but is expected to have type
    (T : Type) → T → Maybe T
  of sort `Type 1`
  -/
  #guard_msgs (whitespace := lax) in
  example: (T: Type) → T → Maybe T := some'

  -- Finally, note that `@` is usable on any term,
  -- but without implicit parameters, there is no effect.
  example: ℕ → ℕ :=  ℕ.succ
  example: ℕ → ℕ := @ℕ.succ
  example:     ℕ :=  ℕ.zero
  example:     ℕ := @ℕ.zero
end Maybe

/-
The `λ { ... }` binder can be omitted!
In this example, `λ {T: Type}` is abbreviated to `λ`,
but as a consequence, Lean _must_ infer the type of `t`!
-/
example:  {T: Type} → T → T := λ {T: Type} (t:T) ↦ t
example:  {T: Type} → T → T := λ           (t:_) ↦ t

/-
Recall that constructors may be functions, too.
Their parameters may be implicit the same as in `def`.
-/
inductive Someℕ: Prop where
  | intro: {_: ℕ} → Someℕ

-- Here the implicit parameter of `Someℕ.intro` cannot be derived from context!
-- So `@` is needed to let it be provided explicitly.
example: Someℕ := @Someℕ.intro ℕ.zero

/- But be careful with implicit parameters!
Sometimes Lean's inferece is dumb,
and then fixing the implicit parameters becomes tedious.
-/
