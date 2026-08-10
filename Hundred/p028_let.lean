import Hundred.p009_simple_function_def
import Hundred.p015_matching
import Hundred.p014_constructor_functions

/-
`let` and introduces an auxiliary
definition which is locally scoped.

Like with `λ` or `∀`, the binding
precedes the term in which it is used.
-/
open ℕ

example :=

  let is_zero: ℕ → Bit
    | ℕ.zero   => Bit.nah
    | ℕ.succ _ => Bit.yep

  let count_yeps: Bit → ℕ
    | Bit.yep => ℕ.one
    | Bit.nah => ℕ.zero

  is_zero (count_yeps Bit.yep)

/-
`let ...` is really a term combinator.
So it can (mostly) be used wherever terms can go.
(In Rocq this is completely true.)
-/
example: Bit := (
  let b := Bit.nah
  let q := (
    let c := b
    c
  )
  -- c is not in scope here
  q
)

/-
By default, the name defined by `let` is
not in scope inside the term it binds to the name.
So you cannot define recursive functions in `let`.

... unless you opt in with `let rec`.
-/
def is_four_odd₁: Bit :=
  let rec odd: ℕ → Bit
    | ℕ.zero   => Bit.nah
    | ℕ.succ n => bit_flip (odd n)
  odd ℕ.four

/-
You can even use `let` in parameters of constructors, although ...
1. you need parentheses around the `let` to avoid it gobbling up the suffix,
2. this is seldom useful, and quite contrived until dependent types
   make these parameters complex enough to justify needing `let` here.
-/
inductive Foo: Type where
  | foo:
    (
      -- this whole term boils down to `Foo`
      let type_id (T:Type): Type := T
      type_id Foo
    ) → Foo
example: Foo → Foo := Foo.foo

/-
Be sparing with `let`. Ask yourself:
1. could this just be in-lined?
2. could this instead be a `def` (possibly in a `namespace`)?

Let is useful for "forward reasoning": building
up a (complex) result from arguments.

We will later see this in proofs with the `have` tactic.
-/
