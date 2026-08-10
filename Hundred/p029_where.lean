import Hundred.p001_inductive_types
import Hundred.p015_matching
import Hundred.p020_currying
import Hundred.p014_constructor_functions

/-
`where` is essentially similar to `let`:
it introduces auxiliary definitions,
but without cluttering the local scope.

However, where `let` is a term combinator,
`where` is at the command level,
acting on its enclosing `def`, `example`, or whatever.

Firstly, this is a restriction of `where` vs `let`.
For example, despite what the indentation of the following `where`
suggests, it actually does not have `b1` in scope (as a `let` could).
-/
example: Bit → Bit → Bit :=
  λ b1 ↦
    -- `(`
    (λ b2 ↦ bit_and b2 (aux b1))
    -- effectively, this is as deeply indented as `example`, above.
    where aux: Bit → Bit :=
      -- neither `b1` nor `b2` are in scope
      λ _ ↦ Bit.nah
    -- `)`

/-
But there are some advantages of `where` over `let`.

Firstly, `where` introduces a set of definitions
which may be mutually defined (like `mututal`) ...
-/
def is_four_odd₂: Bit :=
  odd ℕ.four
where -- note that odd and even are mutually recursive!
  odd: ℕ → Bit
  | ℕ.zero   => Bit.nah
  | ℕ.succ n => even n -- uses `even`

  even: ℕ → Bit :=
    λn ↦ bit_flip (odd n) -- uses `odd`

/-
... and secondly, `where` introduces definitions inside a namespace,
such that they can be accessed later (like `namespace`).

Namely, it puts them in the namespace matching the name of the `def`
(but in `example`, the auxiliaries are inaccessible later).
-/
#print is_four_odd₂.odd
#print is_four_odd₂.even

/-
However, `where` is not exactly like putting the names in a namespace.
For one thing, unlike inside `namespace`, the namespace we would
expect is not opened inside the `where`.
-/
namespace def_name
  def b := Bit.nah
end def_name

def def_name: Bit :=
  foo
where
  foo: Bit := def_name.b -- `b` is _not_ in scope!

-- `let` and `where` may be used together.
def zoopy: Bit :=
  let is_zero: ℕ → Bit
    | ℕ.zero   => Bit.nah
    | ℕ.succ _ => Bit.yep

  and (is_zero ℕ.zero) (is_zero ℕ.two)

  where and: Bit → Bit → Bit
    | Bit.yep => bit_id
    | Bit.nah => bit_const_nah

/-
Personally, I seldom use `where`.
Instead I prefer one of the following alternatives:
1. The auxiliary is generally useful =>
   make a proper `def` possibly inside `mututal` and / or `namespace`.
2. The auxiliary is really never going to be useful elsewhere =>
   use `let`.
-/
