import Hundred.p001_inductive_types
import Hundred.p015_matching
import Hundred.p014_constructor_functions
open ℕ
/-
A `def` can be defined recursively:
its own name may occur in its body.

For example, we now have everything we need to
define the standard binary `sum` of natural numbers!
-/
namespace ℕ
  def sum: ℕ → ℕ → ℕ :=
    λ a b ↦
      match a with
      | zero    => b
      | succ a' => sum a' b.succ


  #reduce zero.sum zero
  #reduce zero.sum  one
  #reduce  one.sum zero
  #reduce  one.sum  two

  -- Here is another example
  def even_len: ℕ → Bit
    | zero   => Bit.yep
    | succ n => bit_flip (even_len n)

  #reduce  zero.even_len
  #reduce   one.even_len
  #reduce   two.even_len
  #reduce three.even_len

end ℕ

/-
Unlike Haskell or others,
Lean must be certain that recursive functions terminate.
This ensures that terms built by applying them
can be normalised (by unfolding, matching, applying).

Most of the time, the best way is to formulate
your function such that Lean can recognise
that one of its arguments are _structurally decreasing_:
  there is some parameter `a` which, in every recursive call,
  is filled by smaller subsructure of `a`.

In the above examples:
- in `sum`, the recursive call is on `a'`
  only in the case the argument was `succ a'`.
- in `even_len`, the recursive call is on `n`
  only in the case the argument was `succ n`.

The idea is that recursive calls cannot decrease forever;
eventually the parameter cannot decrease anymore!
-/

-- Lean rejects non-terminating functions like this

/--
error: fail to show termination for
  foo
with errors
  failed to infer structural recursion:
  Not considering parameter #1 of foo:
    it is unchanged in the recursive calls
  no parameters suitable for structural recursion

well-founded recursion cannot be used,
`foo` does not take any (non-fixed) arguments
-/
#guard_msgs (whitespace := lax) in
def foo: Bit → Bit := λ b ↦ foo b


/-
But Lean rejects some functions that are terminating,
just because it does not automatically confirm they are terminating.

The following example is such a case; we can understand that
it terminates (each recursive call takes the input
one step closer to `ℕ.one`) but Lean cannot.

The error message gives a hint at the solution:
  we use auxiliary goals like `termination_by` to
  give Lean extra information needed for it to
  be convinced that the function is terminating.
-/

/--
error: fail to show termination for
  ℕ.bar
with errors
failed to infer structural recursion:
Cannot use parameter #1:
  failed to eliminate recursive application
    zero.succ.bar

failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
⊢ False
-/
#guard_msgs (whitespace := lax) in
def ℕ.bar: ℕ → Bit
  |      zero => zero.succ.bar
  | succ zero => Bit.nah -- stop condition: arg is one
  | succ n    => n.bar
