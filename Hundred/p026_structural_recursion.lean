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
-- `def foo (x: Bit) := foo`


/-
But lean rejects some functions that are terminating,
just because it does not automatically confirm they are terminating.

Later, we will see how you can fall back to a more
complicated system to _prove_ that
each recursive call is decreasing by some "measure".
-/
