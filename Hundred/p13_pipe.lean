import Hundred.p15_matching

/-
`x |> f` is a (somewhat ugly)
infix notation for `f x`.

Its utility is that `x |> f`:
1. has a weaker binding strength than `f x`
2. obviousy turns the terms around
3. is right-associative.

These differences mean that the right choice
between `f x` and `x |> f` can avoid some
parentheses and read more nicely.
-/
#reduce ℕ.four |> pred |> pred |> pred

/-
`a |>.f` is notation for `a.f`
(where `f` is a method in the namespace of `a`).
In this case, the terms are not even turned around.
But still, the different binding strength
and associativity are handy.
-/
#reduce ℕ.zero |>.succ |> pred |>.succ |> pred |>.succ
