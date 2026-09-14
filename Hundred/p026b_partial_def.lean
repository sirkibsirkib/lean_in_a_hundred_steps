import Hundred.p001_inductive_types
import Hundred.p014_constructor_functions

/-
`partial def` removes the obligation to convince
lean that the definition is well-founded (terminating).
So you can give partial defs that are _not_ terminating.

The downside is that these definitions are _opaque_;
lean will never unfold the function to compute its output.
-/

-- For example, here is an ill-defined function!
partial def endless: ℕ → ℕ := endless

/-
However, `partial def` is only usable when
Lean is convinved that a type is _inhabited_ (aka _non empty_);
that the type has some element.

The following demonstrates this mechanism kicking in.

The motivation will become clear later,
when having a proof (`n_nothing ℕ.zero`)
of something unprovable (`Nothing`)
would ruin Lean's soundness.

But with this restriction, partial defs are
harmless, because (thanks to their opacity),
all that they prove is that the output is
inhabited (which Lean knows already).

`partial defs` however threaten the termination
of _evaluating_ your program (e.g., at runtime).

The primary usages of `partial def` is
1. to define things that you know will not terminate,
   e.g., the main loop of a repl.
2. to postpone the work of proving termination
   of a function you are sure actually terminates.
-/


/--
error:
failed to compile 'partial' definition `n_nothing`,
could not prove that the type
  ℕ → Nothing
is nonempty.

This process uses multiple strategies:
- It looks for a parameter that matches the return type.
- It tries synthesizing 'Inhabited' and 'Nonempty' instances for the return type,
  while making every parameter into a local 'Inhabited' instance.
- It tries unfolding the return type.

If the return type is defined using the 'structure' or
'inductive' command, you can try adding a
'deriving Nonempty' clause to it.
-/
#guard_msgs (whitespace := lax) in
partial def n_nothing: ℕ → Nothing := n_nothing
