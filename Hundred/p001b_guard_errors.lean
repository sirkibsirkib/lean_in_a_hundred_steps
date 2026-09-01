/-
For pedagogical purposes, Lean offers a (clunky)
mechanism for writing erroneous commands (and discarding them).
The benefit is that readers can still inspect
the erroneous commands.

`<comment> #guard_messages in <command>`
is accepted iff the comment reproduces the
error messages caught from the command.
-/

-- Here, let's illustrate that Lean does not let
-- you redefine the same name in the same scope.

inductive Name: Type

/--
error: `Name` has already been declared
-/
#guard_msgs in
inductive Name: Type
