/-
`<comment> #guard_messages in <command>`
suppresses warnings the errors in the command,
as long as they are spelled out identically
in the preceding doc comment!

If you are not careful, this lets you create incomplete definitions!
We will mostly stick to using `#guard_msgs` with `example`,
because the latter preserves the program state anyway.
-/

-- Here, let's illustrate that Lean does not let
-- you redefine the same name in the same scope.
def Toop := Type

/-- error: `Toop` has already been declared -/
#guard_msgs in
def Toop := Type
