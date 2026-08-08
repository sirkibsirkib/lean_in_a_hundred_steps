import Hundred.p01_inductive_types

/-
The `#check` command will check that the
given term as a well-defined type,
and then display it for you.
-/
#check Bit.yep
#check Bit.nah

-- You can approximate this by inspecting an `example`.
-- (In VSCode hovering over `example` shows its type).
example := Bit.yep

/-
Also like `example`, a `#check` can _assert_ that
the specified type by using a type ascription.
Really the ascription is doing all the work.
-/
example: Bit :=  Bit.yep
#check          (Bit.yep : Bit)
example      := (Bit.yep : Bit)
