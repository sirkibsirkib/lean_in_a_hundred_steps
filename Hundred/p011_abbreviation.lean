import Hundred.p009_simple_function_def

/-
`abbrev` is just like `def`, except that it signals to Lean
that they should be unfolded aggresively. We want them
to seem "transparent" and not really a distinct, new name.

Here is a common usage for this: "moving" an existing
definition as-is inside namespace.
-/
namespace Bit
  abbrev bit_id: Bit → Bit := _root_.bit_id
end Bit

example := bit_id
example := Bit.bit_id

-- You can see that `abbrev` is really just sugar for
-- `@[reducible] def`, which is a _declaration attribute_.
-- We will see some later, but they are just metadata that
-- affects what coercions and shortcuts Lean will do automatically.
-- (We will see this come up again when we start proving things).
def    Bit₇ := Bit
abbrev Bit₈ := Bit
#print Bit₇
#print Bit₈
