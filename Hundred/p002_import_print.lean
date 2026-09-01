-- Import brings the names in the imported scope into scope
import Hundred.p001_inductive_types

/-
The `#print <A>` command will print the definition
identified by `<A>` with some extra information.
The details depend on how you run Lean.
Via the VSCode extension, such outputs are cached
and displayed in a window shown when you hover over the command.

In this case, the shown `Bit` was imported.
-/
#print Bit


/-- error: Unknown constant `Cheese` -/
#guard_msgs in
#print Cheese
