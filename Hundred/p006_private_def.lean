import Hundred.p001_inductive_types

/-
Commands that add things to the program scope
can often be prefixed with `private`, removing
their effects outside of the file, from importers.

Demonstrating this will take two files...
-/

def Public := Bit

private
def Private := Bit
