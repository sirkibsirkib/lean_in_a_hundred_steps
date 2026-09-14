import Hundred.p005_namespace

/-
`open` a namespace to import _previously_ defined names into scope outside.

Put a list of identifiers to import within parentheses to import only those.
If this list is omitted, all names are imported.
-/
namespace First
  def name := Bit.yep
end First

open First (name)      -- import only `name`
open First (name name) -- Equivalent to `open First (name)`
example := name

-- Lean has no problem with you _introducing_ ambiguous names.
namespace Second
  def name := Bit.nah
end Second
-- { `Second.name` } are in scope.

open Second -- equivalent to `open Second (name)`
-- { `Second.name`, `name` } are in scope.

-- This shows both possible disambiguations: `First.name` and `Second.name`
#print name

-- Lean would raise an error if you attempt to _use_ ambiguous names!


/--
error: Ambiguous term
  name
Possible interpretations:
  Second.name : Bit
  First.name : Bit
-/
#guard_msgs (whitespace := lax) in
example: Bit := name

-- { `Second.name`, `name` } are in scope.
namespace Second
  def whatever := Bit.nah
end Second
/-
`Second.name`, `name`, `Second.whatever` } are in scope.
Note: `whatever` is not in scope even though we previously opened it!
What was imported was what was defined _at the time it was opened_.
-/

open Second
-- Now { `Second.name`, `name`, `Second.whatever`, `whatever` } are in scope.

-- `_root_` refers to the namespace of the file.
def foo := Bit
example := _root_.foo
example := _root_.Second.name


namespace Bit
  -- `_root_` is useful
  example := _root_.foo
end Bit


-- Define `(<namespace> . )* <name>` to define `name` inside (nested) namespaces!
namespace One
  def Two.Three.name := Bit.nah
end One
example: Bit := One.Two.Three.name

-- Open or close `(<namespace> . )* <namespace>` to do several layers at once!
namespace One.Two
  namespace Three
    #print name
    def another: Bit := name
    #print another
end One.Two.Three

/-
`open <name> in <command>` is a handy way to open the scope
only within a particular definition, example, etc.
-/
open One.Two.Three in
example: Bit := another
