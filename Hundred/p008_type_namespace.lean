import Hundred.p001_inductive_types
import Hundred.p006_namespace

-- Namespaces may have the same names as types in scope.
namespace Bit
end Bit

/-
In fact, you cannot get far without encountering namespaces in Lean,
(e.g., unlike Rocq), because constructors defined with type `T`
are in the namespace which is also called `T`!

Otherwise, (constructor) names in namespace work as per
the resolution of names in namespaces as usual, as we saw already.
-/
example:     Bit := Bit.nah


/-- error: Unknown identifier `nah'` -/
#guard_msgs in
example: Bit := nah'

namespace Bit
  -- Once inside `Bit`, both `nah` and `Bit.nah` are in scope!
  example: Bit := nah
  example: Bit := Bit.nah
end Bit
example: Bit := Bit.nah
