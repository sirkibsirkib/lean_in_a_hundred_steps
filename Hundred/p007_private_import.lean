import Hundred.p006_private_def

/-
... so let's confirm that the private imports
from the other file are not visible here.
-/

/-- this works fine. `Public` was imported! -/
example: Type := Public

/-- error: Unknown identifier `Private` -/
#guard_msgs in
example: Type := Private -- works
