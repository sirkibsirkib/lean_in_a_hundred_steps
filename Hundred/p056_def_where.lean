import Hundred.p001_inductive_types
import Hundred.p015_constructor_functions

/-
when `T` is a `structure` type,
`def <name> : T where <fields>`
is an alternative notation for
`def <name> : T := { <fields> }`
which reads very naturally,
mirroring the `structure` definition itself!
-/
structure Bundle (T: Type): Type where
  first  : T
  second : T
  pred   : T → Prop
  h_first: pred first

def Bundleℕ: Bundle ℕ where
  first   := ℕ.four
  second  := ℕ.three
  pred    := λ _ ↦ True
  h_first := True.intro

-- And also in this sense, `example` is
-- much like `def`, just omitting a name.
example: Bundle Bit where
  first   := Bit.nah
  second  := Bit.yep
  pred    := Eq Bit.nah
  h_first := Eq.refl Bit.nah
