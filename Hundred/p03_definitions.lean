import Hundred.p01_inductive_types

/-
Definitions are commands of the form
`def <identifier> : <type> := <term>`
(This is basically as in Rocq).
-/
def Bit_again: Type := Bit

/-
Identifiers are quite free, notably permitting unicode!
Many editors have convert input sequences or chords to unicode for you.
For example, the ₂ below was input as \_2 in VScode.
\N gives ℕ, \sigma gives σ, \map gives ↦, \la gives λ, etc.
-/
def Bit₂: Type := Bit

/-
The type declaration `: <type>` part can be omitted from definitions
in cases where Lean can infer it, e.g., from the term.
You will get an error if this fails. Defined terms must be typed!
-/
def Bit₃ := Bit₂

/-
A term `t` can be _ascribed_ (annotated) as `(t : T)`.
You seldom see this for terms after the `:=`, but
it is sometimes useful for giving Lean sufficient information to infer
another type somewhere. We will see examples later.
-/
def Bit₄: Type := (Bit : Type)

-- Asmusingly, ascribing a term gives a term. So it can be ascribed.
-- (But why would you want to)?
def Bit₅: Type := ((Bit : Type) : Type)
