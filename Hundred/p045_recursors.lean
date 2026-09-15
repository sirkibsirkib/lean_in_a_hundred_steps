import Hundred.p001_inductive_types
import Hundred.p015_constructor_functions
import Hundred.p032_propositions
import Hundred.p042_inductive_function_types
import Hundred.p045_inductive_parameters_vs_indices

#print ℕ.rec


noncomputable example:
  {motive: ℕ → Sort u}                → -- given any property of ℕ
  motive ℕ.zero                       → -- proven for ℕ.zero
  ((n: ℕ) → motive n → motive n.succ) → -- proven for n.succ given it for n
  (n: ℕ) → motive n                     -- acquire a proof for each ℕ
:= ℕ.rec

def SomeBitLyst: ℕ → Type :=
  λ n ↦ LenLyst Bit n

noncomputable example:
  SomeBitLyst ℕ.zero                            → -- proven for ℕ.zero
  ((n: ℕ) → SomeBitLyst n → SomeBitLyst n.succ) → -- proven for n.succ given it for n
  (n: ℕ) → SomeBitLyst n                          -- acquire a proof for each ℕ
:= @ℕ.rec
  SomeBitLyst

noncomputable example:
  ((n: ℕ) → SomeBitLyst n → SomeBitLyst n.succ) → -- proven for n.succ given it for n
  (n: ℕ) → SomeBitLyst n                          -- acquire a proof for each ℕ
:= @ℕ.rec
  SomeBitLyst
  LenLyst.nil

noncomputable example:
  (n: ℕ) → SomeBitLyst n -- acquire a proof for each ℕ
:= @ℕ.rec
  SomeBitLyst
  LenLyst.nil
  (λ _n l ↦ l.cons Bit.nah)

noncomputable example:
  SomeBitLyst ℕ.four  -- acquire a proof for the chosen ℕ
:= @ℕ.rec
  SomeBitLyst
  LenLyst.nil
  (λ _n l ↦ l.cons Bit.nah)
  ℕ.four
