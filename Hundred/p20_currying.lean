import Hundred.p09_simple_function_def
import Hundred.p14_constructor_functions
open Bit

/-
As in any functional programming language worth its salt,
functions are plain old data data,
that may be passed into or out of functions.
-/
def bit_func_id: (Bit → Bit) → (Bit → Bit) := λf ↦ f
example: Bit → Bit := bit_func_id bit_id
example:       Bit := bit_func_id bit_id nah

/-
Function 1 that returns function 2 is how 2 argument
functions are encoded in Lean. This extends to N-ary functions.

Here is a binary function
-/
def bit_and: Bit → (Bit → Bit)
  | nah => bit_const_nah
  | yep => bit_id

#reduce (bit_and nah: Bit → Bit)
#reduce (bit_and yep: Bit → Bit)

#reduce (bit_and nah nah: Bit)
#reduce (bit_and nah yep: Bit)
#reduce (bit_and yep nah: Bit)
#reduce (bit_and yep yep: Bit)

/-
And `count_yep_3` is a ternary function
(defined on top of some helper funtions).
-/
def ℕ_identity: ℕ → ℕ :=
  λn ↦ n

def yep_succ: Bit → (ℕ → ℕ)
  | nah => ℕ_identity
  | yep => ℕ.succ

def count_yep_3: Bit → (Bit → (Bit → ℕ)) :=
  λ b1 ↦
    (λ b2 ↦
      (λ b3 ↦
        yep_succ b1 (yep_succ b2 (yep_succ b3 ℕ.zero))
      )
    )
#reduce count_yep_3 nah nah nah
#reduce count_yep_3 nah yep nah
#reduce count_yep_3 yep yep nah
#reduce count_yep_3 yep yep yep
