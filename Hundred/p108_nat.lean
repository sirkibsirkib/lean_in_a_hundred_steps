import Hundred.p015_constructor_functions
import Hundred.p065_sub

/-
For instructive purposes, we have mostly stuck to
our own encoding of the natural numbers: `ℕ`.

But let's briefly introduce Lean's inbuilt `Nat` type,
and discuss why you'd want to use those instead.
-/
#print Nat

-- First and foremost, Lean comes with lots of operators
-- and lemmas defined atop the standard `Nat`.
#check Nat.succ_sub_succ
#check Nat.add
#check Nat.add_comm
#check Nat.sub
#check 2
#check 2 + 5
#check 2 + 5 - 3

-- Let's build bridges between `ℕ` and `Nat`.

def ℕNat: ℕ → Nat
  | .succ n => .succ (ℕNat n)
  | .zero   => .zero
instance: Coe ℕ Nat where coe := ℕNat
#reduce (ℕ.four: Nat)
#reduce (ℕ.two:  Nat)

def Natℕ: Nat → ℕ
  | .succ n => .succ (Natℕ n)
  | .zero   => .zero
instance: Coe Nat ℕ where coe := Natℕ

#reduce ((4: Nat): ℕ)
#reduce ((2: Nat): ℕ)

@[simp]
theorem ℕNat_distributes_over_sub:
  ∀ a b,
    ℕNat (a - b) = ℕNat a - ℕNat b
:= by
  intro a b
  change ℕNat (a.sub b) = _
  induction a generalizing b with
  | zero => cases b <;> simp [ℕ.sub, ℕNat]
  | succ a' iha =>
    cases b
    . simp [ℕ.sub, ℕNat]
    . case succ b' =>
      simp only [ℕ.sub, ℕNat]
      rw [Nat.succ_sub_succ]
      exact iha b'
