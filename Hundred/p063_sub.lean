import Hundred.p014_constructor_functions
/-
Let's define how we can subtract `ℕ` values.
Let's define it such that underflow gives zero.
-/
def ℕ.sub: ℕ → ℕ → ℕ
  | a,        .zero    => a
  | .zero,    .succ _  => .zero
  | .succ a', .succ b' => sub a' b'

example:   ℕ.one.sub ℕ.one  = ℕ.zero := by rfl
example: ℕ.three.sub ℕ.one  = ℕ.two  := by rfl
example:   ℕ.two.sub ℕ.four = ℕ.zero := by rfl

-- Let's instantiate the `Sub` typeclass with this!
instance: Sub ℕ where sub := ℕ.sub

-- Now we can use `x - y` notation
example:   ℕ.one - ℕ.one  = ℕ.zero := by rfl
example: ℕ.three - ℕ.one  = ℕ.two  := by rfl
example:   ℕ.two - ℕ.four = ℕ.zero := by rfl
