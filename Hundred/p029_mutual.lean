import Hundred.p015_constructor_functions

/-
Within `mutual` blocks, Lean looks ahead for definitions,
such that they may be mutually defined!

This is quite a clumsy encoding of even / odd for natural numbers.
We will see a better one later!
-/
namespace Weird

  mutual
    inductive Even: Type where
      | zero: Even
      | succ: Odd → Even -- uses `Odd`, defined below!

    inductive Odd: Type where
      | succ: Even → Odd
  end

  def eo₀: Even := Even.zero
  def eo₁: Odd  := Odd.succ Even.zero
  def eo₂: Even := Even.succ (Odd.succ Even.zero)

  mutual
    def even_ℕ : Even → ℕ := λ
      | Even.zero   => ℕ.zero
      | Even.succ o => (odd_ℕ o).succ -- uses `odd_N`, defined below!

    def odd_ℕ : Odd → ℕ := λ
      | Odd.succ e => (even_ℕ e).succ
  end

  #reduce even_ℕ eo₀
  #reduce  odd_ℕ eo₁
  #reduce even_ℕ eo₂

end Weird
