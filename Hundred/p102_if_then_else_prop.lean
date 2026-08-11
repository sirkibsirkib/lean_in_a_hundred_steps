import Hundred.p100_decidable

/-
Recall that `if X then _ else _` works when `X: Bool`.
-/
#reduce if true then 1 else 2

/-
More interestingly, it also works if `X: Prop`,
as long as it has a `Decidable` instance!

The `then` branch is used in the `Decidable.isTrue  _` case,
The `else` branch is used in the `Decidable.isFalse _` case,
-/
#reduce if ℕ.zero < ℕ.one then 1 else 0
#reduce if Bit.yep = Bit.nah then 1 else 0

/-
Preceding the condition with a name binder like `H:`
will put the proof of truth of falsity in
the context of the `then` and `else` branches.

Here, either case returns a proof of `Bit.yep = Bit.yep`
but the `then` case simply returns the proof
carried by the `Decidable.isTrue`!
-/
#reduce (
  (
    if H: Bit.yep = Bit.yep
    then (              H: Bit.yep = Bit.yep)
    else (Eq.refl Bit.yep: Bit.yep = Bit.yep)
  ) : Bit.yep = Bit.yep
)
