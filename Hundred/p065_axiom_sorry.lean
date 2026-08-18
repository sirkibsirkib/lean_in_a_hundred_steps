import Hundred.p015_matching
import Hundred.p049_predicates_and_relations

/-
`axiom` is a command like `def` but where you omit the term;
you only provide a name and a type.
It appears to also define a term, but how can this be?

Axioms are _opaque_ terms which the Lean type checker understands
as black boxes that cannot be opened up, just passed around.

Conceptually:
  Axioms are premises that you accept, and build well-defined terms of.
  Accepting new axioms changes which theorems are provable.
Mechanically:
  Axioms are "holes" for real values, which Lean's (interactive)
  elaborator will treat as opaque (cannot open up and simplify)
  and which cannot survive in any term in Lean's compilation toolchain.

To demonstrate, let's define some fresh axioms and define things atop them:
-/
axiom arb_ℕ: ℕ -- logically: a premise that some ℕ exists (not very controversial)
axiom arb_ℕ_Even: Even arb_ℕ -- logically, a premise that `arb_ℕ` is even.

-- A definition using these axioms
def ArbℕSuccSuccEven: Even arb_ℕ.succ.succ :=
  Even.succ _ (Odd.succ arb_ℕ arb_ℕ_Even)

/-
Be very careful which axioms you add!
If you make contradictions true, nonsense becomes provable in Lean
(trivialising the value of knowing something is true)!

Consider the following, where we can prove the inverse of `EveryNumberEvenAndOdd`,
but show that adding `Odd zero` would _also_ imply `EveryNumberEvenAndOdd`!
-/
open ℕ
def EveryNumberEvenAndOdd := ∀n:ℕ, Even n ∧ Odd n

theorem NotEveryNumberEvenAndOdd: ¬ EveryNumberEvenAndOdd :=
  λ (premise: EveryNumberEvenAndOdd) ↦ nomatch premise zero

theorem if_zero_odd: Odd zero → EveryNumberEvenAndOdd :=
  λ (nonsense: Odd zero) (n: ℕ) ↦
    match n with
    | zero    => And.intro Even.zero nonsense
    | succ n' =>
      match if_zero_odd nonsense n' with
      | And.intro Heven Hodd =>
        And.intro (Even.succ _ Hodd) (Odd.succ _ Heven)

/-
As such, arrivals in an unfamiliar Lean codebase often want to
know what axioms are dependencies of a given result.

The `#print axioms <name>` command does exactly that!
-/
#print axioms ArbℕSuccSuccEven

/-
`sorry` is defined in the Lean standard library.
It acts as an (implicilty polymorphic) axiom of any type.

Essentially, Lean provides `sorry` as shorthand for _any_ axiom.
But what's the point of that if it clearly makes anything provable?
Lean tracks occurrences of `sorry` in examples / defs / theorems,
and highlights them (in VSCode with a warning and yellow underline).

The intention is that Lean writers use `sorry` as a "TODO" placeholder,
and Lean tracks where they occur.

They are also discoverable like axioms as usual via `#print axioms <name>`
-/
def some_number: ℕ := (sorry: ℕ).succ
def some_num_pred: ℕ := pred some_number
#print axioms some_num_pred

/-
Later, we will discuss axioms in the Lean std library
which you may circumstantially want to use.

For example, `Classical.not_forall` proves new
theorems relating `∀x, p x` and `∃x, p x` relying on
additional "classical" axioms.
-/
example (T: Sort u)
:  ∀ (pred: T → Prop), (¬∀t, pred t) ↔ ∃t, ¬pred t
:= @Classical.not_forall T
#print axioms Classical.not_forall
