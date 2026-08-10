import Hundred.p047_predicates_and_relations

/-
The foundations of Lean are some _constructive logic_, which
has very logical axioms like _modus ponens_ `(a → b) ∧ a → b` built in.
This constructive core is even more emphasised in Coq, for example.


The `Classical` module contains axioms that
-/

/-
`propext` formalises _propositional extensionality_:
- "extensionality" is typically some proposition `∀ x y, R x y → x=y`
- "propositional extensionality" asserts that all proofs of the same
  proposition are interchangable (=).

As such, (definitions using) this axiom muddy the originally
strong interpretation of propositions of the form `x=y`.
With it as a premise:
  semantically identical ⟶ syntactically identical
  semantically identical ⟵̸ syntactically identical

Intuitively, `propext` formalises the idea that it does not
matter how any _proposition_ is proven, as all proofs
of the same proposition are the same.

`propext` _could_ have been defined for any `Sort`,
but there is a practical reason to limit it to propositions:
- Lean enforces the "erasure" of propositions in the compilation toolchain, and
- only _un-erased_ terms with holes are problematic for the compilation toolchain.
-/
#print propext

/-
Lean's standard `Classical` library includes a handful of
axioms which extent Lean's _constructive logical_ foundations
into the world of _classical logic_, specifically for _propositions_.

A fundamental axiom it adds is _the axiom of choice_:


Note here how (Lean warned me that) Lean's interactive elaborator
falls over in trying to reason about some axioms.
The `noncomputable` prefix is needed to change its behaviour.
-/
noncomputable example {T: Sort u}: Nonempty T → T :=
  Classical.choice

-- ... where `Nonempty T` is the proposition that some `_witness: T` exists.
example: ∀ (T: Sort u) (_witness: T), Nonempty T := @Nonempty.intro

theorem exists_nonempty: ∀ (T: Sort u), (∃ _witness:T, True) → Nonempty T := by
  intro _T ⟨witness, _true⟩
  apply Nonempty.intro
  exact witness

/-
A long and storied history of mathematics is reflected in Lean,
in that the _law of the excluded middle_ (LEM) follows from the axiom of choice.
i.e., LEM is a theorem premised on some standard axioms, including a couple classical ones.

It is very useful! Any proposition is either true or false!
But naturally, the constructive interpretation is nonsense:
  "we have a function mapping any proposition P to a proof of P or the proof of its inverse".
-/
example: ∀ (P: Prop), P ∨ ¬P := Classical.em

/-
Some instances of `lem_Prop` are provable
without `Classical` and its underlying axiom.
-/
theorem even_nand_odd: ∀ n, Even n → Odd n → False := by
  intro n
  induction n
  . case zero =>
    intro he ho
    cases ho
  . case succ n ih =>
    intro he ho
    apply ih
    . cases ho ; assumption
    . cases he ; assumption

theorem even_or_odd: ∀ n, Even n ∨ Odd n := by
  intro n
  induction n
  . case zero =>
    left ; exact Even.zero
  . case succ n ih =>
    cases ih
    case inl => right ; apply  Odd.succ ; assumption
    case inr =>  left ; apply Even.succ ; assumption

abbrev P_even_or_neven := ∀ n, Even n ∨ ¬ Even n
theorem even_or_neven: P_even_or_neven := by
  intro n
  cases even_or_odd n
  . next he => left ; assumption
  . next ho =>
    right
    intro he
    exact even_nand_odd n he ho

-- Here you can confirm that `even_or_neven` is constructive;
-- it relies on no classical axioms (or any axioms at all)!
#print axioms even_or_neven

-- Some propositions are easier to prove in a classical setting.
-- `P_even_or_neven` is just such a case; it is just a case of LEM!
theorem even_or_neven': P_even_or_neven := by
  intro n
  classical
  apply Classical.em

-- Here you can see that `even_or_neven'` is
-- dependent on some of the classical axioms.
#print axioms even_or_neven'

-- And some theorems are _only_ provable classically!
-- (`Classical.em` itself a simple example)
-- ... although one cannot prove this kind of meta-result in Lean!

/- `funext` _Functional extensionality_ is another standard axiom:
  `(∀ x, f x = g x) → f = g` (here I am hiding the type parameters).

It lets you life a proof that two functions are extensionally equal
(same outputs for same inputs) to equality.
-/
def ℕ.succ_again := ℕ.succ
example: ℕ.succ_again = ℕ.succ := Eq.refl ℕ.succ -- this does not require `funext`
#print funext

def ℕ.succ': ℕ → ℕ
  | ℕ.zero => ℕ.one
  | n => n.succ

example: ℕ.succ = ℕ.succ' := by
  unfold ℕ.succ'
  -- goal: f = g
  apply funext
  -- goal: ∀ n, f n = n
  intro n
  cases n
  . unfold ℕ.one
    simp
  . simp
