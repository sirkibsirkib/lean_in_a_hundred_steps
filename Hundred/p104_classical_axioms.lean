import Hundred.p091_contradiction

/-
The foundations of Lean are some _constructive logic_, which
has very logical axioms like _modus ponens_ `(a → b) ∧ a → b` built in.
This constructive core is even more emphasised in Coq, for example.

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
