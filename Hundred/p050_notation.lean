import Hundred.p001_inductive_types
import Hundred.p026_structural_recursion
import Hundred.p030_propositions
import Hundred.p014_constructor_functions
import Hundred.p043_inductive_parameters_vs_indices
import Hundred.p048_predicates_and_relations

/-
On top of the normal Lean syntax of identifiers, functions, etc,
Lean provides a system of "notation" (like Rocq), which allows users
to define (composite) terms by adding rules to Lean's parser.

These custom definitions of syntax sugar can make your Lean far more
readable, by compacting boilerplate, or by mimicking familiar notation.
-/

-- The Lean prelude includes notation for many of the common
-- logical connectives which we have already seen:
example {P Q : Prop} (p: P) (q: Q)  :   P ∧ Q := And.intro p q
example {P Q : Prop} (p: P)         :   P ∨ Q := Or.inl p
example {P Q : Prop}        (q: Q)  :   P ∨ Q := Or.inr q
example {P   : Prop} (h: P → False) : ¬ P     := Not.intro h

/-
Use `notation` to define your own notation!
This command is quite complex, so let's just
see some examples of what is possible.
-/
local notation:max "~" => Not
example: Prop := ~ True

local notation:51 x "⇔" y => (x → y) ∧ (y → x)
example: Prop := True ⇔ False

local notation:26 "either" x "or" y => x ∨ y
example: Prop := either True or True ⇔ False

-- There are specialised versions of `notation`

-- Let's define some nice infix notation for `Lyst.cons`,
-- in the style of what lean's standard `List` has and also Rocq, Haskell, etc.
infixr:34 "∷" => Lyst.cons
example: Lyst ℕ := ℕ.zero ∷ Lyst.nil
example: Lyst ℕ := ℕ.zero ∷ ℕ.one ∷ Lyst.nil

/-
Lean has other crazy stuff that lets you prettify your presentation.
They are useful for letting you make Lean more readable / embed other languages.
- "syntax" lets you extend Lean's parser to accept new structures
- "macro_rules" alborates syntactic tokens `[1,2]` into 'naked' lean.

Below we define some more powerful notation for
representing `Lyst` in the style we might expect!
-/
syntax "⟦" term,*,? "⟧" : term
macro_rules
  | `(⟦⟧) => `(Lyst.nil)
  | `(⟦$x⟧) => `(Lyst.cons $x Lyst.nil)
  | `(⟦$x, $xs,*⟧) => `(Lyst.cons $x ⟦$xs,*⟧)

example: Lyst Prop := ⟦⟧

example: Lyst ℕ := ⟦ℕ.zero, ℕ.two⟧
example: Lyst ℕ := ⟦ℕ.zero, ℕ.two, ⟧
example: Lyst ℕ := ⟦
  ℕ.zero,
  ℕ.two,
  ℕ.four,
⟧

-- mixing notations
example: Lyst Prop := True ∷ ⟦⟧
example: Lyst Prop := True ∷ ⟦False, True⟧
example: Lyst Prop := True ∷ Lyst.cons True ⟦⟧

-- You can do so much more with  `notation`, `syntax`, and `macro_rules`!
