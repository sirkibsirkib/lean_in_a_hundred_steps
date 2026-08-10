import Hundred.p009_simple_function_def
import Hundred.p014_constructor_functions
import Hundred.p015_matching

/-
The `#reduce <term>` command will _beta reduce_ the given term.
The result is in normal form:
   the only function applications `f a` that remain
   are when `f` is a constructor.

Reduction: loop, do any of the following, returning when none are possible:
1. _unfold_ a name `n` as per its definition in either:
   - some `n x` where `n` is not a constructor
   - some `match n with ...`

2. rewrite `match x with ...` to the first case `x` matches

3. rewrite `(λa ↦ <b>) c` to `<b>` with each occurrence of `a` replaced by `c`.

We trust the designers of Lean that Lean's reduction semantics is _normalising_:
- (_termination_) there are finite reduction steps
- (_confulence_) all choices of reduction step lead to the same result
-/

-- These are already in normal form!
#reduce ℕ.zero
#reduce ℕ.succ ℕ.zero
#reduce ℕ.succ (ℕ.succ ℕ.zero)
#reduce λn:ℕ ↦ n.succ -- no argument is applied!

-- Let's see how function applications are reduced
#reduce (λb ↦ b) Bit.nah
#reduce (λ_ ↦ Bit.yep) Bit.nah

-- Let's see how the definition behind a name (`bit_id`)
-- is unfolded (and then how `bit_id _` is reduced).
#reduce bit_id Bit.nah
#reduce bit_id Bit.yep

-- Let's see how a `match _ with ...` is reduced.
#reduce (
   match Bit.nah with
   | Bit.yep => ℕ.one
   | Bit.nah => ℕ.zero
)

/-
Now let's terms requiring several reduction steps
Here, `pred` had to be unfolded twice, its function applied twice,
and its argument matched twice.
-/
#reduce (pred (pred ℕ.four)).succ -- four-1-1+1 = three

/-
`#eval <term>` has the same semantics as `#reduce <term>`, but
- `reduce` uses Lean's symbolic interpreter.
   CON: it can be slow
- `eval` compiles to source via LLVM and then executes it
   CON: later we will see some `noncomputable` terms that Lean cannot compile.
-/
#eval bit_id Bit.nah
#eval ℕ.succ (ℕ.succ ℕ.zero)
