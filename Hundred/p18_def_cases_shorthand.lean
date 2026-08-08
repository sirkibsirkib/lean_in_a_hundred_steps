import Hundred.p15_matching

/-
In case `λ` binds a name you immediately match and
never use again, e.g., `λ n ↦ match n with ...` above,
just `λ` is understood as shorthand!
-/
example: ℕ → ℕ := λ
  | ℕ.zero   => ℕ.zero
  | ℕ.succ n => n

/-
In fact, then even the `:= λ` can be omitted!
Thus Lean approximates the guarded defintions of Agda / Haskell
But unlike Haskell (etc.), Lean still enforces exhaustive matches!
-/
example: ℕ → ℕ
| ℕ.zero   => ℕ.zero
| ℕ.succ n => n

/-
Case-patterns can look more than one constructor deep,
and patterns may overlap (except trivially)!
In case of overlaps, higher cases take precedence.
-/
example: ℕ → ℕ
| ℕ.succ (ℕ.succ (ℕ.succ _n)) => _n
| ℕ.succ (ℕ.succ  _n)         => ℕ.two
| ℕ.succ  _n                  => _n
| ℕ.zero                      => ℕ.three

-- Undefined names act as binders on the top level
example: ℕ → ℕ
| ℕ.zero => ℕ.four
| anyℕ => anyℕ.succ.succ

-- As usual, wildcard `_` binds but gives no name.
example: ℕ → ℕ
| ℕ.zero => ℕ.four
| anyℕ => anyℕ.succ
