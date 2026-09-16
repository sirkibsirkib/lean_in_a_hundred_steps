import Hundred.p015_constructor_functions

-- The `symm` tactic simply applies `Eq.symm`.
example (x y: Sort u): x=y → x=y := by
  intro h
  -- h : x = y
  -- ⊢   x = y
  symm -- flip goal
  -- h : x = y
  -- ⊢   y = x
  symm at h
  -- h : y = x
  -- ⊢   y = x
  assumption
