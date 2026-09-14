-- Lean offers `section <name> ... end <name>`.
-- Like `namespace`, it scopes `open` and `variable`,
-- Unlike `namespace`, it does not scope definitions and theorems

section Sec
  variable (n: Prop)
  example: Prop := n
end Sec
-- `n` is not in scope

-- Sections in Lean are pretty useless.
