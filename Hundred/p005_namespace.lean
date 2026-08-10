import Hundred.p003_definitions

-- `Bit` is now in scope, because it was in scope in the imported file.
example := Bit

-- Lean code may be sectioned inside "namespace" blocks.
namespace Outer

  -- Namespaces may be nested.
  namespace Inner

    -- Inside, names from outside work as usual.
    def Bit₂ := Bit -- defined outside, in the imported file

    -- Inside, names from inside work as usual
    def Bit₃ := Bit₂ -- defined just above, in this namespace

  end Inner
end Outer

/-
The same namespaces may be opened, populated, closed repeatedly!
You can keep doing this even in subsequent files!
PRO: very flexible! you can slap new definitions anywhere
CON: you can easily lose track of which file/line populates a namespace.
-/
namespace Outer
  def Bit₄ := Bit
end Outer

-- Names in a namespace are not in scope outside by default
-- `example := Bit₁` -- Uncommenting this would raise an error

-- Refer to a name in a deeper namespace by traversing into it with `<namespace>.`
-- You may traverse recursively.
example := Outer.Inner.Bit₂

-- From inside a scope, you may begin your traversal as if you were further outside.
namespace Outer
  example :=       Inner.Bit₂
  example := Outer.Inner.Bit₂

  namespace Inner
    example :=             Bit₂
    example :=       Inner.Bit₂
    example := Outer.Inner.Bit₂
  end Inner
end Outer
