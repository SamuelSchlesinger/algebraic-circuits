namespace Algebraic

/-- A collection of finitary operation symbols and their arities. -/
structure Signature where
  /-- The operation symbols of the signature. -/
  Op : Type v
  /-- The number of arguments taken by each operation symbol. -/
  Arity : (op : Op) → Nat

end Algebraic
