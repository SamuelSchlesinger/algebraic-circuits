namespace Algebraic

/-- A collection of finitary operation symbols and their arities. -/
structure Signature where
  Op : Type v
  Arity : (op : Op) → Nat

end Algebraic
