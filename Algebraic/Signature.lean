/-!
# Signatures

A signature is a collection of finitary operation symbols, each with a fixed
arity. Signatures carry no semantics: an `Interpretation` assigns concrete
operations to the symbols, and programs and circuits over a signature are
purely syntactic until they are evaluated in an interpretation.
-/

namespace Algebraic

/-- A collection of finitary operation symbols and their arities. -/
structure Signature where
  /-- The operation symbols of the signature. -/
  Op : Type v
  /-- The number of arguments taken by each operation symbol. -/
  Arity : (op : Op) → Nat

end Algebraic
