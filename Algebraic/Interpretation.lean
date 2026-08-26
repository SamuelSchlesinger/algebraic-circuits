import Algebraic.Signature

namespace Algebraic

/-- An interpretation assigns an operation on `Universe` to every symbol in `σ`. -/
abbrev Interpretation (σ : Signature) Universe :=
  (op : σ.Op) → (Fin (σ.Arity op) → Universe) → Universe

end Algebraic
