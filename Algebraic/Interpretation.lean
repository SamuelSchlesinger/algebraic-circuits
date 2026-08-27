import Algebraic.Signature

/-!
# Interpretations

An interpretation of a signature over a carrier type `Universe` assigns to
every operation symbol a function from argument tuples, indexed by `Fin` of
the symbol's arity, to `Universe`. Interpretations are plain functions rather
than a structure, so they can be built pointwise, specialized, and pulled back
through `Translation`s without any wrapping.
-/

namespace Algebraic

/-- An interpretation assigns an operation on `Universe` to every symbol in `σ`. -/
abbrev Interpretation (σ : Signature) Universe :=
  (op : σ.Op) → (Fin (σ.Arity op) → Universe) → Universe

end Algebraic
