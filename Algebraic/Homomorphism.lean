import Algebraic.Signature
import Algebraic.Interpretation

namespace Algebraic

/-- A map that preserves every operation in a pair of interpretations. -/
structure Homomorphism (i₁ : Interpretation σ U₁) (i₂ : Interpretation σ U₂) where
  map : U₁ → U₂
  homomorphic :
    ∀ (op : σ.Op) (input : Fin (σ.Arity op) → U₁),
      map (i₁ op input) = i₂ op (map ∘ input)

end Algebraic
