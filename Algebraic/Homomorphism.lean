import Algebraic.Interpretation
import Cslib.Computability.Circuit.Homomorphism

/-!
# Interpretation homomorphisms from CSLib

The homomorphism structure, identities, composition, and their laws are supplied
by CSLib. The names here preserve the existing public imports.
-/

namespace Algebraic

export Cslib.Circuits (Homomorphism)

namespace Homomorphism

export Cslib.Circuits.Homomorphism
  (ext id comp id_map comp_map id_comp comp_id comp_assoc)

end Homomorphism
end Algebraic
