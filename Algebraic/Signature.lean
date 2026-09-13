import Cslib.Computability.Circuit.Signature

/-!
# Circuit signatures from CSLib

The library uses CSLib's finite-arity signatures directly. This re-export
preserves the `Algebraic.Signature` name without introducing a second model.
-/

namespace Algebraic

export Cslib.Circuits (Signature)

end Algebraic
