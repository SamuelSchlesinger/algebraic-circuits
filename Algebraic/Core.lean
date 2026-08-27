import Algebraic.Fin
import Algebraic.Signature
import Algebraic.Interpretation
import Algebraic.Homomorphism
import Algebraic.Program
import Algebraic.Circuit
import Algebraic.Semantics
import Algebraic.Support
import Algebraic.Cost
import Algebraic.Substitution
import Algebraic.Translation

/-!
# Core circuit API

This is the focused import for defining finite-arity signatures, shared
programs and circuits, their semantics and costs, and basic translations.
Concrete bases, analyses, and lower-bound developments remain in their own
modules so downstream users do not need the full research surface.
-/
