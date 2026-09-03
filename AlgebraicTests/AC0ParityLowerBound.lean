import Algebraic.LowerBound.AC0.ParityLowerBound

/-!
# Concrete AC0 parity lower-bound regression tests
-/

namespace AlgebraicTests.AC0ParityLowerBound

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (circuit : Circuit signature n g 1)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : AC0.Circuit.logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (small : ParityParameters.switchingFailure circuit.program t <
      (ParityParameters.minimumRatio t : ENNReal))
    (survivors : t < n / (20 * (20 * t) ^ (depth - 2))) :
    ¬circuit.Computes interpretation (Parity.target n) :=
  AC0.Circuit.not_computes_parity_of_concrete_depth_reduction
    circuit normal depth t twoLeDepth circuitDepth oneLe small survivors

end AlgebraicTests.AC0ParityLowerBound
