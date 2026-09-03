import Algebraic.LowerBound.AC0.ParitySizeArithmetic

/-!
# Integral AC0 parity-size regression tests
-/

namespace AlgebraicTests.AC0ParitySizeArithmetic

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (program : Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t) :
    ParityParameters.switchingFailure program t <
          (ParityParameters.minimumRatio t : ENNReal) ↔
      20 * t * program.cost AC0.andOrCost < 2 ^ (t + 1) :=
  ParityParameters.switchingFailure_lt_minimum_iff program t oneLe

example
    (circuit : Circuit signature n g 1)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : AC0.Circuit.logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (small : 20 * t * circuit.program.cost AC0.andOrCost < 2 ^ (t + 1))
    (survivors : t < n / (20 * (20 * t) ^ (depth - 2))) :
    ¬circuit.Computes interpretation (Parity.target n) :=
  AC0.Circuit.not_computes_parity_of_integral_bounds
    circuit normal depth t twoLeDepth circuitDepth oneLe small survivors

end AlgebraicTests.AC0ParitySizeArithmetic
