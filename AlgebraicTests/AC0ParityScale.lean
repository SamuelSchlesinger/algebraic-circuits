import Algebraic.LowerBound.AC0.ParityScale

/-!
# Quantitative AC0 parity-scale regression tests
-/

namespace AlgebraicTests.AC0ParityScale

open Algebraic
open Algebraic.AC0

example
    (circuit : Circuit signature n g 1)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : AC0.Circuit.logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (inputLarge : (20 * (t + 1)) ^ (depth - 1) ≤ n) :
    2 ^ (t + 1) ≤
      20 * t * circuit.program.cost AC0.andOrCost :=
  AC0.Circuit.parity_size_tradeoff_at_scale_raw
    circuit computes depth t twoLeDepth circuitDepth oneLe inputLarge

example
    (circuit : Circuit signature n g 1)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depth t : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : AC0.Circuit.logicalDepth circuit ≤ depth)
    (oneLe : 1 ≤ t)
    (inputLarge : (20 * (t + 1)) ^ (depth - 1) ≤ n) :
    2 ^ (t + 1) ≤
      20 * t * circuit.program.cost AC0.andOrCost :=
  AC0.Circuit.parity_size_tradeoff_at_scale
    circuit normal computes depth t twoLeDepth circuitDepth oneLe inputLarge

end AlgebraicTests.AC0ParityScale
