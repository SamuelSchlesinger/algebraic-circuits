import Algebraic.LowerBound.AC0.ParityRoot

/-!
# Root-selected AC0 parity lower-bound regression tests
-/

namespace AlgebraicTests.AC0ParityRoot

open Algebraic
open Algebraic.AC0

example
    (circuit : Circuit signature n g 1)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : AC0.Circuit.logicalDepth circuit ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    2 ^ ParityParameters.rootQuotient n depth /
        (20 * ParityParameters.rootScale n depth) ≤
      circuit.program.cost AC0.andOrCost :=
  AC0.Circuit.parity_andOrCost_lower_bound_at_root_raw
    circuit computes depth twoLeDepth circuitDepth inputLarge

example
    (circuit : Circuit signature n g 1)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depth : Nat)
    (twoLeDepth : 2 ≤ depth)
    (circuitDepth : AC0.Circuit.logicalDepth circuit ≤ depth)
    (inputLarge : 40 ^ (depth - 1) ≤ n) :
    2 ^ ParityParameters.rootQuotient n depth /
        (20 * ParityParameters.rootScale n depth) ≤
      circuit.program.cost AC0.andOrCost :=
  AC0.Circuit.parity_andOrCost_lower_bound_at_root
    circuit normal computes depth twoLeDepth circuitDepth inputLarge

end AlgebraicTests.AC0ParityRoot
