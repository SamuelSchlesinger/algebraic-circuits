import Algebraic.LowerBound.AC0.ParityTopGate

/-!
# Parity top-gate obstruction regression tests
-/

namespace AlgebraicTests.AC0ParityTopGate

open Algebraic
open Algebraic.AC0

example
    (circuit : Circuit signature n g 1)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depthBound : AC0.Circuit.logicalDepth circuit ≤ level + 1)
    (shallow : AC0.Program.ShallowUpTo
      circuit.program rho level bound) :
    rho.liveCount ≤ bound :=
  AC0.Circuit.liveCount_le_of_shallowBelowTop_computes_parity_raw
    computes depthBound shallow

example
    (circuit : Circuit signature n g 1)
    (rho : PartialAssignment n)
    (level bound : Nat)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depthBound : AC0.Circuit.logicalDepth circuit ≤ level + 1)
    (shallow : AC0.Program.ShallowUpTo
      circuit.program rho level bound) :
    rho.liveCount ≤ bound :=
  AC0.Circuit.liveCount_le_of_shallowBelowTop_computes_parity
    normal computes depthBound shallow

end AlgebraicTests.AC0ParityTopGate
