import Algebraic.LowerBound.AC0.ParityCircuit

/-!
# Iterated switching contradiction for parity regression tests
-/

namespace AlgebraicTests.AC0ParityCircuit

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (circuit : Circuit signature n g 1)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (computes : circuit.Computes interpretation (Parity.target n))
    (depth bound : Nat)
    (circuitDepth : AC0.Circuit.logicalDepth circuit <= depth)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      AC0.Program.layerFailureBound circuit.program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        AC0.Program.layerFailureBound circuit.program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal)) :
    retained depth <= bound :=
  AC0.Circuit.retained_le_bound_of_iterated_parity
    circuit normal computes depth bound circuitDepth oneLeBound
    p atMostOne retained initial failureLe room

example
    (circuit : Circuit signature n g 1)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (depth bound : Nat)
    (circuitDepth : AC0.Circuit.logicalDepth circuit <= depth)
    (oneLeBound : 1 <= bound)
    (p : NNReal)
    (atMostOne : p <= 1)
    (retained : Nat -> Nat)
    (initial : retained 0 <= n)
    (failureLe :
      AC0.Program.layerFailureBound circuit.program p bound <= (p : ENNReal))
    (room : forall level,
      level < depth ->
        AC0.Program.layerFailureBound circuit.program p bound *
              (retained level : ENNReal) +
            (retained (level + 1) : ENNReal) <
          (p : ENNReal) * (retained level : ENNReal))
    (tooMany : bound < retained depth) :
    Not (circuit.Computes interpretation (Parity.target n)) :=
  AC0.Circuit.not_computes_parity_of_iterated_switching
    circuit normal depth bound circuitDepth oneLeBound p atMostOne
    retained initial failureLe room tooMany

end AlgebraicTests.AC0ParityCircuit
