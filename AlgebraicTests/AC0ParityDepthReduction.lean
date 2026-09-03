import Algebraic.LowerBound.AC0.ParityDepthReduction

/-!
# Variable-parameter parity depth-reduction regression tests
-/

namespace AlgebraicTests.AC0ParityDepthReduction

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (circuit : Circuit signature n g 1)
    (normal : AC0.Program.NegationsAtInputs circuit.program)
    (rounds : Nat)
    (circuitDepth : AC0.Circuit.logicalDepth circuit ≤ rounds + 1)
    (treeBound : Nat → Nat)
    (oneLeInitialBound : 1 ≤ treeBound 0)
    (p : Nat → NNReal)
    (atMostOne : ∀ level, level < rounds → p level ≤ 1)
    (boundMonotone : ∀ level, level < rounds →
      treeBound level ≤ treeBound (level + 1))
    (retained : Nat → Nat)
    (initial : retained 0 ≤ n)
    (failureLe : ∀ level, level < rounds →
      AC0.Program.layerFailureBoundOfBounds circuit.program (p level)
          (treeBound level) (treeBound (level + 1)) ≤
        (p level : ENNReal))
    (room : ∀ level, level < rounds →
      AC0.Program.layerFailureBoundOfBounds circuit.program (p level)
              (treeBound level) (treeBound (level + 1)) *
            (retained level : ENNReal) +
          (retained (level + 1) : ENNReal) <
        (p level : ENNReal) * (retained level : ENNReal))
    (tooMany : treeBound rounds < retained rounds) :
    ¬circuit.Computes interpretation (Parity.target n) :=
  AC0.Circuit.not_computes_parity_of_iterated_switching_below_top
    circuit normal rounds circuitDepth treeBound oneLeInitialBound p
    atMostOne boundMonotone retained initial failureLe room tooMany

end AlgebraicTests.AC0ParityDepthReduction
