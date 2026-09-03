import Algebraic.LowerBound.AC0.ParityParameters

/-!
# Concrete parity-parameter regression tests
-/

namespace AlgebraicTests.AC0ParityParameters

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat) :
    (5 : ENNReal) *
        (ParityParameters.probability t level : ENNReal) *
        (ParityParameters.treeBound t level : ENNReal) = 1 / 2 :=
  ParityParameters.five_mul_probability_mul_treeBound t oneLe level

example
    (program : Program signature n g)
    (t : Nat)
    (oneLe : 1 ≤ t)
    (level : Nat)
    (small : ParityParameters.switchingFailure program t <
      (ParityParameters.minimumRatio t : ENNReal)) :
    AC0.Program.layerFailureBoundOfBounds program
          (ParityParameters.probability t level)
          (ParityParameters.treeBound t level)
          (ParityParameters.treeBound t (level + 1)) +
        (ParityParameters.retentionRatio t level : ENNReal) <
      (ParityParameters.probability t level : ENNReal) :=
  ParityParameters.layer_slack program t oneLe level small

end AlgebraicTests.AC0ParityParameters
