import Algebraic.LowerBound.AC0.ParitySurvivors

/-!
# Integer parity-survivor regression tests
-/

namespace AlgebraicTests.AC0ParitySurvivors

open Algebraic
open Algebraic.AC0
open scoped ENNReal

example (n t level : Nat) :
    ParityParameters.retained n t (level + 1) =
      n / (20 * (20 * t) ^ level) :=
  ParityParameters.retained_closed n t level

example (n t level : Nat) :
    (ParityParameters.retained n t (level + 1) : ENNReal) ≤
      (ParityParameters.retentionRatio t level : ENNReal) *
        (ParityParameters.retained n t level : ENNReal) :=
  ParityParameters.retained_shrinks n t level

end AlgebraicTests.AC0ParitySurvivors
